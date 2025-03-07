// This file is adapted from MIRAI (https://github.com/facebookexperimental/MIRAI)
// Original author: Herman Venter <hermanv@fb.com>
// Original copyright header:

// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

use crate::analysis::memory::expression::ExpressionType;
use crate::analysis::memory::path::{Path, PathEnum, PathSelector};
use crate::analysis::memory::utils;
use rustc_hir::def_id::DefId;
// use rustc_middle::mir;
// use rustc_middle::ty::subst::{GenericArg, GenericArgKind, InternalSubsts, GenericArgsRef};
// use rustc_middle::ty::{
//     AdtDef, Binder, ExistentialPredicate, ExistentialProjection, ExistentialTraitRef, FnSig,
//     ParamTy, Ty, TyCtxt, TyKind, TypeAndMut,
// };

use rustc_middle::mir;
use rustc_middle::ty::{
    AdtDef, CoroutineArgsExt, ExistentialPredicate, ExistentialProjection, ExistentialTraitRef, FnSig, GenericArg, GenericArgKind, GenericArgs, GenericArgsRef, ParamTy, Ty, TyCtxt, TyKind
};
use rustc_target::abi::FieldIdx;

use std::collections::HashMap;
use std::fmt::{Debug, Formatter, Result};
use std::rc::Rc;

pub struct TypeVisitor<'tcx> {
    pub actual_argument_types: Vec<Ty<'tcx>>,
    pub def_id: DefId,
    pub generic_argument_map: Option<HashMap<rustc_span::Symbol, Ty<'tcx>>>,
    pub generic_arguments: Option<GenericArgsRef<'tcx>>,
    pub mir: mir::Body<'tcx>,
    pub path_ty_cache: HashMap<Rc<Path>, Ty<'tcx>>,
    tcx: TyCtxt<'tcx>,
}

impl<'tcx> Debug for TypeVisitor<'tcx> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        "TypeVisitor".fmt(f)
    }
}

impl<'compilation, 'tcx> TypeVisitor<'tcx> {
    pub fn new(def_id: DefId, mir: mir::Body<'tcx>, tcx: TyCtxt<'tcx>) -> TypeVisitor<'tcx> {
        TypeVisitor {
            actual_argument_types: Vec::new(),
            def_id,
            generic_argument_map: None,
            generic_arguments: None,
            mir,
            path_ty_cache: HashMap::new(),
            tcx,
        }
    }

    /// Returns the size (including padding) and alignment, in bytes,  of an instance of the given type.
    pub fn get_type_size_and_alignment(&self, ty: Ty<'tcx>) -> (u128, u128) {
        if let Ok(ty_and_layout) = self.layout_of(ty) {
            (
                ty_and_layout.layout.size().bytes() as u128,
                ty_and_layout.align.pref.bytes() as u128,
            )
        } else {
            (0, 8)
        }
    }

    pub fn get_typing_env_for(&self, def_id: DefId) -> rustc_middle::ty::TypingEnv<'tcx> {
        let env_def_id = if self.tcx.is_closure_like(def_id) {
            self.tcx.typeck_root_def_id(def_id)
        } else {
            def_id
        };
        let param_env = self.tcx.param_env(env_def_id);
        rustc_middle::ty::TypingEnv {
            typing_mode: rustc_middle::ty::TypingMode::PostAnalysis,
            param_env,
        }
    }

    pub fn get_typing_env(&self) -> rustc_middle::ty::TypingEnv<'tcx> {
        let param_env = self.get_param_env();
        rustc_middle::ty::TypingEnv {
            typing_mode: rustc_middle::ty::TypingMode::PostAnalysis,
            param_env,
        }
    }

    /// Updates the type cache of the visitor so that looking up the type of path returns ty.
    pub fn set_path_rustc_type(&mut self, path: Rc<Path>, ty: Ty<'tcx>) {
        self.path_ty_cache.insert(path, ty);
    }



    /// Returns the size in bytes (including padding) of an element of the given collection type.
    /// If the type is not a collection, it returns one.
    pub fn get_elem_type_size(&self, ty: Ty<'tcx>) -> u64 {
        match ty.kind() {
            TyKind::Array(ty, _) | TyKind::Slice(ty) => self.get_type_size(*ty),
            TyKind::RawPtr(ty, _) => self.get_type_size(*ty),
            _ => 1,
        }
    }

    /// Returns a parameter environment for the current function.
    pub fn get_param_env(&self) -> rustc_middle::ty::ParamEnv<'tcx> {
        let env_def_id = if self.tcx.is_closure_like(self.def_id) {
            self.tcx.typeck_root_def_id(self.def_id)
        } else {
            self.def_id
        };
        self.tcx.param_env(env_def_id)
    }

    pub fn get_field_type(
        &self,
        def: &'tcx AdtDef,
        args: GenericArgsRef<'tcx>,
        ordinal: usize,
    ) -> Ty<'tcx> {
        for variant in def.variants().iter() {
            if ordinal < variant.fields.len() {
                let field = &variant.fields[ordinal.into()];
                let ft = field.ty(self.tcx, args);
                trace!("field {:?} type is {:?}", ordinal, ft);
                return ft;
            }
        }
        debug!("adt def does not have a field with ordinal {}", ordinal);
        self.tcx.types.never
    }

    /// This is a hacky and brittle way to navigate the Rust compiler's type system.
    /// Eventually it should be replaced with a comprehensive and principled mapping.
    pub fn get_path_rustc_type(
        &mut self,
        path: &Rc<Path>,
        current_span: rustc_span::Span,
    ) -> Ty<'tcx> {
        if let Some(ty) = self.path_ty_cache.get(path) {
            return *ty;
        }
        match &path.value {
            PathEnum::LocalVariable { ordinal } => {
                if *ordinal > 0 && *ordinal < self.mir.local_decls.len() {
                    self.mir.local_decls[mir::Local::from(*ordinal)].ty
                } else {
                    info!("path.value is {:?}", path.value);
                    self.tcx.types.unit
                }
            }
            PathEnum::Parameter { ordinal } => {
                if self.actual_argument_types.len() >= *ordinal {
                    self.actual_argument_types[*ordinal - 1]
                } else if *ordinal > 0 && *ordinal < self.mir.local_decls.len() {
                    self.mir.local_decls[mir::Local::from(*ordinal)].ty
                } else {
                    info!("path.value is {:?}", path.value);
                    self.tcx.types.unit
                }
            }
            PathEnum::Result => {
                if self.mir.local_decls.is_empty() {
                    info!("result type wanted from function without result local");
                    self.tcx.types.unit
                } else {
                    self.mir.local_decls[mir::Local::from(0usize)].ty
                }
            }
            PathEnum::QualifiedPath {
                qualifier,
                selector,
                ..
            } => {
                let t = self.get_path_rustc_type(qualifier, current_span);
                match &**selector {
                    PathSelector::Slice(_) => {
                        return t;
                    }
                    PathSelector::Field(ordinal) => {
                        let bt = Self::get_dereferenced_type(t);
                        match &bt.kind() {
                            TyKind::Adt(def, args) => {
                                return self.get_field_type(def, args, *ordinal);
                            }
                            TyKind::Closure(def_id, args) => {
                                let closure_substs = args.as_closure();
                                return *closure_substs.upvar_tys().get(*ordinal).unwrap_or_else(
                                    || {
                                        info!("closure field not found {:?} {:?}", def_id, ordinal);
                                        &self.tcx.types.never
                                    },
                                );
                            }
                            TyKind::Tuple(types) => {
                                if let Some(ty) = types.get(*ordinal) {
                                    return *ty;
                                }
                            }
                            _ => (),
                        }
                    }
                    PathSelector::Deref => {
                        return Self::get_dereferenced_type(t);
                    }
                    PathSelector::Discriminant => {
                        return self.tcx.types.i32;
                    }
                    // PathSelector::Downcast(_, ordinal) => {
                    //     let t = type_visitor::get_target_type(t);
                    //     if let TyKind::Adt(def, substs) = t.kind() {
                    //         use rustc_index::vec::Idx;
                    //         if *ordinal >= def.variants.len() {
                    //             debug!(
                    //                 "illegally down casting to index {} of {:?} at {:?}",
                    //                 *ordinal, t, current_span
                    //             );
                    //             return self.tcx.types.never;
                    //         }
                    //         let variant = &def.variants[VariantIdx::new(*ordinal)];
                    //         let field_tys = variant.fields.iter().map(|fd| fd.ty(self.tcx, substs));
                    //         return self.tcx.mk_tup(field_tys);
                    //     }
                    //     return self.tcx.types.never;
                    //     // if let TyKind::Adt(def, substs) = &t.kind() {
                    //     //     use rustc_index::vec::Idx;
                    //     //     let variant = &def.variants[VariantIdx::new(*ordinal)];
                    //     //     let field_tys = variant.fields.iter().map(|fd| fd.ty(self.tcx, substs));
                    //     //     return self.tcx.mk_tup(field_tys);
                    //     // }
                    // }
                    PathSelector::Index(_) => match &t.kind() {
                        TyKind::Array(elem_ty, _) | TyKind::Slice(elem_ty) => {
                            return *elem_ty;
                        }
                        _ => (),
                    },
                    _ => {}
                }
                info!("current span is {:?}", current_span);
                info!("t is {:?}", t);
                info!("qualifier is {:?}", qualifier);
                info!("selector is {:?}", selector);
                self.tcx.types.unit
            }
            PathEnum::StaticVariable { def_id, .. } => {
                if let Some(def_id) = def_id {
                    return self.tcx.type_of(*def_id).skip_binder();
                }
                info!("path.value is {:?}", path.value);
                self.tcx.types.unit
            }
            _ => {
                info!("path.value is {:?}", path.value);
                self.tcx.types.unit
            }
        }
    }

    /// Returns the target type of a reference type.
    fn get_dereferenced_type(ty: Ty<'tcx>) -> Ty<'tcx> {
        match &ty.kind() {
            TyKind::Ref(_, t, _) => *t,
            _ => ty,
        }
    }

    /// If Operand corresponds to a compile time constant function, return
    /// the generic parameter substitutions (type arguments) that are used by
    /// the call instruction whose operand this is.
    pub fn get_generic_arguments_map(
        &self,
        def_id: DefId,
        generic_args: GenericArgsRef<'tcx>,
        actual_argument_types: &[Ty<'tcx>],
    ) -> Option<HashMap<rustc_span::Symbol, Ty<'tcx>>> {
        let mut substitution_map = self.generic_argument_map.clone();
        let mut map: HashMap<rustc_span::Symbol, Ty<'tcx>> = HashMap::new();

        // This iterates over the callee's generic parameter definitions.
        // If the parent of the callee is generic, those definitions are iterated
        // as well. This applies recursively. Note that a child cannot mask the
        // generic parameters of its parent with one of its own, so each parameter
        // definition in this iteration will have a unique name.
        GenericArgs::for_item(self.tcx, def_id, |param_def, _| {
            if let Some(gen_arg) = generic_args.get(param_def.index as usize) {
                if let GenericArgKind::Type(ty) = gen_arg.unpack() {
                    let specialized_gen_arg_ty =
                        self.specialize_generic_argument_type(ty, &substitution_map);
                    if let Some(substitution_map) = &mut substitution_map {
                        substitution_map.insert(param_def.name, specialized_gen_arg_ty);
                    }
                    map.insert(param_def.name, specialized_gen_arg_ty);
                }
            } else {
                debug!("unmapped generic param def");
            }
            self.tcx.mk_param_from_def(param_def) // not used
        });
        // Add "Self" -> actual_argument_types[0]
        if let Some(self_ty) = actual_argument_types.get(0) {
            let self_ty = if let TyKind::Ref(_, ty, _) = self_ty.kind() {
                *ty
            } else {
                *self_ty
            };
            let self_sym = rustc_span::Symbol::intern("Self");
            map.entry(self_sym).or_insert(self_ty);
        }
        if map.is_empty() {
            None
        } else {
            Some(map)
        }
    }

    /// Returns an ExpressionType value corresponding to the Rustc type of the place.
    pub fn get_place_type(
        &mut self,
        place: &mir::Place<'tcx>,
        current_span: rustc_span::Span,
    ) -> ExpressionType {
        (self.get_rustc_place_type(place, current_span).kind()).into()
    }

    /// Returns the rustc Ty of the given place in memory.
    pub fn get_rustc_place_type(
        &self,
        place: &mir::Place<'tcx>,
        current_span: rustc_span::Span,
    ) -> Ty<'tcx> {
        let result = {
            let base_type = self.mir.local_decls[place.local].ty;
            self.get_type_for_projection_element(current_span, base_type, &place.projection)
        };
        match result.kind() {
            // Type parameter, e.g., `T` in `fn f<T>(x: T) {}`
            TyKind::Param(t_par) => {
                if let Some(generic_args) = self.generic_arguments {
                    if let Some(gen_arg) = generic_args.as_ref().get(t_par.index as usize) {
                        return gen_arg.expect_ty();
                    }
                    if t_par.name.as_str() == "Self" && !self.actual_argument_types.is_empty() {
                        return self.actual_argument_types[0];
                    }
                }
            }
            TyKind::Ref(region, ty, mutbl) => {
                if let TyKind::Param(t_par) = ty.kind() {
                    if t_par.name.as_str() == "Self" && !self.actual_argument_types.is_empty() {
                        return Ty::new_ref(
                            self.tcx,
                            *region,
                            self.actual_argument_types[0],
                            *mutbl,
                        );
                    }
                }
            }
            _ => {}
        }
        result
    }

    /// Returns the rustc TyKind of the element selected by projection_elem.
    pub fn get_type_for_projection_element(
        &self,
        current_span: rustc_span::Span,
        base_ty: Ty<'tcx>,
        place_projection: &[rustc_middle::mir::PlaceElem<'tcx>],
    ) -> Ty<'tcx> {
        place_projection
            .iter()
            .fold(base_ty, |base_ty, projection_elem| match projection_elem {
                mir::ProjectionElem::Deref => match base_ty.kind() {
                    TyKind::Adt(..) => base_ty,
                    TyKind::RawPtr(ty, _) => *ty,
                    TyKind::Ref(_, ty, _) => *ty,
                    _ => {
                        info!(
                            "bad deref projection span: {:?}\nelem: {:?} type: {:?}",
                            current_span, projection_elem, base_ty
                        );
                        self.tcx.types.never
                    }
                },
                mir::ProjectionElem::Field(_, ty) => {
                    self.specialize_generic_argument_type(*ty, &self.generic_argument_map)
                }
                mir::ProjectionElem::Subslice { .. } => base_ty,
                mir::ProjectionElem::Index(_) | mir::ProjectionElem::ConstantIndex { .. } => {
                    match base_ty.kind() {
                        TyKind::Adt(..) => base_ty,
                        TyKind::Array(ty, _) => *ty,
                        TyKind::Ref(_, ty, _) => get_element_type(*ty),
                        TyKind::Slice(ty) => *ty,
                        _ => {
                            debug!(
                                "span: {:?}\nelem: {:?} type: {:?}",
                                current_span, projection_elem, base_ty
                            );
                            panic!();
                        }
                    }
                }
                mir::ProjectionElem::Subtype(ty) => *ty,
                mir::ProjectionElem::OpaqueCast(ty) => *ty,
                mir::ProjectionElem::Downcast(_, ordinal) => {
                    if let TyKind::Adt(def, args) = base_ty.kind() {
                        if ordinal.index() >= def.variants().len() {
                            debug!(
                                "illegally down casting to index {} of {:?} at {:?}",
                                ordinal.index(),
                                base_ty,
                                current_span
                            );
                            let variant = &def.variants().iter().last().unwrap();
                            let field_tys = variant.fields.iter().map(|fd| fd.ty(self.tcx, args));
                            return Ty::new_tup_from_iter(self.tcx, field_tys);
                        }
                        let variant = &def.variants()[*ordinal];
                        let field_tys = variant.fields.iter().map(|fd| fd.ty(self.tcx, args));
                        return Ty::new_tup_from_iter(self.tcx, field_tys);
                    } else if let TyKind::Coroutine(def_id, args) = base_ty.kind() {
                        let mut tuple_types = args.as_coroutine().state_tys(*def_id, self.tcx);
                        if let Some(field_tys) = tuple_types.nth(ordinal.index()) {
                            return Ty::new_tup_from_iter(self.tcx, field_tys);
                        }
                        debug!(
                            "illegally down casting to index {} of {:?} at {:?}",
                            ordinal.index(),
                            base_ty,
                            current_span
                        );
                    } else {
                        info!("unexpected type for downcast {:?}", base_ty);
                    }
                    base_ty
                }
            })
    }

    /// Returns the size in bytes (including padding) of an instance of the given type.
    pub fn get_type_size(&self, ty: Ty<'tcx>) -> u64 {
        if let Ok(ty_and_layout) = self.layout_of(ty) {
            ty_and_layout.layout.size().bytes()
        } else {
            0
        }
    }

    /// Returns a layout for the given type, if concrete.
    pub fn layout_of(
        &self,
        ty: Ty<'tcx>,
    ) -> std::result::Result<
        rustc_middle::ty::layout::TyAndLayout<'tcx>,
        &'tcx rustc_middle::ty::layout::LayoutError<'tcx>,
    > {
        let typing_env = self.get_typing_env();
        if utils::is_concrete(ty.kind()) {
            self.tcx.layout_of(typing_env.as_query_input(ty))
        } else {
            Err(&*self
                .tcx
                .arena
                .alloc(rustc_middle::ty::layout::LayoutError::Unknown(ty)))
        }
    }

    pub fn specialize_generic_args(
        &self,
        args: GenericArgsRef<'tcx>,
        map: &Option<HashMap<rustc_span::Symbol, Ty<'tcx>>>,
    ) -> GenericArgsRef<'tcx> {
        let specialized_generic_args: Vec<GenericArg<'_>> = args
            .iter()
            .map(|gen_arg| self.specialize_generic_argument(gen_arg, map))
            .collect();
        self.tcx.mk_args(&specialized_generic_args)
    }

    fn specialize_generic_argument(
        &self,
        gen_arg: GenericArg<'tcx>,
        map: &Option<HashMap<rustc_span::Symbol, Ty<'tcx>>>,
    ) -> GenericArg<'tcx> {
        match gen_arg.unpack() {
            GenericArgKind::Type(ty) => self.specialize_generic_argument_type(ty, map).into(),
            _ => gen_arg,
        }
    }

    pub fn specialize_generic_argument_type(
        &self,
        gen_arg_type: Ty<'tcx>,
        map: &Option<HashMap<rustc_span::Symbol, Ty<'tcx>>>,
    ) -> Ty<'tcx> {
        // The projection of an associated type. For example,
        // `<T as Trait<..>>::N`.
        if let TyKind::Alias(rustc_middle::ty::Projection, projection) = gen_arg_type.kind() {
            let specialized_substs = self.specialize_generic_args(projection.args, map);
            let item_def_id = projection.def_id;
            return if utils::are_concrete(specialized_substs) {
                let typing_env = self.get_typing_env_for(
                    self.tcx.associated_item(item_def_id).container_id(self.tcx),
                );
                if let Ok(Some(instance)) = rustc_middle::ty::Instance::try_resolve(
                    self.tcx,
                    typing_env,
                    item_def_id,
                    specialized_substs,
                ) {
                    let instance_item_def_id = instance.def.def_id();
                    if item_def_id == instance_item_def_id {
                        return Ty::new_projection(self.tcx, projection.def_id, specialized_substs);
                    }
                    let item_type = self.tcx.type_of(instance_item_def_id).skip_binder();
                    let map =
                        self.get_generic_arguments_map(instance_item_def_id, instance.args, &[]);
                    if item_type == gen_arg_type && map.is_none() {
                        // Can happen if the projection just adds a life time
                        item_type
                    } else {
                        self.specialize_generic_argument_type(item_type, &map)
                    }
                } else {
                    let projection_trait = Some(self.tcx.parent(item_def_id));
                    if projection_trait == self.tcx.lang_items().pointee_trait() {
                        // assume!(!specialized_substs.is_empty());
                        if let GenericArgKind::Type(ty) = specialized_substs[0].unpack() {
                            return ty.ptr_metadata_ty(self.tcx, |ty| ty);
                        }
                    } else if projection_trait == self.tcx.lang_items().discriminant_kind_trait() {
                        // assume!(!specialized_substs.is_empty());
                        if let GenericArgKind::Type(enum_ty) = specialized_substs[0].unpack() {
                            return enum_ty.discriminant_ty(self.tcx);
                        }
                    }
                    debug!("could not resolve an associated type with concrete type arguments");
                    gen_arg_type
                }
            } else {
                Ty::new_projection(self.tcx, projection.def_id, specialized_substs)
            };
        }

        if map.is_none() {
            return gen_arg_type;
        }
        match gen_arg_type.kind() {
            TyKind::Adt(def, args) => {
                Ty::new_adt(self.tcx, *def, self.specialize_generic_args(args, map))
            }
            TyKind::Array(elem_ty, len) => {
                let specialized_elem_ty = self.specialize_generic_argument_type(*elem_ty, map);
                // let specialized_len = self.specialize_const(*len, map);
                self.tcx
                    .mk_ty_from_kind(TyKind::Array(specialized_elem_ty, *len))
            }
            TyKind::Slice(elem_ty) => {
                let specialized_elem_ty = self.specialize_generic_argument_type(*elem_ty, map);
                Ty::new_slice(self.tcx, specialized_elem_ty)
            }
            TyKind::RawPtr(ty, mutbl) => {
                let specialized_ty = self.specialize_generic_argument_type(*ty, map);
                Ty::new_ptr(
                    self.tcx,
                    specialized_ty, 
                    *mutbl
                )
            }
            TyKind::Ref(region, ty, mutbl) => {
                let specialized_ty = self.specialize_generic_argument_type(*ty, map);
                Ty::new_ref(self.tcx, *region, specialized_ty, *mutbl)
            }
            TyKind::FnDef(def_id, args) => {
                Ty::new_fn_def(self.tcx, *def_id, self.specialize_generic_args(args, map))
            }
            TyKind::FnPtr(sig_tys, hdr) => {
                let fn_sig = sig_tys.with(*hdr);
                let map_fn_sig = |fn_sig: FnSig<'tcx>| {
                    let specialized_inputs_and_output = self.tcx.mk_type_list_from_iter(
                        fn_sig
                            .inputs_and_output
                            .iter()
                            .map(|ty| self.specialize_generic_argument_type(ty, map)),
                    );
                    FnSig {
                        inputs_and_output: specialized_inputs_and_output,
                        c_variadic: fn_sig.c_variadic,
                        safety: fn_sig.safety,
                        abi: fn_sig.abi,
                    }
                };
                let specialized_fn_sig = fn_sig.map_bound(map_fn_sig);
                Ty::new_fn_ptr(self.tcx, specialized_fn_sig)
            }
            TyKind::Dynamic(predicates, region, kind) => {
                let specialized_predicates = predicates.iter().map(
                    |bound_pred: rustc_middle::ty::Binder<'_, ExistentialPredicate<'tcx>>| {
                        bound_pred.map_bound(|pred| match pred {
                            ExistentialPredicate::Trait(ExistentialTraitRef {
                                def_id,
                                args,
                                ..
                            }) => {
                                ExistentialPredicate::Trait(ExistentialTraitRef::new_from_args(
                                    self.tcx,
                                    def_id,
                                    self.specialize_generic_args(args, map),
                                ))
                            }
                            ExistentialPredicate::Projection(ExistentialProjection {
                                def_id,
                                args,
                                term,
                                ..
                            }) => {
                                if let Some(ty) = term.as_type() {
                                    ExistentialPredicate::Projection(
                                        ExistentialProjection::new_from_args(
                                            self.tcx,
                                            def_id,
                                            self.specialize_generic_args(args, map),
                                            self.specialize_generic_argument_type(ty, map).into(),
                                        ),
                                    )
                                } else {
                                    ExistentialPredicate::Projection(
                                        ExistentialProjection::new_from_args(
                                            self.tcx,
                                            def_id,
                                            self.specialize_generic_args(args, map),
                                            term,
                                        ),
                                    )
                                }
                            }
                            ExistentialPredicate::AutoTrait(_) => pred,
                        })
                    },
                );
                Ty::new_dynamic(
                    self.tcx,
                    self.tcx
                        .mk_poly_existential_predicates_from_iter(specialized_predicates),
                    *region,
                    *kind,
                )
            }
            TyKind::Closure(def_id, args) => {
                Ty::new_closure(self.tcx, *def_id, self.specialize_generic_args(args, map))
            }

            TyKind::Coroutine(def_id, args) => {
                Ty::new_coroutine(self.tcx, *def_id, self.specialize_generic_args(args, map))
            }

            TyKind::CoroutineWitness(def_id, args) => {
                let specialized_types = self.specialize_generic_args(args, map);
                Ty::new_coroutine_witness(self.tcx, *def_id, specialized_types)
            }

            // TyKind::Generator(def_id, substs, movability) => {
            //     self.tcx
            //         .mk_generator(*def_id, self.specialize_substs(substs, map), *movability)
            // }
            // TyKind::GeneratorWitness(bound_types) => {
            //     let map_types = |types: &rustc_middle::ty::List<Ty<'tcx>>| {
            //         self.tcx.mk_type_list(
            //             types
            //                 .iter()
            //                 .map(|ty| self.specialize_generic_argument_type(ty, map)),
            //         )
            //     };
            //     let specialized_types = bound_types.map_bound(map_types);
            //     self.tcx.mk_generator_witness(specialized_types)
            // }
            TyKind::Tuple(types) => Ty::new_tup_from_iter(
                self.tcx,
                types
                    .iter()
                    .map(|ty| self.specialize_generic_argument_type(ty, map)),
            ),
            TyKind::Alias(
                rustc_middle::ty::Opaque,
                rustc_middle::ty::AliasTy { def_id, args, .. },
            ) => Ty::new_opaque(self.tcx, *def_id, self.specialize_generic_args(args, map)),

            // The projection of an associated type. For example,
            // `<T as Trait<..>>::N`.
            // TyKind::Projection(projection) => {
            //     let specialized_substs = self.specialize_substs(projection.substs, map);
            //     let item_def_id = projection.item_def_id;
            //     if utils::are_concrete(specialized_substs) {
            //         let param_env = self
            //             .tcx
            //             .param_env(self.tcx.associated_item(item_def_id).container.id());
            //         let specialized_substs = self.specialize_substs(projection.substs, map);
            //         if let Ok(Some(instance)) = rustc_middle::ty::Instance::resolve(
            //             self.tcx,
            //             param_env,
            //             item_def_id,
            //             specialized_substs,
            //         ) {
            //             let item_def_id = instance.def.def_id();
            //             let item_type = self.tcx.type_of(item_def_id);
            //             if item_type == gen_arg_type {
            //                 // Can happen if the projection just adds a life time
            //                 item_type
            //             } else {
            //                 self.specialize_generic_argument_type(item_type, map)
            //             }
            //         } else {
            //             debug!("could not resolve an associated type with concrete type arguments");
            //             gen_arg_type
            //         }
            //     } else {
            //         self.tcx
            //             .mk_projection(projection.item_def_id, specialized_substs)
            //     }
            // }
            // TyKind::Opaque(def_id, substs) => self
            //     .tcx
            //     .mk_opaque(*def_id, self.specialize_substs(substs, map)),
            TyKind::Param(ParamTy { name, .. }) => {
                if let Some(ty) = map.as_ref().unwrap().get(&name) {
                    return *ty;
                }
                gen_arg_type
            }
            _ => gen_arg_type,
        }
    }

    // TODO: this is only used in promote constant, remove it if not necessary
    pub fn starts_with_slice_pointer(&self, ty_kind: &TyKind<'tcx>) -> bool {
        match ty_kind {
            TyKind::RawPtr(target, _) | TyKind::Ref(_, target, _) => {
                // Pointers to sized arrays are thin pointers.
                matches!(target.kind(), TyKind::Slice(..))
            }
            TyKind::Adt(def, args) => {
                for v in def.variants().iter() {
                    // return v;
                    if let Some(field0) = v.fields.get(FieldIdx::from_usize(0)) {
                        let field0_ty = field0.ty(self.tcx, args);
                        if self.starts_with_slice_pointer(&field0_ty.kind()) {
                            return true;
                        }
                    }
                }
                false
            }
            TyKind::Tuple(types) => {
                if let Some(field0_ty) = types.iter().next() {
                    self.starts_with_slice_pointer(field0_ty.kind())
                } else {
                    false
                }
            }
            _ => false,
        }
    }
}

/// Returns the element type of an array or slice type.
pub fn get_element_type(ty: Ty<'_>) -> Ty<'_> {
    match &ty.kind() {
        TyKind::Array(t, _) => *t,
        TyKind::Ref(_, t, _) => match t.kind() {
            TyKind::Array(t, _) => *t,
            TyKind::Slice(t) => *t,
            _ => *t,
        },
        TyKind::Slice(t) => *t,
        _ => ty,
    }
}

/// Returns true if the ty is a union.
pub fn is_union(ty: Ty<'_>) -> bool {
    if let TyKind::Adt(def, ..) = ty.kind() {
        def.is_union()
    } else {
        false
    }
}

pub fn get_target_type(ty: Ty<'_>) -> Ty<'_> {
    match ty.kind() {
        TyKind::RawPtr(t, _) | TyKind::Ref(_, t, _) => *t,
        _ => ty,
    }
}

pub fn is_slice_pointer(ty_kind: &TyKind<'_>) -> bool {
    if let TyKind::RawPtr(target, _) | TyKind::Ref(_, target, _) = ty_kind {
        // Pointers to sized arrays and slice pointers are thin pointers.
        matches!(target.kind(), TyKind::Slice(..) | TyKind::Str)
    } else {
        false
    }
}
