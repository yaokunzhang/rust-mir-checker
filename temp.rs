#[logfn_inputs(TRACE)]
pub fn specialize_generic_argument_type(
    &self,
    gen_arg_type: Ty<'tcx>,
    map: &Option<HashMap<rustc_span::Symbol, GenericArg<'tcx>>>,
) -> Ty<'tcx> {
    // The projection of an associated type. For example,
    // `<T as Trait<..>>::N`.
    if let TyKind::Projection(projection) = gen_arg_type.kind() {
        let specialized_substs = self.specialize_substs(projection.substs, map);
        let item_def_id = projection.item_def_id;
        return if utils::are_concrete(specialized_substs) {
            let param_env = self
                .tcx
                .param_env(self.tcx.associated_item(item_def_id).container.id());
            if let Ok(Some(instance)) = rustc_middle::ty::Instance::resolve(
                self.tcx,
                param_env,
                item_def_id,
                specialized_substs,
            ) {
                let instance_item_def_id = instance.def.def_id();
                if item_def_id == instance_item_def_id {
                    return self
                        .tcx
                        .mk_projection(projection.item_def_id, specialized_substs);
                }
                let item_type = self.tcx.type_of(instance_item_def_id);
                let map =
                    self.get_generic_arguments_map(instance_item_def_id, instance.substs, &[]);
                if item_type == gen_arg_type && map.is_none() {
                    // Can happen if the projection just adds a life time
                    item_type
                } else {
                    self.specialize_generic_argument_type(item_type, &map)
                }
            } else {
                let projection_trait = self.tcx.parent(item_def_id);
                if projection_trait == self.tcx.lang_items().pointee_trait() {
                    assume!(!specialized_substs.is_empty());
                    if let GenericArgKind::Type(ty) = specialized_substs[0].unpack() {
                        return ty.ptr_metadata_ty(self.tcx);
                    }
                } else if projection_trait == self.tcx.lang_items().discriminant_kind_trait() {
                    assume!(!specialized_substs.is_empty());
                    if let GenericArgKind::Type(enum_ty) = specialized_substs[0].unpack() {
                        return enum_ty.discriminant_ty(self.tcx);
                    }
                }
                debug!("could not resolve an associated type with concrete type arguments");
                gen_arg_type
            }
        } else {
            self.tcx
                .mk_projection(projection.item_def_id, specialized_substs)
        };
    }
    if map.is_none() {
        return gen_arg_type;
    }
    match gen_arg_type.kind() {
        TyKind::Adt(def, substs) => self.tcx.mk_adt(def, self.specialize_substs(substs, map)),
        TyKind::Array(elem_ty, len) => {
            let specialized_elem_ty = self.specialize_generic_argument_type(elem_ty, map);
            let specialized_len = self.specialize_const(len, map);
            self.tcx
                .mk_ty(TyKind::Array(specialized_elem_ty, specialized_len))
        }
        TyKind::Slice(elem_ty) => {
            let specialized_elem_ty = self.specialize_generic_argument_type(elem_ty, map);
            self.tcx.mk_slice(specialized_elem_ty)
        }
        TyKind::RawPtr(rustc_middle::ty::TypeAndMut { ty, mutbl }) => {
            let specialized_ty = self.specialize_generic_argument_type(ty, map);
            self.tcx.mk_ptr(rustc_middle::ty::TypeAndMut {
                ty: specialized_ty,
                mutbl: *mutbl,
            })
        }
        TyKind::Ref(region, ty, mutbl) => {
            let specialized_ty = self.specialize_generic_argument_type(ty, map);
            self.tcx.mk_ref(
                region,
                rustc_middle::ty::TypeAndMut {
                    ty: specialized_ty,
                    mutbl: *mutbl,
                },
            )
        }
        TyKind::FnDef(def_id, substs) => self
            .tcx
            .mk_fn_def(*def_id, self.specialize_substs(substs, map)),
        TyKind::FnPtr(fn_sig) => {
            let map_fn_sig = |fn_sig: FnSig<'tcx>| {
                let specialized_inputs_and_output = self.tcx.mk_type_list(
                    fn_sig
                        .inputs_and_output
                        .iter()
                        .map(|ty| self.specialize_generic_argument_type(ty, map)),
                );
                FnSig {
                    inputs_and_output: specialized_inputs_and_output,
                    c_variadic: fn_sig.c_variadic,
                    unsafety: fn_sig.unsafety,
                    abi: fn_sig.abi,
                }
            };
            let specialized_fn_sig = fn_sig.map_bound(map_fn_sig);
            self.tcx.mk_fn_ptr(specialized_fn_sig)
        }
        TyKind::Dynamic(predicates, region) => {
            let specialized_predicates = predicates.iter().map(
                |bound_pred: rustc_middle::ty::Binder<'_, ExistentialPredicate<'tcx>>| {
                    bound_pred.map_bound(|pred| match pred {
                        ExistentialPredicate::Trait(ExistentialTraitRef { def_id, substs }) => {
                            ExistentialPredicate::Trait(ExistentialTraitRef {
                                def_id,
                                substs: self.specialize_substs(substs, map),
                            })
                        }
                        ExistentialPredicate::Projection(ExistentialProjection {
                            item_def_id,
                            substs,
                            ty,
                        }) => ExistentialPredicate::Projection(ExistentialProjection {
                            item_def_id,
                            substs: self.specialize_substs(substs, map),
                            ty: self.specialize_generic_argument_type(ty, map),
                        }),
                        ExistentialPredicate::AutoTrait(_) => pred,
                    })
                },
            );
            self.tcx.mk_dynamic(
                self.tcx
                    .mk_poly_existential_predicates(specialized_predicates),
                region,
            )
        }
        TyKind::Closure(def_id, substs) => {
            // Closure types can be part of their own type parameters...
            // so need to guard against endless recursion
            {
                let mut borrowed_closures_being_specialized =
                    self.closures_being_specialized.borrow_mut();
                let closures_being_specialized =
                    borrowed_closures_being_specialized.deref_mut();
                if !closures_being_specialized.insert(*def_id) {
                    return gen_arg_type;
                }
            }
            let specialized_closure = self
                .tcx
                .mk_closure(*def_id, self.specialize_substs(substs, map));
            let mut borrowed_closures_being_specialized =
                self.closures_being_specialized.borrow_mut();
            let closures_being_specialized = borrowed_closures_being_specialized.deref_mut();
            closures_being_specialized.remove(def_id);
            specialized_closure
        }
        TyKind::Generator(def_id, substs, movability) => {
            self.tcx
                .mk_generator(*def_id, self.specialize_substs(substs, map), *movability)
        }
        TyKind::GeneratorWitness(bound_types) => {
            let map_types = |types: &rustc_middle::ty::List<Ty<'tcx>>| {
                self.tcx.mk_type_list(
                    types
                        .iter()
                        .map(|ty| self.specialize_generic_argument_type(ty, map)),
                )
            };
            let specialized_types = bound_types.map_bound(map_types);
            self.tcx.mk_generator_witness(specialized_types)
        }
        TyKind::Tuple(substs) => self.tcx.mk_tup(
            self.specialize_substs(substs, map)
                .iter()
                .map(|gen_arg| gen_arg.expect_ty()),
        ),
        TyKind::Opaque(def_id, substs) => self
            .tcx
            .mk_opaque(*def_id, self.specialize_substs(substs, map)),
        TyKind::Param(ParamTy { name, .. }) => {
            if let Some(map) = map {
                if let Some(gen_arg) = map.get(name) {
                    return gen_arg.expect_ty();
                }
            }
            gen_arg_type
        }
        _ => gen_arg_type,
    }
}
