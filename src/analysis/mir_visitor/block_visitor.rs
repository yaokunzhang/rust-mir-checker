// This file is adapted from MIRAI (https://github.com/facebookexperimental/MIRAI)
// Original author: Herman Venter <hermanv@fb.com>
// Original copyright header:

// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

use crate::analysis::abstract_domain::AbstractDomain;
use crate::analysis::diagnostics::DiagnosticCause;
use crate::analysis::memory::constant_value::{ConstantValue, FunctionReference};
use crate::analysis::memory::expression::{Expression, ExpressionType};
use crate::analysis::memory::k_limits;
use crate::analysis::memory::path::{Path, PathEnum, PathRefinement, PathSelector};
use crate::analysis::memory::symbolic_domain::SymbolicDomain;
use crate::analysis::memory::symbolic_value::{
    self, SymbolicValue, SymbolicValueRefinement, SymbolicValueTrait,
};
use crate::analysis::memory::utils;
use crate::analysis::mir_visitor::body_visitor::WtoFixPointIterator;
use crate::analysis::mir_visitor::call_visitor::CallVisitor;
use crate::analysis::mir_visitor::type_visitor;
use crate::analysis::numerical::apron_domain::{
    ApronAbstractDomain, ApronDomainType, ApronOperation, GetManagerTrait,
};
use crate::analysis::numerical::linear_constraint::LinearConstraintSystem;
use crate::analysis::z3_solver::SmtResult;
use rug::Integer;
use rustc_infer::infer::TyCtxtInferExt;
use rustc_span::source_map::Spanned;
use rustc_target::abi::{FieldIdx, Primitive, TagEncoding, VariantIdx, Variants};
use rustc_hir::def_id::DefId;
use rustc_index::{Idx, IndexVec};
use rustc_middle::mir::{self, ConstValue};
use rustc_middle::mir::interpret::{alloc_range, GlobalAlloc, Scalar};
use rustc_middle::mir::UnwindTerminateReason;
use rustc_middle::ty::{
    Const, CoroutineArgsExt, IntTy, ParamConst, ScalarInt, Ty, TyKind, TypingMode, UintTy, ValTree
};

use rustc_middle::ty::GenericArgsRef;
use rustc_span::Span;
use std::borrow::Borrow;
use std::convert::TryFrom;
use std::convert::TryInto;
use std::fmt;
use std::rc::Rc;

use super::type_visitor::get_element_type;

/// This class is used to extract properties from Rust MIR
/// Initially a pre-condition is given, then the visitor abstractly execute a basic block,
/// and returns a post-condition.
pub struct BlockVisitor<'tcx, 'a, 'b, 'compiler, DomainType>
where
    DomainType: ApronDomainType,
    ApronAbstractDomain<DomainType>: GetManagerTrait,
{
    /// The upper layer wto visitor, block visitor may change body visitor's state
    pub body_visitor: &'b mut WtoFixPointIterator<'tcx, 'a, 'compiler, DomainType>,

    /// The MIR that is analyzed
    pub mir: &'a mir::Body<'tcx>,

    /// The DefId of the current function
    pub def_id: DefId,

    /// Current basic block
    pub current_block: mir::BasicBlock,
}

impl<'tcx, 'a, 'b, 'compiler, DomainType> fmt::Debug
    for BlockVisitor<'tcx, 'a, 'b, 'compiler, DomainType>
where
    DomainType: ApronDomainType,
    ApronAbstractDomain<DomainType>: GetManagerTrait,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "MirVisitor with abstract state: {:?}", self.state())
    }
}

impl<'tcx, 'a, 'b, 'compiler, DomainType> BlockVisitor<'tcx, 'a, 'b, 'compiler, DomainType>
where
    DomainType: ApronDomainType,
    ApronAbstractDomain<DomainType>: GetManagerTrait,
{
    pub fn state(&self) -> &AbstractDomain<DomainType> {
        &self.body_visitor.state
    }

    pub fn new(
        body_visitor: &'b mut WtoFixPointIterator<'tcx, 'a, 'compiler, DomainType>,
        init_state: AbstractDomain<DomainType>,
    ) -> Self {
        body_visitor.state = init_state;
        let def_id = body_visitor.def_id;
        Self {
            mir: body_visitor.wto.get_mir(),
            def_id: def_id,
            body_visitor,
            current_block: mir::BasicBlock::from_usize(0),
        }
    }

    pub fn visit_basic_block(&mut self, bb: mir::BasicBlock) {
        self.current_block = bb;
        let mir::BasicBlockData {
            ref statements,
            ref terminator,
            ..
        } = &self.mir[bb];
        let mut location = bb.start_location();
        // Visit statements
        for stmt in statements {
            self.body_visitor.current_location = location;
            self.visit_statement(stmt);
            location.statement_index += 1;
        }
        // Visit terminators
        if let Some(terminator) = terminator {
            self.body_visitor.current_location = location;
            self.visit_terminator(terminator);
        }
    }

    fn visit_statement(&mut self, statement: &mir::Statement<'tcx>) {
        let mir::Statement { kind, source_info } = statement;
        // Ignore the following to reduce logging
        if matches!(
            kind,
            mir::StatementKind::FakeRead(..)
                | mir::StatementKind::AscribeUserType(..)
                | mir::StatementKind::Retag(..)
                | mir::StatementKind::Nop
                | mir::StatementKind::Coverage(..)
                | mir::StatementKind::StorageLive(..)
        ) {
            return;
        }
        debug!("------------------------------------------------------");
        debug!("Visiting a {:?} statement: {:?}", kind, statement);

        // Only record span when encountering these statements
        // Other statements do not provide useful information in output warnings
        // if matches!(
        //     kind,
        //     mir::StatementKind::Assign(..)
        //         | mir::StatementKind::SetDiscriminant { .. }
        // ) {
        //     self.body_visitor.current_span = source_info.span;
        // }
        // match kind {
        //     mir::StatementKind::Assign(box (place, rvalue)) => {
        //         self.visit_assign(place, rvalue.borrow())
        //     }
        //     mir::StatementKind::SetDiscriminant {
        //         place,
        //         variant_index,
        //     } => self.visit_set_discriminant(place, *variant_index),
        //     mir::StatementKind::StorageDead(local) => self.visit_storage_dead(*local),

        //     // The rest are ignored
        //     _ => (),
        // }

        if matches!(
            kind,
            mir::StatementKind::Assign(..)
                | mir::StatementKind::SetDiscriminant { .. }
        ) {
            self.body_visitor.current_span = source_info.span;
        }

        match kind {
            mir::StatementKind::Assign(box (place, rvalue)) => self.visit_assign(place, rvalue),
            mir::StatementKind::ConstEvalCounter => (),
            // mir::StatementKind::FakeRead(..) => panic!(),
            mir::StatementKind::SetDiscriminant {
                place,
                variant_index,
            } => self.visit_set_discriminant(place, *variant_index),
            // mir::StatementKind::Deinit(box place) => {
            //     self.visit_deinit(place);
            // }
            // mir::StatementKind::StorageLive(local) => self.visit_storage_live(*local),
            mir::StatementKind::StorageDead(local) => self.visit_storage_dead(*local),
            // mir::StatementKind::Retag(retag_kind, place) => self.visit_retag(*retag_kind, place),
            // mir::StatementKind::AscribeUserType(..) => panic!(),
            // mir::StatementKind::Coverage(..) => (),
            // mir::StatementKind::Intrinsic(box non_diverging_intrinsic) => {
            //     self.visit_non_diverging_intrinsic(non_diverging_intrinsic);
            // }
            mir::StatementKind::Nop => (),
            // mir::StatementKind::PlaceMention(_) => (),
            _ => (),
        }

        debug!("State after visiting statement:");
        debug!("Numerical: {:?}", self.state().numerical_domain);
        debug!("Symbolic:  {:?}", self.state().symbolic_domain);
        debug!("------------------------------------------------------\n");
    }

    fn visit_unwind_resume(&self) {}

    fn visit_unwind_terminate(&self, _reason: &UnwindTerminateReason) {}

    fn visit_unreachable(&mut self) {
        // An unreachable terminator is the compiler's way to tell us that this block will
        // actually never be reached because the type system says so.
        // Having the block in the control flow graph allows the join to remove the condition
        // guarding entry to this block.
    }

    fn visit_terminator(&mut self, terminator: &mir::Terminator<'tcx>) {
        let mir::Terminator { source_info, kind } = terminator;
        let _span: Span = source_info.span;
        debug!("------------------------------------------------------");
        debug!("Visiting terminator: {:?}", terminator);

        // Comment this line because terminators do not provide useful span information
        self.body_visitor.current_span = source_info.span;

        match kind {
            // mir::TerminatorKind::SwitchInt {
            //     discr,
            //     switch_ty,
            //     targets,
            // } => self.visit_switch_int(discr, switch_ty, targets),
            mir::TerminatorKind::SwitchInt { discr, targets } => self.visit_switch_int(
                discr,
                discr.ty(self.mir, self.body_visitor.context.tcx),
                targets,
            ),
            mir::TerminatorKind::UnwindResume => self.visit_unwind_resume(),
            mir::TerminatorKind::UnwindTerminate(reason) => self.visit_unwind_terminate(reason),
            mir::TerminatorKind::Return => self.visit_return(),
            mir::TerminatorKind::Unreachable => self.visit_unreachable(),
            mir::TerminatorKind::Drop {
                place,
                target,
                unwind,
                replace,
            } => self.visit_drop(place, *target, *unwind, *replace),
            mir::TerminatorKind::Call {
                func,
                args,
                destination,
                target,
                unwind,
                call_source,
                fn_span,
            } => self.visit_call(
                func,
                args,
                *destination,
                *target,
                *unwind,
                *call_source,
                fn_span,
            ),
            mir::TerminatorKind::Assert {
                cond,
                expected,
                msg,
                target,
                unwind,
            } => self.visit_assert(cond, *expected, msg, *target, *unwind),
            _ => (),
        }
        debug!("State after visiting terminator:");
        debug!("Numerical: {:?}", self.state().numerical_domain);
        debug!("Symbolic:  {:?}", self.state().symbolic_domain);
        debug!("------------------------------------------------------\n");
    }

    /// Delete dead variables from abstract domains to save memory
    /// However, since we symbolically evaluate values, it is possible that symbolic values still
    /// depend on variables that have been dead. So we only clean dead variables if no other
    /// symbolic values depend on them.
    fn visit_storage_dead(&mut self, local: mir::Local) {
        // Some heuristics that reduce the cost of removing dead variables
        // Only proceed if `bb % cleaning_delay ==0`, since `depend_on` is expensive
        let cleaning_delay = self.body_visitor.context.analysis_options.cleaning_delay;
        // cleaning_delay is 0 means no cleaning
        if cleaning_delay == 0 || self.current_block.index() % cleaning_delay != 0 {
            return;
        }

        let path = Path::new_local_parameter_or_result(
            local.as_usize(),
            self.body_visitor.fresh_variable_offset,
            self.mir.arg_count,
        );
        if !self.state().symbolic_domain.depend_on(&path) {
            debug!("{:?} is not depended in symbolic domain, clean it", path);
            self.body_visitor
                .state
                .update_value_at(path, symbolic_value::BOTTOM.into());
        }
    }

    fn visit_set_discriminant(
        &mut self,
        place: &mir::Place<'tcx>,
        variant_index: rustc_target::abi::VariantIdx,
    ) {
        let target_path =
            Path::new_discriminant(self.visit_place(place)).refine_paths(&self.state());

        let ty = self
            .body_visitor
            .type_visitor
            .get_rustc_place_type(place, self.body_visitor.current_span);

        // let param_env = self.body_visitor.type_visitor.get_param_env();
        
        match ty.kind() {
            TyKind::Adt(..) | TyKind::Coroutine(..) => {
                let discr_ty = ty
                    .discriminant_ty(self.body_visitor.context.tcx);
                let discr_bits = match ty
                    .discriminant_for_variant(self.body_visitor.context.tcx, variant_index)
                {
                    Some(discr) => discr.val,
                    None => variant_index.as_u32() as u128,
                };
                let val = self.get_int_const_val(discr_bits, discr_ty);
                self.body_visitor.state.update_value_at(target_path, val);
                
                return;
            }
            _ => panic!("rustc should ensure this"),
        }
        // let index_val: ConstantValue = Integer::from(variant_index.as_usize()).into();
        // self.body_visitor
        //     .state
        //     .update_value_at(target_path, Rc::new(index_val.into()));
    }

    fn propagate_taint(&mut self, place: &mir::Place<'tcx>, rvalue: &mir::Rvalue<'tcx>) {
        let llocal = place.local;
        if let Some(rlocals) = self.extract_local_from_rvalue(rvalue) {
            for local in rlocals {
                if self.body_visitor.tainted_variables.contains(&local) {
                    self.body_visitor.tainted_variables.insert(llocal);
                }
            }
        }
    }

    // Extract `mir::Local` from `mir::Operand` if there exits some
    pub fn extract_local_from_operand(
        &self,
        operand: &mir::Operand<'tcx>,
    ) -> Option<Vec<mir::Local>> {
        match operand {
            mir::Operand::Copy(p) | mir::Operand::Move(p) => Some(vec![p.local]),
            _ => None,
        }
    }

    // Extract `mir::Local` from `mir::Rvalue` if there exits some
    // The result is a list of `Local` because a `Rvalue` may associate multiple `Local`s
    fn extract_local_from_rvalue(&self, rvalue: &mir::Rvalue<'tcx>) -> Option<Vec<mir::Local>> {
        use mir::Rvalue::*;
        match rvalue {
            Use(operand) | Repeat(operand, _) | Cast(_, operand, _) | UnaryOp(_, operand) => {
                self.extract_local_from_operand(operand)
            }
            Ref(_, _, place) | Discriminant(place) => {
                Some(vec![place.local])
            }
            BinaryOp(_, box (operand1, operand2))
             => {
                let res1 = self.extract_local_from_operand(operand1);
                let res2 = self.extract_local_from_operand(operand2);
                match (res1, res2) {
                    (Some(ref mut vec_local1), Some(ref mut vec_local2)) => {
                        vec_local1.append(vec_local2);
                        Some(vec_local1.to_vec())
                    }
                    (None, Some(vec_local2)) => Some(vec_local2),
                    (Some(vec_local1), None) => Some(vec_local1),
                    _ => None,
                }
            }

            Aggregate(_, vec_operand) => {
                let mut res = Vec::new();
                for operand in vec_operand {
                    if let Some(ref mut vec_local) = self.extract_local_from_operand(operand) {
                        res.append(vec_local);
                    }
                }
                Some(res)
            }
            _ => None,
        }
    }

    /// Handles assignment `place = rvalue`
    fn visit_assign(&mut self, place: &mir::Place<'tcx>, rvalue: &mir::Rvalue<'tcx>) {
        self.propagate_taint(place, rvalue);
        debug!(
            "Current tainted variables: {:?}",
            self.body_visitor.tainted_variables
        );
        let path = self.visit_place(place);
        debug!("Get LHS Path: {:?}", path);
        self.visit_rvalue(path, rvalue);
    }

    pub fn visit_function_reference(
        &mut self,
        def_id: DefId,
        ty: Ty<'tcx>,
        generic_args: Option<GenericArgsRef<'tcx>>,
    ) -> &ConstantValue {
        if let Some(generic_args) = generic_args {
            self.body_visitor
                .crate_context
                .generic_args_cache
                .insert(def_id, generic_args);
        }

        &mut self
            .body_visitor
            .crate_context
            .constant_value_cache
            .get_function_constant_for(
                def_id,
                ty,
                generic_args,
                self.body_visitor.context.tcx,
                &mut self.body_visitor.crate_context.known_names_cache,
            )
    }

    // Convert mir::Place into Path
    pub fn visit_place(&mut self, place: &mir::Place<'tcx>) -> Rc<Path> {
        debug!(
            "In visit_place, current offset: {}",
            self.body_visitor.fresh_variable_offset
        );
        let place_path = self.get_path_for_place(place);
        let mut path = place_path.refine_paths(&self.state());
        match &path.value {
            PathEnum::QualifiedPath {
                qualifier,
                selector,
                ..
            } if **selector == PathSelector::Deref => {
                let refined_qualifier = qualifier.refine_paths(&self.state());
                let qualifier_ty = self
                    .body_visitor
                    .type_visitor
                    .get_path_rustc_type(&refined_qualifier, self.body_visitor.current_span);
                if let TyKind::Ref(_, t, _) = qualifier_ty.kind() {
                    if let TyKind::Array(..) = t.kind() {
                        // *&array => array[0]
                        // The place path dereferences a qualifier that type checks as a pointer.
                        // After refinement we know that the qualifier is a reference to an array.
                        // This means that the current value of path ended up as the refinement of
                        // *&p which reduced to p, which is of type array. The point of all this
                        // aliasing is to get to the first element of the array, so just go there
                        // directly.
                        path = Path::new_index(path, Rc::new(0u128.into()));
                    }
                }
            }
            _ => {}
        }
        let ty = self
            .body_visitor
            .type_visitor
            .get_rustc_place_type(place, self.body_visitor.current_span);

        match &path.value {
            PathEnum::QualifiedPath {
                qualifier,
                selector,
                ..
            } if **selector == PathSelector::Deref => {
                if let PathEnum::Alias { value } = &qualifier.value {
                    match &value.expression {
                        Expression::Join { left, right, .. } => {
                            let target_type = ExpressionType::from(ty.kind());
                            let distributed_deref = left
                                .dereference(target_type.clone())
                                .join(right.dereference(target_type));
                            path = Path::get_as_path(distributed_deref);
                        }
                        Expression::Widen { operand, .. } => {
                            let target_type = ExpressionType::from(ty.kind());
                            let distributed_deref =
                                operand.dereference(target_type).widen(&place_path);
                            path = Path::get_as_path(distributed_deref);
                        }
                        _ => (),
                    }
                }
            }
            _ => (),
        };
        if !self
            .body_visitor
            .type_visitor
            .path_ty_cache
            .contains_key(&path)
        {
            self.body_visitor
                .type_visitor
                .path_ty_cache
                .insert(path.clone(), ty);
        }
        path
    }

    /// Get integer constant from `rustc_middle::ty::consts::int::ScalarInt`
    /// Note: must rule out ZSTs before using this
    fn get_constant_from_scalar(&mut self, ty: Ty<'tcx>, data: u128, size: usize) -> ConstantValue {
        match ty.kind() {
            TyKind::Bool => {
                if data == 0 {
                    ConstantValue::Int(Integer::from(0))
                } else {
                    ConstantValue::Int(Integer::from(1))
                }
            }
            TyKind::Char => ConstantValue::Int(Integer::from(data as u32)),
            TyKind::Int(..) => {
                let value: i128 = match size {
                    1 => i128::from(data as i8),
                    2 => i128::from(data as i16),
                    4 => i128::from(data as i32),
                    8 => i128::from(data as i64),
                    _ => data as i128,
                };
                ConstantValue::Int(Integer::from(value))
            }
            TyKind::Closure(def_id, args) => {
                let specialized_ty = self
                    .body_visitor
                    .type_visitor
                    .specialize_generic_argument_type(
                        ty,
                        &self.body_visitor.type_visitor.generic_argument_map,
                    );
                let specialized_args = self.body_visitor.type_visitor.specialize_generic_args(
                    args,
                    &&self.body_visitor.type_visitor.generic_argument_map,
                );
                if specialized_args.len() >= 3 {
                    let tuple_ty = specialized_args.last().unwrap().expect_ty();
                    let cv: ConstantValue = self.get_constant_from_scalar(tuple_ty, data, size);
                    let cp = Path::get_as_path(Rc::new(cv.into()));
                    let fr: ConstantValue = self
                        .visit_function_reference(*def_id, specialized_ty, Some(specialized_args))
                        .clone();
                    let fv = Rc::<SymbolicValue>::new(fr.clone().into());
                    let fp = Path::get_as_path(fv.clone());
                    self.copy_or_move_elements(fp, cp, tuple_ty, true);
                    return fr;
                } else {
                    unreachable!("args for closure not right {:?}", specialized_args);
                }
            }
            TyKind::Uint(..) => ConstantValue::Int(Integer::from(data)),
            TyKind::FnDef(def_id, args) => {
                debug_assert!(size == 0 && data == 0);
                let specialized_ty = self
                    .body_visitor
                    .type_visitor
                    .specialize_generic_argument_type(
                        ty,
                        &self.body_visitor.type_visitor.generic_argument_map,
                    );
                let specialized_args = self.body_visitor.type_visitor.specialize_generic_args(
                    args,
                    &&self.body_visitor.type_visitor.generic_argument_map,
                );
                self.visit_function_reference(*def_id, specialized_ty, Some(specialized_args))
                    .clone()
            }
            // Ignore floats, etc.
            _ => ConstantValue::Top,
        }
    }

    pub fn get_int_const_val(&mut self, mut val: u128, ty: Ty<'tcx>) -> Rc<SymbolicValue> {
        // let param_env = self.body_visitor.type_visitor.get_param_env();
        let is_signed;
        if let Ok(ty_and_layout) = self.body_visitor.type_visitor.layout_of(ty) {
            is_signed = ty_and_layout.backend_repr.is_signed();
            let size = ty_and_layout.size;
            if is_signed {  
                val = size.sign_extend(val) as u128;
            } else {
                val = size.truncate(val);
            }
        } else {
            is_signed = ty.is_signed();
        }
        if is_signed {
            self.body_visitor.get_i128_const_val(val as i128)
        } else {
            self.body_visitor.get_u128_const_val(val)
        }
    }
    
    /// Use for deconstructing `ConstValue::Slice` (i.e., `&[u8]` and `&str`) and `ConstValue::ByRef`
    #[allow(dead_code)]
    fn deconstruct_constant_array(
        &mut self,
        bytes: &[u8],
        elem_type: ExpressionType,
        len: Option<u128>,
        array_ty: Ty<'tcx>,
    ) -> Rc<SymbolicValue> {
        let byte_len = bytes.len();
        let alignment = self
            .body_visitor
            .get_u128_const_val((elem_type.bit_length() / 8) as u128);
        let byte_len_value = self.body_visitor.get_u128_const_val(byte_len as u128);
        let array_value = self
            .body_visitor
            .get_new_heap_block(byte_len_value, alignment, array_ty);
        if byte_len > k_limits::MAX_BYTE_ARRAY_LENGTH {
            return array_value;
        }
        let array_path = Path::get_as_path(array_value);
        let mut last_index: u128 = 0;
        for (i, operand) in self
            .get_element_values(bytes, elem_type, len)
            .into_iter()
            .enumerate()
        {
            last_index = i as u128;
            let index_value = self.body_visitor.get_u128_const_val(last_index);
            let index_path =
                Path::new_index(array_path.clone(), index_value).refine_paths(&self.state()); //todo: maybe not needed?
            self.body_visitor.state.update_value_at(index_path, operand);
        }
        let length_path = Path::new_length(array_path.clone());
        let length_value = self.body_visitor.get_u128_const_val(last_index + 1);
        self.body_visitor
            .state
            .update_value_at(length_path, length_value);
        SymbolicValue::make_reference(array_path)
    }

    #[warn(dead_code)]
    fn get_element_values(
        &mut self,
        bytes: &[u8],
        elem_type: ExpressionType,
        len: Option<u128>,
    ) -> Vec<Rc<SymbolicValue>> {
        let is_signed_type = elem_type.is_signed_integer();
        let bytes_per_elem = (elem_type.bit_length() / 8) as usize;
        if let Some(len) = len {
            assert_eq!(
                len * (bytes_per_elem as u128),
                u128::try_from(bytes.len()).unwrap()
            );
        }
        let chunks = bytes.chunks_exact(bytes_per_elem);
        if is_signed_type {
            fn get_signed_element_value(bytes: &[u8]) -> i128 {
                match bytes.len() {
                    1 => i128::from(bytes[0] as i8),
                    2 => i128::from(i16::from_ne_bytes(bytes.try_into().unwrap())),
                    4 => i128::from(i32::from_ne_bytes(bytes.try_into().unwrap())),
                    8 => i128::from(i64::from_ne_bytes(bytes.try_into().unwrap())),
                    16 => i128::from_ne_bytes(bytes.try_into().unwrap()),
                    _ => unreachable!(),
                }
            }

            let signed_numbers = chunks.map(get_signed_element_value);
            signed_numbers
                .map(|n| Rc::new(ConstantValue::Int(Integer::from(n)).into()))
                .collect()
        } else {
            fn get_unsigned_element_value(bytes: &[u8]) -> u128 {
                match bytes.len() {
                    1 => u128::from(bytes[0]),
                    2 => u128::from(u16::from_ne_bytes(bytes.try_into().unwrap())),
                    4 => u128::from(u32::from_ne_bytes(bytes.try_into().unwrap())),
                    8 => u128::from(u64::from_ne_bytes(bytes.try_into().unwrap())),
                    16 => u128::from_ne_bytes(bytes.try_into().unwrap()),
                    _ => unreachable!(),
                }
            }

            let unsigned_numbers = chunks.map(get_unsigned_element_value);
            unsigned_numbers
                .map(|n| Rc::new(ConstantValue::Int(Integer::from(n)).into()))
                .collect()
        }
    }

    fn get_scalar_int_data(scalar_int: &ScalarInt) -> (u128, usize) {
        let size = scalar_int.size();
        let data: u128 = scalar_int.try_to_bits(size).unwrap();
        (data, size.bytes() as usize)
    }

    // TODO: implement promoted constant
    fn visit_constant(
        &mut self,
        // _user_ty: Option<UserTypeAnnotationIndex>, // TODO: Is this argument useful?
        literal: &Const<'tcx>,
    ) -> Rc<SymbolicValue> {
        let mut kind = literal.kind();
        // let lty = literal.ty();
        // let mut val = literal.val;
        // let ty = literal.ty;

        if let rustc_middle::ty::ConstKind::Unevaluated(_unevaluated) = &kind {
            let infcx = self
                .body_visitor
                .context
                .tcx
                .infer_ctxt()
                .build(TypingMode::non_body_analysis());
            kind = rustc_trait_selection::traits::evaluate_const(
                &infcx,
                *literal,
                self.body_visitor.type_visitor.get_param_env(),
            )
            .kind()
        }

        let result;

        match &kind {
            rustc_middle::ty::ConstKind::Param(ParamConst { index, .. }) => {
                if let Some(gen_args) = self.body_visitor.type_visitor.generic_arguments {
                    if let Some(arg_val) = gen_args.as_ref().get(*index as usize) {
                        return self.visit_constant(&arg_val.expect_const());
                    }
                } else {
                    return symbolic_value::BOTTOM.into();
                }
                unreachable!(
                    "reference to unmatched generic constant argument {:?} {:?}",
                    literal, self.body_visitor.current_span
                );
            }
            // ZSTs, integers, `bool`, `char` and small structs are represented as scalars.
            // See the `ScalarInt` documentation for how `ScalarInt` guarantees that equal values
            // of these types have the same representation.
            rustc_middle::ty::ConstKind::Value(lty, ValTree::Leaf(scalar_int)) => {
                let (data, size) = Self::get_scalar_int_data(scalar_int);
                result = self.get_constant_from_scalar(*lty, data, size);
                // self.get_constant_value_from_scalar(lty, data, size)
            }
            // The fields of any kind of aggregate. Structs, tuples and arrays are represented by
            // listing their fields' values in order.
            // Enums are represented by storing their discriminant as a field, followed by all
            // the fields of the variant.
            rustc_middle::ty::ConstKind::Value(lty, val_tree) => {
                let heap_block = self.get_heap_block_and_path(*lty, val_tree);
                // self.deserialize_val_tree(val_tree, heap_path, lty);
                return heap_block;
            }
            _ => {
                debug!("kind {:?}", kind);
                return symbolic_value::BOTTOM.into();
            }
        }

        Rc::new(result.clone().into())
    }

    fn get_heap_block_and_path(
        &mut self,
        lty: Ty<'tcx>,
        _val_tree: &ValTree<'tcx>,
    ) -> Rc<SymbolicValue> {
        let size = 0; // todo: get it from the type or val_tree
        let heap_block = self.body_visitor.get_new_heap_block(
            Rc::new((size as u128).into()),
            Rc::new(1u128.into()),
            lty,
        );
        heap_block
    }

    // fn get_reference_to_slice(
    //     &mut self,
    //     ty: &TyKind<'tcx>,
    //     data: &'tcx mir::interpret::Allocation,
    //     start: usize,
    //     end: usize,
    // ) -> Rc<SymbolicValue> {
    //     // The rust compiler should ensure this.
    //     assert!(end >= start);
    //     let slice_len = end - start;
    //     let bytes = data
    //         .get_bytes(
    //             &self.body_visitor.context.tcx,
    //             // invent a pointer, only the offset is relevant anyway
    //             mir::interpret::Pointer::new(
    //                 mir::interpret::AllocId(0),
    //                 rustc_target::abi::Size::from_bytes(start as u64),
    //             ),
    //             rustc_target::abi::Size::from_bytes(slice_len as u64),
    //         )
    //         .unwrap();
    //     let slice = &bytes[start..end];
    //     match ty {
    //         TyKind::Ref(_, ty, _) => match ty.kind() {
    //             TyKind::Array(elem_type, ..) | TyKind::Slice(elem_type) => self
    //                 .deconstruct_reference_to_constant_array(
    //                     slice,
    //                     elem_type.kind().into(),
    //                     None,
    //                     ty,
    //                 ),
    //             _ => Rc::new(symbolic_value::BOTTOM),
    //         },
    //         _ => unreachable!(),
    //     }
    // }

    // fn visit_reference_to_array_constant(
    //     &mut self,
    //     val: &rustc_middle::ty::ConstKind<'tcx>,
    //     ty: Ty<'tcx>,
    //     elem_type: Ty<'tcx>,
    //     length: &rustc_middle::ty::Const<'tcx>,
    // ) -> Rc<SymbolicValue> {
    //     if let rustc_middle::ty::ConstKind::Value(ConstValue::Scalar(Scalar::Int(scalar_int), ..)) =
    //         &length.val
    //     {
    //         let data = scalar_int.assert_bits(scalar_int.size());
    //         let len = data;
    //         let e_type = ExpressionType::from(elem_type.kind());
    //         match val {
    //             rustc_middle::ty::ConstKind::Value(ConstValue::Slice { data, start, end }) => {
    //                 // The Rust compiler should ensure this.
    //                 assert!(*end > *start);
    //                 let slice_len = *end - *start;
    //                 let bytes = data
    //                     .get_bytes(
    //                         &self.body_visitor.context.tcx,
    //                         // invent a pointer, only the offset is relevant anyway
    //                         mir::interpret::Pointer::new(
    //                             mir::interpret::AllocId(0),
    //                             rustc_target::abi::Size::from_bytes(*start as u64),
    //                         ),
    //                         rustc_target::abi::Size::from_bytes(slice_len as u64),
    //                     )
    //                     .unwrap();
    //                 let slice = &bytes[*start..*end];
    //                 self.deconstruct_reference_to_constant_array(slice, e_type, Some(len), ty)
    //             }
    //             rustc_middle::ty::ConstKind::Value(ConstValue::Scalar(
    //                 mir::interpret::Scalar::Ptr(ptr),
    //             )) => {
    //                 if let Some(rustc_middle::mir::interpret::GlobalAlloc::Static(def_id)) =
    //                     self.body_visitor.context.tcx.get_global_alloc(ptr.alloc_id)
    //                 {
    //                     // TODO: implement this
    //                     // unreachable!("static is not supported yet");
    //                     return SymbolicValue::make_reference(self.body_visitor.import_static(
    //                         Path::new_static(self.body_visitor.context.tcx, def_id),
    //                     ));
    //                 }
    //                 let alloc = self
    //                     .body_visitor
    //                     .context
    //                     .tcx
    //                     .global_alloc(ptr.alloc_id)
    //                     .unwrap_memory();
    //                 let alloc_len = alloc.len() as u64;
    //                 let offset_bytes = ptr.offset.bytes();
    //                 // The Rust compiler should ensure this.
    //                 assert!(alloc_len > offset_bytes);
    //                 let num_bytes = alloc_len - offset_bytes;
    //                 let bytes = alloc
    //                     .get_bytes(
    //                         &self.body_visitor.context.tcx,
    //                         *ptr,
    //                         rustc_target::abi::Size::from_bytes(num_bytes),
    //                     )
    //                     .unwrap();
    //                 self.deconstruct_reference_to_constant_array(&bytes, e_type, Some(len), ty)
    //             }
    //             _ => {
    //                 debug!("unsupported val of type Ref: {:?}", val);
    //                 unimplemented!();
    //             }
    //         }
    //     } else {
    //         debug!("unsupported array length: {:?}", length);
    //         unimplemented!();
    //     }
    // }

    #[allow(dead_code)]
    fn deconstruct_reference_to_constant_array(
        &mut self,
        bytes: &[u8],
        elem_type: ExpressionType,
        len: Option<u128>,
        array_ty: Ty<'tcx>,
    ) -> Rc<SymbolicValue> {
        let byte_len = bytes.len();
        let alignment = self
            .body_visitor
            .get_u128_const_val((elem_type.bit_length() / 8) as u128);
        let byte_len_value = self.body_visitor.get_u128_const_val(byte_len as u128);
        let array_value = self
            .body_visitor
            .get_new_heap_block(byte_len_value, alignment, array_ty);
        let array_path = Path::get_as_path(array_value);
        let mut last_index: u128 = 0;
        let mut value_map = self.state().symbolic_domain.value_map.clone();
        for (i, operand) in self
            .get_element_values(bytes, elem_type, len)
            .into_iter()
            .enumerate()
        {
            last_index = i as u128;
            if i < k_limits::MAX_BYTE_ARRAY_LENGTH {
                let index_value = self.body_visitor.get_u128_const_val(last_index);
                let index_path = Path::new_index(array_path.clone(), index_value);
                value_map.insert(index_path, operand);
            } else {
                info!(
                    "constant array has {} elements, but maximum tracked is {}",
                    i,
                    k_limits::MAX_BYTE_ARRAY_LENGTH
                );
            }
        }
        let length_path = Path::new_length(array_path.clone());
        let length_value = self.body_visitor.get_u128_const_val(last_index + 1);
        value_map.insert(length_path, length_value);
        self.body_visitor.state.symbolic_domain.value_map = value_map;
        SymbolicValue::make_reference(array_path)
    }

    // fn get_reference_to_constant(
    //     &mut self,
    //     literal: &rustc_middle::ty::Const<'tcx>,
    //     ty: Ty<'tcx>,
    // ) -> Rc<SymbolicValue> {
    //     match &literal.val {
    //         rustc_middle::ty::ConstKind::Value(ConstValue::Scalar(Scalar::Ptr(p))) => {
    //             if let Some(rustc_middle::mir::interpret::GlobalAlloc::Static(def_id)) =
    //                 self.body_visitor.context.tcx.get_global_alloc(p.alloc_id)
    //             {
    //                 // TODO: implement this
    //                 // let name = utils::summary_key_str(self.body_visitor.context.tcx, def_id);
    //                 // let expression_type: ExpressionType = ExpressionType::from(ty.kind());
    //                 // let path = Rc::<SymbolicValue>::new(
    //                 //     PathEnum::StaticVariable {
    //                 //         def_id: Some(def_id),
    //                 //         summary_cache_key: name,
    //                 //         expression_type,
    //                 //     }
    //                 //     .into(),
    //                 // );
    //                 // unreachable!("static is not supported yet");
    //                 return SymbolicValue::make_reference(
    //                     self.body_visitor
    //                         .import_static(Path::new_static(self.body_visitor.context.tcx, def_id)),
    //                 );
    //             }
    //             debug!("span: {:?}", self.body_visitor.current_span);
    //             debug!("type kind {:?}", ty.kind());
    //             debug!("ptr {:?}", p);
    //             unreachable!();
    //         }
    //         rustc_middle::ty::ConstKind::Value(ConstValue::Slice { data, start, end }) => {
    //             self.get_reference_to_slice(&ty.kind(), *data, *start, *end)
    //         }
    //         _ => {
    //             debug!("span: {:?}", self.body_visitor.current_span);
    //             debug!("type kind {:?}", ty.kind());
    //             debug!("unimplemented constant {:?}", literal);
    //             unreachable!();
    //         }
    //     }
    // }

    // fn get_enum_variant_as_constant(
    //     &mut self,
    //     literal: &rustc_middle::ty::Const<'tcx>,
    //     ty: Ty<'tcx>,
    // ) -> Rc<SymbolicValue> {
    //     let result;
    //     match &literal.val {
    //         rustc_middle::ty::ConstKind::Value(ConstValue::Scalar(Scalar::Int(scalar_int)))
    //             if scalar_int.size().bytes() == 1 =>
    //         {
    //             let data = scalar_int.assert_bits(scalar_int.size());
    //             let e = self.body_visitor.get_new_heap_block(
    //                 Rc::new(1u128.into()),
    //                 Rc::new(1u128.into()),
    //                 ty,
    //             );
    //             if let Expression::HeapBlock { .. } = &e.expression {
    //                 let p = Path::new_discriminant(Path::get_as_path(e.clone()));
    //                 let d = self.body_visitor.get_u128_const_val(data);
    //                 self.body_visitor.state.update_value_at(p, d);
    //                 return e;
    //             }
    //             unreachable!();
    //         }
    //         _ => {
    //             debug!("span: {:?}", self.body_visitor.current_span);
    //             debug!("type kind {:?}", ty.kind());
    //             debug!("unimplemented constant {:?}", literal);
    //             result = &ConstantValue::Top;
    //         }
    //     };
    //     Rc::new(result.clone().into())
    // }

    pub fn get_path_for_place(&mut self, place: &mir::Place<'tcx>) -> Rc<Path> {
        let base_path: Rc<Path> = Path::new_local_parameter_or_result(
            place.local.as_usize(),
            self.body_visitor.fresh_variable_offset,
            self.mir.arg_count,
        );
        if place.projection.is_empty() {
            let ty = self
                .body_visitor
                .type_visitor
                .get_rustc_place_type(place, self.body_visitor.current_span);
            match &ty.kind() {
                TyKind::Array(_, len) => {
                    let len_val = self.visit_constant(&len);
                    let len_path = Path::new_length(base_path.clone()).refine_paths(&self.state());
                    self.body_visitor.state.update_value_at(len_path, len_val);
                }
                TyKind::Closure(def_id, generic_args) | TyKind::Coroutine(def_id, generic_args) => {
                    let func_const = self.visit_function_reference(*def_id, ty, Some(generic_args));
                    let func_val = Rc::new(func_const.clone().into());
                    self.body_visitor
                        .state
                        .update_value_at(base_path.clone(), func_val);
                }
                TyKind::FnDef(def_id, generic_args) => {
                    let func_const = self.visit_function_reference(
                        *def_id,
                        ty,
                        Some(generic_args.as_closure().args),
                    );
                    let func_val = Rc::new(func_const.clone().into());
                    self.body_visitor
                        .state
                        .update_value_at(base_path.clone(), func_val);
                }
                TyKind::Alias(
                    rustc_middle::ty::Opaque,
                    rustc_middle::ty::AliasTy { def_id, .. },
                ) => {
                    if let TyKind::Closure(def_id, generic_args)
                    | TyKind::Coroutine(def_id, generic_args) = self
                        .body_visitor
                        .context
                        .tcx
                        .type_of(*def_id)
                        .skip_binder()
                        .kind()
                    {
                        let func_const =
                            self.visit_function_reference(*def_id, ty, Some(generic_args));
                        let func_val = Rc::new(func_const.clone().into());
                        self.body_visitor
                            .state
                            .update_value_at(base_path.clone(), func_val);
                    }
                }
                // TyKind::Opaque(def_id, ..) => {
                //     if let TyKind::Closure(def_id, generic_args) =
                //         self.body_visitor.context.tcx.type_of(*def_id).kind()
                //     {
                //         let func_const = self.visit_function_reference(
                //             *def_id,
                //             ty,
                //             generic_args.as_generator().substs,
                //         );
                //         let func_val = Rc::new(func_const.clone().into());
                //         self.body_visitor
                //             .state
                //             .update_value_at(base_path.clone(), func_val);
                //     }
                // }
                _ => (),
            }
            base_path
        } else {
            self.visit_projection(base_path, &place.projection)
        }
    }

    fn visit_projection(
        &mut self,
        base_path: Rc<Path>,
        projection: &[mir::PlaceElem<'tcx>],
    ) -> Rc<Path> {
        let result = projection.iter().fold(base_path, |base_path, elem| {
            if let Some(selector) = self.visit_projection_elem(&elem) {
                Path::new_qualified(base_path, Rc::new(selector)).refine_paths(&self.state())
            } else {
                base_path.refine_paths(&self.state())
            }
        });
        result
    }

    fn visit_projection_elem(
        &mut self,
        projection_elem: &mir::ProjectionElem<mir::Local, Ty<'tcx>>,
    ) -> Option<PathSelector> {
        match projection_elem {
            mir::ProjectionElem::Deref => Some(PathSelector::Deref),
            // For simplicity, we ignore the case where this field access is applied on union types
            mir::ProjectionElem::Field(field, _field_ty) => {
                Some(PathSelector::Field(field.index()))
            }
            mir::ProjectionElem::Index(local) => {
                let local_path = Path::new_local_parameter_or_result(
                    local.as_usize(),
                    self.body_visitor.fresh_variable_offset,
                    self.mir.arg_count,
                );
                let index_value = self.body_visitor.lookup_path_and_refine_result(
                    local_path,
                    self.body_visitor.context.tcx.types.usize,
                );
                Some(PathSelector::Index(index_value))
            }
            mir::ProjectionElem::ConstantIndex {
                offset,
                min_length,
                from_end,
            } => Some(PathSelector::ConstantIndex {
                offset: *offset,
                min_length: *min_length,
                from_end: *from_end,
            }),
            // Ignore subslice, consider it as the whole slice
            mir::ProjectionElem::Subslice { .. } => None,
            mir::ProjectionElem::Downcast(..) => None,
            mir::ProjectionElem::Subtype(..) => None,
            mir::ProjectionElem::OpaqueCast(..) => None, 
        }
    }

    fn visit_switch_int(
        &mut self,
        discr: &mir::Operand<'tcx>,
        _switch_ty: rustc_middle::ty::Ty<'tcx>,
        targets: &mir::SwitchTargets,
    ) {
        let mut default_exit_condition = Rc::new(SymbolicValue::new_true());
        let discr = self.visit_operand(discr);
        for (v, target) in targets.iter() {
            let val: Rc<SymbolicValue> = Rc::new(ConstantValue::Int(Integer::from(v)).into());
            let cond = discr.equals(val);
            let not_cond = cond.logical_not();
            default_exit_condition = default_exit_condition.and(not_cond);
            self.body_visitor.state.exit_conditions.insert(target, cond);
        }
        self.body_visitor
            .state
            .exit_conditions
            .insert(targets.otherwise(), default_exit_condition);
    }

    fn visit_return(&mut self) {
        debug!("Visiting return at block: {:?}", self.current_block);
        self.body_visitor.result_blocks.insert(self.current_block);

        // Test whether tainted variables reach the `Return` terminator.

        // `_0` is always used for return value
        let ret = mir::Local::from_u32(0);
        if self.body_visitor.tainted_variables.contains(&ret) {
            debug!("Found possible double-free or use-after-free!");
            let warning = self.body_visitor.context.session.dcx().struct_span_warn(
                self.body_visitor.current_span,
                "[MirChecker] Possible error n visit return: double-free or use-after-free",
            );
            self.body_visitor
                .emit_diagnostic(warning, true, DiagnosticCause::Memory);
        }
    }

    fn visit_drop(
        &mut self,
        place: &mir::Place<'tcx>,
        _target: mir::BasicBlock,
        _unwind: mir::UnwindAction,
        // The `replace` flag indicates whether this terminator was created as part of an assignment.
        // This should only be used for diagnostic purposes, and does not have any operational
        // meaning.
        _replace: bool,
    ) {
        // Test whether tainted variables reach the `Drop` terminator.
        if self.body_visitor.tainted_variables.contains(&place.local) {
            let warning = self.body_visitor.context.session.dcx().struct_span_warn(
                self.body_visitor.current_span,
                format!(
                    "[MirChecker] Possible error in visit drop: double-free or use-after-free for {:?}",
                    self.body_visitor.get_var_name(&mir::Operand::Move(*place))
                ),
            );
            self.body_visitor
                .emit_diagnostic(warning, true, DiagnosticCause::Memory);
        }

        let dropped_path = self.visit_place(place);
        let dropped_path_ty = self
            .body_visitor
            .type_visitor
            .get_rustc_place_type(place, self.body_visitor.current_span);
        let dropped_val = self
            .body_visitor
            .lookup_path_and_refine_result(dropped_path.clone(), dropped_path_ty);

        // Get related heaps from the symbolic domain
        // E.g. if droped_path is `local_1`, and there are `local_1.0.0.0: &(local_1000001), local_1000001.0.0: heap_0`
        // then we should record `heap_0`
        fn get_related_heaps(
            dropped_path: Rc<Path>,
            symbolic_domain: &SymbolicDomain,
        ) -> Option<Rc<SymbolicValue>> {
            for (path, value) in &symbolic_domain.value_map {
                if path.is_rooted_by(&dropped_path) {
                    match value.expression {
                        Expression::HeapBlock { .. } => {
                            return Some(value.clone());
                        }
                        _ => {
                            let new_path = Path::get_as_path(value.clone());
                            return get_related_heaps(new_path, symbolic_domain);
                        }
                    }
                }
            }
            None
        }
        let related_heap = get_related_heaps(dropped_path.clone(), &self.state().symbolic_domain);
        debug!(
            "Visiting Drop: path: {:?}, value: {:?}, related_heaps: {:?}",
            dropped_path, dropped_val, related_heap
        );

        if let Some(related_heap) = related_heap {
            if self
                .body_visitor
                .context
                .dropped_heaps
                .contains(&related_heap)
            {
                let warning = self.body_visitor.context.session.dcx().struct_span_warn(
                    self.body_visitor.current_span,
                    format!(
                        "[MirChecker] Possible error: double-free or use-after-free for {:?}",
                        self.body_visitor.get_var_name(&mir::Operand::Move(*place))
                    ),
                );
                self.body_visitor
                    .emit_diagnostic(warning, true, DiagnosticCause::Memory);
            } else {
                self.body_visitor
                    .context
                    .dropped_heaps
                    .insert(related_heap.clone());
            }
        }
    }

    /// Block ends with the call of a function.
    ///
    /// #Arguments
    /// * `func` - The function that’s being called
    /// * `args` - Arguments the function is called with.
    /// These are owned by the callee, which is free to modify them.
    /// This allows the memory occupied by "by-value" arguments to be
    /// reused across function calls without duplicating the contents.
    /// * `destination` - Destination for the return value. If some, the call returns a value.
    /// * `unwind` - Work to be done if the call unwinds.
    /// * `call_source` - Where this call came from in HIR/THIR.
    /// operator. True for overloaded function call.
    fn visit_call(
        &mut self,
        func: &mir::Operand<'tcx>,
        args: &[Spanned<mir::Operand<'tcx>>],
        destination: mir::Place<'tcx>,
        _target: Option<mir::BasicBlock>,
        _unwind: mir::UnwindAction,
        _call_source: mir::CallSource,
        _fn_span: &rustc_span::Span,
    ) {
        // debug!("source location {:?}", self.body_visitor.current_span);
        debug!("function operand: {:?}, arguments: {:?}", func, args);
        debug!(
            "self.generic_argument_map {:?}",
            self.body_visitor.type_visitor.generic_argument_map
        );
        debug!("Before visit_call, env: {:?}", self.state());
        // Store the offset that is about to be used while executing the following call visitor
        let old_offset = self.body_visitor.next_fresh_variable_offset;
        // Get `SymbolicValue` from `mir::Operand::Constant`
        let func_to_call = self.visit_operand(func);
        info!("func_to_call is {:?}", func_to_call);
        // Get `FunctionReference` from `SymbolicValue`
        let func_ref = self.get_func_ref(&func_to_call);
        // If the function cannot be reliably analyzed, simply ignore it and return
        let func_ref_to_call = if let Some(fr) = func_ref {
            fr
        } else {
            info!(
                "function {} can't be reliably analyzed because it calls an unknown function.",
                utils::summary_key_str(self.body_visitor.context.tcx, self.def_id),
            );
            return;
        };
        let callee_def_id = func_ref_to_call
            .def_id
            .expect("callee obtained via operand should have def id");
        // The list of generic arguments
        let generic_args = self
            .body_visitor
            .crate_context
            .generic_args_cache
            .get(&callee_def_id)
            .expect("MIR should ensure this");
        // Try to specialize generic arguments
        let callee_generic_arguments = self.body_visitor.type_visitor.specialize_generic_args(
            generic_args,
            &self.body_visitor.type_visitor.generic_argument_map,
        );
        let actual_args: Vec<(Rc<Path>, Rc<SymbolicValue>)> = args
            .iter()
            .map(|arg| (self.get_operand_path(&arg.node), self.visit_operand(&arg.node)))
            .collect();

        // let mut args_path_vec: Vec<(Rc<Path>, Rc<SymbolicValue>)> = Vec::new();
        // for args_index in 0..args.len() {
        //     args_path_vec.push((
        //         actual_args[args_index].0.clone(),
        //         actual_args[args_index].1.clone(),
        //     ));
        // }
        // if self.body_visitor.terminator_to_place.contains_key(span) {
        // } else {
        //     self.body_visitor
        //         .terminator_to_place
        //         .insert(*span, args_path_vec);
        // }

        let actual_argument_types: Vec<Ty<'tcx>> = args
            .iter()
            .map(|arg| {
                let arg_ty = self.get_operand_rustc_type(&arg.node);
                self.body_visitor
                    .type_visitor
                    .specialize_generic_argument_type(
                        arg_ty,
                        &self.body_visitor.type_visitor.generic_argument_map,
                    )
            })
            .collect();
        // Construct the map from generic arguments to their actual types
        let callee_generic_argument_map = self.body_visitor.type_visitor.get_generic_arguments_map(
            callee_def_id,
            callee_generic_arguments,
            &actual_argument_types,
        );

        let func_const = ConstantValue::Function(func_ref_to_call);
        let func_const_args = &self.get_function_constant_args(&actual_args);

        let destination_path = self.get_path_for_place(&destination);

        debug!("actual_args: {:?}", actual_args);
        debug!("actual_argument_types: {:?}", actual_argument_types);
        debug!("destination: {:?}", destination_path);
        debug!("callee_fun_val: {:?}", func_to_call);

        // Create a call visitor
        let mut call_visitor = CallVisitor::new(
            self,
            callee_def_id,
            Some(callee_generic_arguments),
            callee_generic_argument_map.clone(),
            func_const,
        );
        call_visitor.args = &args;
        call_visitor.actual_args = &actual_args;
        call_visitor.actual_argument_types = &actual_argument_types;
        call_visitor.destination = destination.clone();
        call_visitor.callee_fun_val = func_to_call;
        call_visitor.function_constant_args = func_const_args;
        debug!("Calling function {:?}", call_visitor.callee_func_ref);

        // If the function is a special function, handle it separately
        if call_visitor.handled_as_special_function_call() {
            debug!("Successfully handled as special function call");
            return;
        }

        debug!("Executing call visitor...");
        // Run the call visitor and get post states
        let function_post_state = call_visitor
            .get_function_post_state()
            .unwrap_or_else(AbstractDomain::default);

        // Here, the offset should have already been reset

        debug!(
            "Finish call visitor, get function post state {:?}",
            function_post_state
        );
        debug!(
            "Before handling side-effects, pre env {:?}",
            call_visitor.block_visitor.state()
        );
        call_visitor.transfer_and_refine_normal_return_state(&function_post_state, old_offset);
        debug!(
            "After handling side-effects, post env {:?}",
            call_visitor.block_visitor.state()
        );
    }

    fn get_operand_rustc_type(&mut self, operand: &mir::Operand<'tcx>) -> Ty<'tcx> {
        match operand {
            mir::Operand::Copy(place) | mir::Operand::Move(place) => self
                .body_visitor
                .type_visitor
                .get_rustc_place_type(place, self.body_visitor.current_span),
            mir::Operand::Constant(constant) => {
                let mir::ConstOperand { const_, .. } = constant.borrow();
                const_.ty()
            }
        }
    }

    fn get_function_constant_args(
        &self,
        actual_args: &[(Rc<Path>, Rc<SymbolicValue>)],
    ) -> Vec<(Rc<Path>, Rc<SymbolicValue>)> {
        let mut result = vec![];
        // TODO: Do we need to directly access the symbolic domain?
        for (path, value) in self.state().symbolic_domain.value_map.iter() {
            if let Expression::CompileTimeConstant(ConstantValue::Function(..)) = &value.expression
            {
                for (i, (arg_path, arg_val)) in actual_args.iter().enumerate() {
                    if (*path) == *arg_path || path.is_rooted_by(arg_path) {
                        let param_path_root =
                            Path::new_parameter(i + 1, self.body_visitor.fresh_variable_offset);
                        let param_path = path.replace_root(arg_path, param_path_root);
                        result.push((param_path, value.clone()));
                        break;
                    } else {
                        match &arg_val.expression {
                            Expression::Reference(ipath)
                            | Expression::Variable { path: ipath, .. } => {
                                if (*path) == *ipath || path.is_rooted_by(ipath) {
                                    let param_path_root = Path::new_parameter(
                                        i + 1,
                                        self.body_visitor.fresh_variable_offset,
                                    );
                                    let param_path = path.replace_root(arg_path, param_path_root);
                                    result.push((param_path, value.clone()));
                                    break;
                                }
                            }
                            _ => {}
                        }
                    }
                }
            }
        }
        for (i, (path, value)) in actual_args.iter().enumerate() {
            if let PathEnum::Alias { value: val } = &path.value {
                if *val == *value {
                    if let Expression::CompileTimeConstant(ConstantValue::Function(..)) =
                        &value.expression
                    {
                        let param_path =
                            Path::new_parameter(i + 1, self.body_visitor.fresh_variable_offset);
                        result.push((param_path, value.clone()));
                    }
                }
            }
        }
        result
    }

    fn get_operand_path(&mut self, operand: &mir::Operand<'tcx>) -> Rc<Path> {
        match operand {
            mir::Operand::Copy(place) | mir::Operand::Move(place) => self.visit_place(place),
            mir::Operand::Constant(..) => Path::new_alias(self.visit_operand(operand)),
        }
    }

    fn get_func_ref(&mut self, val: &Rc<SymbolicValue>) -> Option<Rc<FunctionReference>> {
        let extract_func_ref = |c: &ConstantValue| match c {
            ConstantValue::Function(func_ref) => Some(func_ref.clone()),
            _ => None,
        };
        match &val.expression {
            Expression::CompileTimeConstant(c) => {
                return extract_func_ref(c);
            }
            Expression::Reference(path)
            | Expression::Variable {
                path,
                var_type: ExpressionType::NonPrimitive,
            }
            | Expression::Variable {
                path,
                var_type: ExpressionType::Reference,
            } => {
                let closure_ty = self
                    .body_visitor
                    .type_visitor
                    .get_path_rustc_type(path, self.body_visitor.current_span);
                let mut specialized_closure_ty = self
                    .body_visitor
                    .type_visitor
                    .specialize_generic_argument_type(
                        closure_ty,
                        &self.body_visitor.type_visitor.generic_argument_map,
                    );
                if let TyKind::Alias(
                    rustc_middle::ty::Opaque,
                    rustc_middle::ty::AliasTy { def_id, args, .. },
                ) = specialized_closure_ty.kind()
                {
                    let args = self.body_visitor.type_visitor.specialize_generic_args(
                        args,
                        &self.body_visitor.type_visitor.generic_argument_map,
                    );
                    self.body_visitor
                        .crate_context
                        .generic_args_cache
                        .insert(*def_id, args);
                    let closure_ty = self.body_visitor.context.tcx.type_of(*def_id).skip_binder();
                    let map = self.body_visitor.type_visitor.get_generic_arguments_map(
                        *def_id,
                        args,
                        &[],
                    );
                    specialized_closure_ty = self
                        .body_visitor
                        .type_visitor
                        .specialize_generic_argument_type(closure_ty, &map);
                }
                match specialized_closure_ty.kind() {
                    TyKind::Closure(def_id, args) | TyKind::FnDef(def_id, args) => {
                        return extract_func_ref(self.visit_function_reference(
                            *def_id,
                            specialized_closure_ty,
                            Some(args),
                        ));
                    }
                    TyKind::Ref(_, ty, _) => {
                        let specialized_closure_ty = self
                            .body_visitor
                            .type_visitor
                            .specialize_generic_argument_type(
                                *ty,
                                &self.body_visitor.type_visitor.generic_argument_map,
                            );
                        if let TyKind::Closure(def_id, args) | TyKind::FnDef(def_id, args) =
                            specialized_closure_ty.kind()
                        {
                            return extract_func_ref(self.visit_function_reference(
                                *def_id,
                                specialized_closure_ty,
                                Some(args),
                            ));
                        }
                    }
                    _ => {}
                }
            }
            _ => {}
        }
        None
    }

    fn visit_assert(
        &mut self,
        cond: &mir::Operand<'tcx>,
        _expected: bool,
        _msg: &mir::AssertMessage<'tcx>,
        _target: mir::BasicBlock,
        _unwind: mir::UnwindAction,
    ) {
        let cond_value = self.visit_operand(cond);
        if let Some(place) = cond.place() {
            self.body_visitor
                .place_to_abstract_value
                .insert(place, cond_value);
        }
    }
    
    // fn visit_inline_asm(&mut self) {
    //     let span = self.body_visitor.current_span;
    //     let err = self
    //         .body_visitor
    //         .context
    //         .session
    //         .dcx()
    //         .struct_span_warn(span, "Inline assembly code is not supported.");
    //     self.body_visitor
    //         .emit_diagnostic(err, true, DiagnosticCause::Assembly);
    // }

    fn visit_rvalue(&mut self, path: Rc<Path>, rvalue: &mir::Rvalue<'tcx>) {
        // println!("visit_rvalue: {:?}", rvalue);
        match rvalue {
            mir::Rvalue::Use(operand) => {
                        debug!("Get RHS Rvalue: Use({:?})", operand);
                        self.visit_use(path, operand);
                    }
            mir::Rvalue::Repeat(operand, count) => {
                        debug!("Get RHS Rvalue: Repeat({:?}, {:?})", operand, count);
                        self.visit_repeat(path, operand, count);
                    }
            mir::Rvalue::Ref(_, _, place) | mir::Rvalue::RawPtr(_, place) => {
                        debug!("Get RHS Rvalue: Ref/AddressOf({:?})", place);
                        self.visit_address_of(path, place);
                    }
            // mir::Rvalue::Len(place) => {
            //             debug!("Get RHS Rvalue: Len({:?})", place);
            //             self.visit_len(path, place);
            //         }
            mir::Rvalue::Cast(cast_kind, operand, ty) => {
                        debug!(
                            "Get RHS Rvalue: Cast({:?}, {:?}, {:?})",
                            cast_kind, operand, ty
                        );
                        self.visit_cast(path, *cast_kind, operand, *ty);
                    }
            mir::Rvalue::BinaryOp(bin_op, box (left_operand, right_operand)) => {
                        debug!(
                            "Get RHS Rvalue: BinaryOp({:?}, {:?}, {:?})",
                            bin_op, left_operand, right_operand
                        );
                        self.visit_binary_op(path, *bin_op, left_operand, right_operand);
                    }
            // mir::Rvalue::CheckedBinaryOp(bin_op, box (left_operand, right_operand)) => {
            //             debug!(
            //                 "Get RHS Rvalue: CheckedBinaryOp({:?}, {:?}, {:?})",
            //                 bin_op, left_operand, right_operand
            //             );
            //             self.visit_checked_binary_op(path, *bin_op, left_operand, right_operand);
            //         }
            mir::Rvalue::NullaryOp(null_op, ty) => {
                        debug!("Get RHS Rvalue: NullaryOp({:?}, {:?})", null_op, ty);
                        self.visit_nullary_op(path, *null_op, *ty);
                    }
            mir::Rvalue::UnaryOp(unary_op, operand) => {
                        debug!("Get RHS Rvalue: UnaryOp({:?}, {:?})", unary_op, operand);
                        self.visit_unary_op(path, *unary_op, operand);
                    }
            mir::Rvalue::Discriminant(place) => {
                        debug!("Get RHS Rvalue: Discriminant({:?})", place);
                        self.visit_discriminant(path, place);
                    }
            mir::Rvalue::Aggregate(aggregate_kinds, operands) => {
                        debug!(
                            "Get RHS Rvalue: Aggregate({:?}, {:?})",
                            aggregate_kinds, operands
                        );
                        self.visit_aggregate(path, aggregate_kinds, operands);
                    }
            mir::Rvalue::ThreadLocalRef(def_id) => {
                        self.visit_thread_local_ref(*def_id);
                    }
            mir::Rvalue::ShallowInitBox(..) => todo!(),
            mir::Rvalue::CopyForDeref(..) => todo!(),
                    }
    }

    fn visit_thread_local_ref(&mut self, def_id: DefId) -> Rc<SymbolicValue> {
        let static_var = Path::new_static(self.body_visitor.context.tcx, def_id);
        SymbolicValue::make_reference(static_var)
    }

    // operands contains a list of values
    // E.g. Aggregate(Array(i32), [const 1_i32, const 2_i32, const 3_i32, const 4_i32, const 5_i32])
    fn visit_aggregate(
        &mut self,
        path: Rc<Path>,
        aggregate_kind: &mir::AggregateKind<'tcx>,
        operands: &IndexVec<FieldIdx, mir::Operand<'tcx>>,
    ) {
        // assert!(matches!(aggregate_kind, mir::AggregateKind::Array(..)));
        // let length_path = Path::new_length(path.clone()).refine_paths(&self.state());
        // let length_value = self.body_visitor.get_u128_const_val(operands.len() as u128);
        // self.body_visitor
        //     .state
        //     .update_value_at(length_path, length_value);

        // // Handle the list of operands
        // for (i, operand) in operands.iter().enumerate() {
        //     let index_value = self.body_visitor.get_u128_const_val(i as u128);
        //     let index_path = Path::new_index(path.clone(), index_value).refine_paths(&self.state());
        //     self.visit_used_operand(index_path, operand);
        // }
        match aggregate_kind {
            mir::AggregateKind::Array(_ty) => {
                let length_path = Path::new_length(path.clone());
                let length_value = self.body_visitor.get_u128_const_val(operands.len() as u128);
                self.body_visitor
                    .state
                    .update_value_at(length_path, length_value);
                for (i, operand) in operands.iter().enumerate() {
                    let index_value = self.body_visitor.get_u128_const_val(i as u128);
                    let index_path = Path::new_index(path.clone(), index_value);
                    // self.type_visitor_mut()
                    //     .set_path_rustc_type(index_path.clone(), *ty);
                    self.visit_use(index_path, operand);
                }
            }
            mir::AggregateKind::Tuple => {
                let ty = self
                    .body_visitor
                    .type_visitor
                    .get_path_rustc_type(&path, self.body_visitor.current_span);
                let _types = if let TyKind::Tuple(types) = ty.kind() {
                    types.as_slice()
                } else {
                    &[]
                };
                for (i, operand) in operands.iter().enumerate() {
                    let index_path = Path::new_field(path.clone(), i);
                    // if let Some(ty) = types.get(i) {
                    //     self.type_visitor_mut()
                    //         .set_path_rustc_type(index_path.clone(), *ty);
                    // };
                    self.visit_use(index_path, operand);
                }
            }
            mir::AggregateKind::Adt(def, variant_idx, args, _, _case_index) => {
                let path = path;
                let adt_def = self.body_visitor.context.tcx.adt_def(def);
                let variant_def = &adt_def.variants()[*variant_idx];
                let _adt_ty = self.body_visitor.context.tcx.type_of(def).skip_binder();
                if adt_def.is_enum() {
                    // let discr_path = Path::new_discriminant(path.clone());
                    // let discr_ty = adt_ty.discriminant_ty(self.body_visitor.context.tcx);
                    // let discr_bits =
                    //     match adt_ty.discriminant_for_variant(self.body_visitor.context.tcx, *variant_idx) {
                    //         Some(discr) => discr.val,
                    //         None => variant_idx.as_usize() as u128,
                    //     };
                    // let val = self.get_int_const_val(discr_bits, discr_ty);
                    // self.body_visitor.state.update_value_at(discr_path, val.clone());
                    // let discr_name = variant_def.name.to_string();
                    // path = Path::new_qualified(
                    //     path,
                    //     Rc::new(PathSelector::Downcast(
                    //         Rc::from(discr_name),
                    //         variant_idx.as_usize(),
                    //         val,
                    //     )),
                    // );
                } else if adt_def.is_union() {
                    // let num_cases = variant_def.fields.len();
                    // let case_index = case_index.unwrap_or(0usize.into());
                    // let field_path = Path::new_union_field(path, case_index.into(), num_cases);
                    // let field = &variant_def.fields[case_index];
                    // let field_ty = field.ty(self.body_visitor.context.tcx, args);
                    // // self.type_visitor_mut()
                    // //     .set_path_rustc_type(field_path.clone(), field_ty);
                    // self.visit_use(field_path, &operands[0usize.into()]);
                    return;
                }
                if variant_def.fields.is_empty() {
                    // self.body_visitor.state
                    //     .update_value_at(Path::new_field(path.clone(), 0), Rc::new(BOTTOM));
                }
                for (i, field) in variant_def.fields.iter().enumerate() {
                    let field_path = Path::new_field(path.clone(), i);
                    let _field_ty = field.ty(self.body_visitor.context.tcx, args);
                    // self.type_visitor_mut()
                    //     .set_path_rustc_type(field_path.clone(), field_ty);
                    if let Some(operand) = operands.get(i.into()) {
                        self.visit_use(field_path, operand);
                    } else {
                        debug!(
                            "variant has more fields than was serialized {:?}",
                            variant_def
                        );
                    }
                }
            }
            mir::AggregateKind::Closure(def_id, args)
            | mir::AggregateKind::Coroutine(def_id, args) 
            | mir::AggregateKind::CoroutineClosure(def_id, args)=> {
                let ty = self.body_visitor.context.tcx.type_of(*def_id).skip_binder();
                let func_const = self.visit_function_reference(*def_id, ty, Some(args));
                let func_val = Rc::new(func_const.clone().into());
                self.body_visitor.state.update_value_at(path.clone(), func_val);
                for (i, operand) in operands.iter().enumerate() {
                    let field_path = Path::new_field(path.clone(), i);
                    self.visit_use(field_path, operand);
                }
            }
            mir::AggregateKind::RawPtr(ty, mutbl) => {
                let thin_pointer_path = Path::new_field(path.clone(), 0);
                let pointer_type = Ty::new_ptr(self.body_visitor.context.tcx, *ty, *mutbl);
                self.body_visitor.type_visitor
                    .set_path_rustc_type(thin_pointer_path.clone(), pointer_type);
                self.visit_use(thin_pointer_path, &operands[0usize.into()]);
                let metadata_path = Path::new_field(path, 1);
                self.visit_use(metadata_path, &operands[1usize.into()]);
            }
        }
    }

    // fn visit_used_operand(&mut self, target_path: Rc<Path>, operand: &mir::Operand<'tcx>) {
    //     match operand {
    //         mir::Operand::Copy(place) => {
    //             self.visit_used_copy(target_path, place);
    //         }
    //         mir::Operand::Move(place) => {
    //             self.visit_used_move(target_path, place);
    //         }
    //         mir::Operand::Constant(constant) => {
    //             let mir::Constant {
    //                 user_ty, literal, ..
    //             } = constant.borrow();
    //             let const_value = self.visit_constant(*user_ty, &literal);
    //             self.body_visitor
    //                 .state
    //                 .update_value_at(target_path, const_value);
    //         }
    //     };
    // }

    // E.g. NullaryOp(Box, [usize; 5])
    fn visit_nullary_op(
        &mut self,
        path: Rc<Path>,
        null_op: mir::NullOp,
        ty: rustc_middle::ty::Ty<'tcx>,
    ) {
        let len =
            // Get the layout of the type
            if let Ok(ty_and_layout) = self.body_visitor.type_visitor.layout_of(ty) {
                Rc::new((ty_and_layout.layout.size.bytes() as u128).into())
            } else {
                SymbolicValue::make_typed_unknown(ExpressionType::U128)
            };
        let alignment = Rc::new(1u128.into());
        let value = match null_op {
            mir::NullOp::AlignOf => alignment,
            mir::NullOp::SizeOf => len,
            mir::NullOp::OffsetOf(fields) => {
                if let Ok(ty_and_layout) = self.body_visitor.type_visitor.layout_of(ty) {

                    let offset_in_bytes = self.body_visitor.context.tcx
                        .offset_of_subfield(self.body_visitor.type_visitor.get_typing_env(), ty_and_layout, fields.iter())
                        .bytes();
                    Rc::new((offset_in_bytes as u128).into())
                } else {
                    //todo: need expression that eventually refines into the actual offset
                    // let type_index = self.body_visitor.type_visitor.get_index_for(self.body_visitor.context.tcx.types.u128);
                    // SymbolicValue::make_typed_unknown(
                    //     ExpressionType::U128,
                    //     Path::new_local(996, type_index),
                    // )
                    symbolic_value::BOTTOM.into()
                }
            }
            mir::NullOp::UbChecks => SymbolicValue::make_typed_unknown(ExpressionType::U128),
        };
        self.body_visitor.state.update_value_at(path, value);
    }

    fn visit_unary_op(&mut self, path: Rc<Path>, un_op: mir::UnOp, operand: &mir::Operand<'tcx>) {
        match un_op {
            mir::UnOp::Neg => {
                let operand_path = self.get_operand_path(operand);
                self.body_visitor.state.numerical_domain.apply_un_op_place(
                    ApronOperation::Neg,
                    &operand_path,
                    &path,
                );
            }
            mir::UnOp::Not => {
                let val = self.visit_operand(operand);
                self.body_visitor
                    .state
                    .update_value_at(path, val.logical_not());
            }
            mir::UnOp::PtrMetadata => {
                // FIXME: Implement this
            }
        }
    }

    fn visit_discriminant(&mut self, path: Rc<Path>, place: &mir::Place<'tcx>) {
        let discriminant_path = Path::new_discriminant(self.visit_place(place));
        let discriminant_value = self.body_visitor.lookup_path_and_refine_result(
            discriminant_path,
            self.body_visitor.context.tcx.types.u128,
        );
        self.body_visitor
            .state
            .update_value_at(path, discriminant_value);
    }

    // E.g. Cast(Pointer(Unsize), move _3, std::boxed::Box<[i32]>)
    // Casting `_3` which is originally a pointer, to `std::boxed::Box<[i32]>`
    fn visit_cast(
        &mut self,
        path: Rc<Path>,
        cast_kind: mir::CastKind,
        operand: &mir::Operand<'tcx>,
        ty: rustc_middle::ty::Ty<'tcx>,
    ) {
        let operand_val = self.visit_operand(operand);
        match cast_kind {
            // TODO: do we need to check overflow while casting?
            mir::CastKind::Transmute 
            | mir::CastKind::IntToInt
            | mir::CastKind::FloatToFloat
            | mir::CastKind::FloatToInt
            | mir::CastKind::IntToFloat
            | mir::CastKind::FnPtrToPtr
            | mir::CastKind::PtrToPtr => {
                let result = operand_val.cast(ExpressionType::from(ty.kind()));
                self.body_visitor.state.update_value_at(path, result);
            }
            // Leave pointer unchanged
            // An exposing pointer to address cast. A cast between a pointer and an integer type, or
            // between a function pointer and an integer type.
            // See the docs on `expose_addr` for more details.
            mir::CastKind::PointerExposeProvenance
            // An address-to-pointer cast that picks up an exposed provenance.
            // See the docs on `from_exposed_addr` for more details.
            | mir::CastKind::PointerWithExposedProvenance
            // All sorts of pointer-to-pointer casts. Note that reference-to-raw-ptr casts are
            // translated into `&raw mut/const *r`, i.e., they are not actually casts.
            | mir::CastKind::PointerCoercion(..)
            // Cast into a dyn* object.
            // | mir::CastKind::DynStar 
            => {
                self.visit_use(path, operand);
            }
        }
    }

    fn bin_op_to_apron_bin_op(&mut self, bin_op: mir::BinOp) -> Option<ApronOperation> {
        let res = match bin_op {
            mir::BinOp::Add | mir::BinOp::AddUnchecked | mir::BinOp::AddWithOverflow => ApronOperation::Add,
            mir::BinOp::Sub | mir::BinOp::SubUnchecked | mir::BinOp::SubWithOverflow => ApronOperation::Sub,
            mir::BinOp::Mul | mir::BinOp::MulUnchecked | mir::BinOp::MulWithOverflow => ApronOperation::Mul,
            mir::BinOp::Div => ApronOperation::Div,
            mir::BinOp::Rem => ApronOperation::Rem,
            mir::BinOp::BitXor => ApronOperation::Xor,
            mir::BinOp::BitAnd => ApronOperation::And,
            mir::BinOp::BitOr => ApronOperation::Or,
            mir::BinOp::Shl | mir::BinOp::ShlUnchecked => ApronOperation::Shl,
            mir::BinOp::Shr | mir::BinOp::ShrUnchecked => ApronOperation::Shr,

            // Eq, Lt, Le, Ne, Ge, Gt, Offset are not handled by apron library
            mir::BinOp::Eq
            | mir::BinOp::Ge
            | mir::BinOp::Gt
            | mir::BinOp::Le
            | mir::BinOp::Lt
            | mir::BinOp::Ne
            | mir::BinOp::Offset
            | mir::BinOp::Cmp => return None,
        };
        Some(res)
    }

    fn visit_binary_op(
        &mut self,
        path: Rc<Path>,
        bin_op: mir::BinOp,
        left_operand: &mir::Operand<'tcx>,
        right_operand: &mir::Operand<'tcx>,
    ) {
        // For arithmetic binary operators, handle by numerical domain
        if let Some(op) = self.bin_op_to_apron_bin_op(bin_op) {
            match (left_operand, right_operand) {
                (mir::Operand::Constant(..), _) => {
                    match &self.visit_operand(left_operand).expression {
                        Expression::CompileTimeConstant(ConstantValue::Int(left_integer)) => {
                            let right_path = self.get_operand_path(right_operand);
                            self.body_visitor
                                .state
                                .numerical_domain
                                .apply_bin_op_const_place(op, &left_integer, &right_path, &path);
                        }
                        // Expression::CompileTimeConstant(ConstantValue::Top) => {
                        _ => {
                            self.body_visitor.state.numerical_domain.forget(&path);
                        }
                    }
                }
                (_, mir::Operand::Constant(..)) => {
                    match &self.visit_operand(right_operand).expression {
                        Expression::CompileTimeConstant(ConstantValue::Int(right_integer)) => {
                            let left_path = self.get_operand_path(left_operand);
                            self.body_visitor
                                .state
                                .numerical_domain
                                .apply_bin_op_place_const(op, &left_path, &right_integer, &path);
                        }
                        // Expression::CompileTimeConstant(ConstantValue::Top) => {
                        _ => {
                            self.body_visitor.state.numerical_domain.forget(&path);
                        }
                    }
                }
                _ => {
                    let left_path = self.get_operand_path(left_operand);
                    let right_path = self.get_operand_path(right_operand);

                    self.body_visitor
                        .state
                        .numerical_domain
                        .apply_bin_op_place_place(op, &left_path, &right_path, &path);
                }
            }
        }
        // For comparison operators, handle by abstract domain
        else {
            let left = self.visit_operand(left_operand);
            let right = self.visit_operand(right_operand);
            let result = match bin_op {
                mir::BinOp::Eq => left.equals(right),
                mir::BinOp::Ge => left.greater_or_equal(right),
                mir::BinOp::Gt => left.greater_than(right),
                mir::BinOp::Le => left.less_or_equal(right),
                mir::BinOp::Lt => left.less_than(right),
                mir::BinOp::Ne => left.not_equals(right),
                mir::BinOp::Offset => left,
                _ => unreachable!(),
            };
            debug!("Comparison result: {:?}", result);
            self.body_visitor.state.update_value_at(path, result);
        }
    }

    #[allow(dead_code)]
    fn visit_checked_binary_op(
        &mut self,
        path: Rc<Path>,
        bin_op: mir::BinOp,
        left_operand: &mir::Operand<'tcx>,
        right_operand: &mir::Operand<'tcx>,
    ) {
        let path0 = Path::new_field(path, 0).refine_paths(&self.state());
        self.visit_binary_op(path0, bin_op, left_operand, right_operand);
    }

    // Repeat `operand` for `count` times
    fn visit_repeat(&mut self, path: Rc<Path>, operand: &mir::Operand<'tcx>, count: &Const<'tcx>) {
        let length_path = Path::new_length(path.clone());
        let length_value = self.visit_constant(count);
        self.body_visitor
            .state
            .update_value_at(length_path, length_value.clone());
        let slice_path = Path::new_slice(path, length_value).refine_paths(&self.state());
        let initial_value = self.visit_operand(operand);
        self.body_visitor
            .state
            .update_value_at(slice_path, initial_value);
    }

    // TODO: check this
    // Convert mir::Operand into SymbolicValue
    fn visit_operand(&mut self, operand: &mir::Operand<'tcx>) -> Rc<SymbolicValue> {
        match operand {
            mir::Operand::Copy(place) | mir::Operand::Move(place) => {
                self.visit_operand_place(place)
            }
            mir::Operand::Constant(constant) => {
                let mir::ConstOperand { const_, .. } = constant.borrow();
                self.visit_literal(const_)
            }
        }
    }

    pub fn visit_literal(&mut self, literal: &mir::Const<'tcx>) -> Rc<SymbolicValue> {
        info!("visit_literal {:?}", literal);
        match literal {
            // This constant came from the type system
            mir::Const::Ty(_ty, c) => self.visit_constant(c),
            // An unevaluated mir constant which is not part of the type system.
            // mir::Const::Unevaluated(c, ty) => self.visit_unevaluated_const(c, *ty),
            // // This constant contains something the type system cannot handle (e.g. pointers).
            mir::Const::Val(v, ty) => self.visit_const_value(*v, *ty),
            // mir::Const::Val(v, ty) => self.
            _ => symbolic_value::BOTTOM.into()
        }
    }

    

    fn visit_const_value(&mut self, val: ConstValue<'tcx>, lty: Ty<'tcx>) -> Rc<SymbolicValue> {
        match val {
            // The raw bytes of a simple value.
            ConstValue::Scalar(Scalar::Int(scalar_int)) => {
                let (data, size) = Self::get_scalar_int_data(&scalar_int);
                Rc::new(self.get_constant_from_scalar(lty, data, size).into())
            }

            // A pointer into an `Allocation`. An `Allocation` in the `memory` module has a list of
            // relocations, but a `Scalar` is only large enough to contain one, so we just represent the
            // relocation and its associated offset together as a `Pointer` here.
            //
            // We also store the size of the pointer, such that a `Scalar` always knows how big it is.
            // The size is always the pointer size of the current target, but this is not information
            // that we always have readily available.
            ConstValue::Scalar(Scalar::Ptr(ptr, _size)) => {
                match self.body_visitor.context.tcx.try_get_global_alloc(ptr.provenance.alloc_id()) {
                    Some(GlobalAlloc::Memory(alloc)) => {
                        let alloc_len = alloc.inner().len() as u64;
                        let offset_bytes = ptr.into_parts().1.bytes();
                        // The Rust compiler should ensure this.
                        assert!(alloc_len > offset_bytes);
                        let size = alloc_len - offset_bytes;
                        let range = alloc_range(
                            ptr.into_parts().1,
                            rustc_target::abi::Size::from_bytes(size),
                        );
                        let bytes = if size > 0
                            && alloc.inner().provenance().range_empty(range, &self.body_visitor.context.tcx)
                        {
                            alloc
                                .inner()
                                .get_bytes_strip_provenance(&self.body_visitor.context.tcx, range)
                                .unwrap()
                        } else {
                            let mut bytes = alloc.inner().get_bytes_unchecked(range);
                            if let Some(p) = alloc.inner().provenance().provenances().next() {
                                match self.body_visitor.context.tcx.try_get_global_alloc(p.alloc_id()) {
                                    Some(GlobalAlloc::Memory(alloc)) => {
                                        let size = alloc.inner().len() as u64;
                                        let range = alloc_range(
                                            rustc_target::abi::Size::from_bytes(0),
                                            rustc_target::abi::Size::from_bytes(size),
                                        );
                                        bytes = alloc
                                            .inner()
                                            .get_bytes_strip_provenance(&self.body_visitor.context.tcx, range)
                                            .unwrap();
                                    }
                                    _ => panic!(
                                        "ConstValue::Scalar with type {:?}",
                                        lty
                                    ),
                                }
                            }
                            bytes
                        };
                        match lty.kind() {
                            TyKind::Array(elem_type, length) => {
                                let length = self.body_visitor.get_array_length(length);
                                let array_value =
                                    self.get_heap_array_and_path(lty, size as usize);
                                let array_path = Rc::new(PathEnum::HeapBlock { value: array_value.clone() }.into());
                                self.deserialize_constant_array(
                                    array_path, bytes, length, *elem_type,
                                );
                                array_value
                            }
                            TyKind::Ref(_, t, _) => match t.kind() {
                                TyKind::Array(elem_type, length) => {
                                    let length = self.body_visitor.get_array_length(length);
                                    let array_value =
                                    self.get_heap_array_and_path(lty, size as usize);
                                    let array_path: Rc<Path> = Rc::new(PathEnum::HeapBlock { value: array_value }.into());
                                    self.deserialize_constant_array(
                                        array_path.clone(),
                                        bytes,
                                        length,
                                        *elem_type,
                                    );
                                    SymbolicValue::make_reference(array_path)
                                }
                                TyKind::Adt(..) => {
                                    let heap_val = self.body_visitor.get_new_heap_block(
                                        Rc::new((bytes.len() as u128).into()),
                                        Rc::new(1u128.into()),
                                        lty,
                                    );

                                    let heap_path: Rc<Path> = Rc::new(PathEnum::HeapBlock { value: heap_val }.into());

                                    let bytes_left_to_deserialize = self
                                        .deserialize_constant_bytes(heap_path.clone(), bytes, *t);
                                    if !bytes_left_to_deserialize.is_empty() {
                                        debug!("span: {:?}", self.body_visitor.current_span);
                                        debug!("type kind {:?}", lty.kind());
                                        debug!(
                                            "constant value did not serialize correctly {:?}",
                                            val
                                        );
                                    }
                                    SymbolicValue::make_reference(heap_path)
                                }
                                _ => {
                                    panic!(
                                        "ConstValue::Ptr with type {:?} {:?}",
                                        lty,
                                        t.kind()
                                    );
                                }
                            },
                            _ => {
                                panic!("ConstValue::Scalar with type {:?}", lty);
                            }
                        }
                    }
                    Some(GlobalAlloc::Function{ instance }) => {
                        let def_id = instance.def.def_id();
                        let args = self.body_visitor.type_visitor.specialize_generic_args(
                            instance.args,
                            &self.body_visitor.type_visitor.generic_argument_map,
                        );
                        let fn_ty = self.body_visitor.context.tcx.type_of(def_id).skip_binder();
                        self.body_visitor.crate_context.generic_args_cache.insert(def_id, args);
                        let fun_val = Rc::new(
                            self.body_visitor
                                .crate_context
                                .constant_value_cache
                                .get_function_constant_for(
                                    def_id,
                                    fn_ty,
                                    Some(args),
                                    self.body_visitor.context.tcx,
                                    &mut self.body_visitor.crate_context.known_names_cache,
                                )
                                .clone()
                                .into(),
                        );
                        let heap_val = self.body_visitor.get_new_heap_block(
                            Rc::new((8u128).into()),
                            Rc::new(1u128.into()),
                            lty,
                        );
                        let heap_path: Rc<Path> = Rc::new(PathEnum::HeapBlock { value: heap_val.clone() }.into());
                        let field_0 = Path::new_field(heap_path, 0);
                        self.body_visitor
                            .state
                            .update_value_at(field_0, fun_val);
                        heap_val
                    }
                    Some(GlobalAlloc::Static(def_id)) => SymbolicValue::make_reference(
                        self.body_visitor.import_static(Path::new_static(self.body_visitor.context.tcx, def_id)),
                    ),
                    Some(GlobalAlloc::VTable(_, _)) => {
                        self.body_visitor
                            .get_new_heap_block(
                                Rc::new(0u128.into()),
                                Rc::new(8u128.into()),
                                lty,
                            )
                    }
                    None => unreachable!("missing allocation {:?}", ptr.provenance),
                }
            }

            // Only used when lty is a Zero Sized type.
            
            ConstValue::ZeroSized => Rc::new(self.get_constant_from_scalar(lty, 0, 0).into()),

            // Used only for `&[u8]` and `&str`
            ConstValue::Slice { data, meta } => {
                let size = rustc_target::abi::Size::from_bytes(meta);
                let bytes = data
                    .inner()
                    .get_bytes_strip_provenance(
                        &self.body_visitor.context.tcx,
                        alloc_range(rustc_target::abi::Size::ZERO, size),
                    )
                    .unwrap();
                let _slice = &bytes[0..];
                match lty.kind() {
                    // todo: is this case possible? The comment suggests not.
                    TyKind::Array(elem_type, length) => {
                        let length = self.body_visitor.get_array_length(length);
                        let array_value =
                        self.get_heap_array_and_path(lty, size.bytes() as usize);
                        let array_path: Rc<Path> = Rc::new(PathEnum::HeapBlock { value: array_value.clone() }.into());
                        self.deserialize_constant_array(array_path, bytes, length, *elem_type);
                        array_value
                    }
                    TyKind::Ref(_, t, _) if matches!(t.kind(), TyKind::Slice(..)) => {
                        let elem_type = get_element_type(*t);
                        let bytes_per_elem = self.body_visitor.type_visitor.get_type_size(elem_type);
                        let length = size.bytes() / bytes_per_elem;
                        let array_value = self.get_heap_array_and_path(lty, size.bytes() as usize);
                        let array_path: Rc<Path> = Rc::new(PathEnum::HeapBlock { value: array_value }.into());
                        self.deserialize_constant_array(
                            array_path.clone(),
                            bytes,
                            length as usize,
                            elem_type,
                        );
                        SymbolicValue::make_reference(array_path)
                    }
                    TyKind::Ref(_, t, _) if matches!(t.kind(), TyKind::Str) => {
                        // FIXME: This is a hack to get the string value from the slice
                        Rc::new(self.get_constant_from_scalar(lty, 0, 0).into())
                    }
                    _ => {
                        panic!("ConstValue::Slice with type {:?}", lty);
                    }
                }
            }

            // A value not represented/representable by `Scalar` or `Slice`
            ConstValue::Indirect {
                // The backing memory of the value, may contain more memory than needed for just the value
                // in order to share `ConstAllocation`s between values
                alloc_id,
                // Offset into `alloc`
                offset,
            } => {
                let alloc = self.body_visitor.context.tcx.global_alloc(alloc_id).unwrap_memory();
                let alloc_len = alloc.inner().len();
                let offset_bytes = offset.bytes() as usize;
                // The Rust compiler should ensure this.
                assert!(alloc_len > offset_bytes);
                let num_bytes = alloc_len - offset_bytes;
                let bytes = alloc
                    .inner()
                    .inspect_with_uninit_and_ptr_outside_interpreter(offset_bytes..alloc_len);
                let heap_val = self.body_visitor.get_new_heap_block(
                    Rc::new((num_bytes as u128).into()),
                    Rc::new(1u128.into()),
                    lty,
                );

                let target_path = Rc::new(PathEnum::HeapBlock { value: heap_val.clone() }.into());

                let bytes_left_to_deserialize =
                    self.deserialize_constant_bytes(target_path, bytes, lty);
                if !bytes_left_to_deserialize.is_empty() {
                    debug!("span: {:?}", self.body_visitor.current_span);
                    debug!("type kind {:?}", lty.kind());
                    debug!("constant value did not serialize correctly {:?}", val);
                }
                heap_val
            }
        }
    }

    fn visit_operand_place(&mut self, place: &mir::Place<'tcx>) -> Rc<SymbolicValue> {
        let path = self.visit_place(place);
        let rust_place_type = self
            .body_visitor
            .type_visitor
            .get_rustc_place_type(place, self.body_visitor.current_span);
        self.body_visitor
            .lookup_path_and_refine_result(path, rust_place_type)
    }

    /// Use a prefix of the byte slice as a serialized value of the given array type.
    /// Write the deserialized value to the given path in the current environment.
    /// Return the unused suffix of the byte slice as the result.
    fn deserialize_constant_array<'c>(
        &mut self,
        target_path: Rc<Path>,
        bytes: &'c [u8],
        len: usize,
        elem_ty: Ty<'tcx>,
    ) -> &'c [u8] {
        let mut bytes_left_deserialize = bytes;
        for i in 0..len {
            let elem_path =
                Path::new_index(target_path.clone(), self.body_visitor.get_u128_const_val(i as u128));
            bytes_left_deserialize =
                self.deserialize_constant_bytes(elem_path, bytes_left_deserialize, elem_ty);
        }
        let length_path = Path::new_length(target_path);
        let length_value = self.body_visitor.get_u128_const_val(len as u128);
        self.body_visitor.state.update_value_at(length_path, length_value);
        bytes_left_deserialize
    }

    /// Use a prefix of the byte slice as a serialized value of the given type.
    /// Write the deserialized value to the given path in the current environment.
    /// Return the unused suffix of the byte slice as the result.
    fn deserialize_constant_bytes<'c>(
        &mut self,
        target_path: Rc<Path>,
        bytes: &'c [u8],
        ty: Ty<'tcx>,
    ) -> &'c [u8] {
        self.body_visitor.type_visitor
            .set_path_rustc_type(target_path.clone(), ty);
        match ty.kind() {
            TyKind::Adt(def, args) if def.is_enum() => {
                trace!("deserializing {:?} {:?}", def, args);
                trace!("def.repr() {:?}", def.repr());
                let mut bytes_left_to_deserialize = bytes;
                if let Ok(enum_ty_layout) = self.body_visitor.type_visitor.layout_of(ty) {
                    trace!("enum_ty_layout {:?}", enum_ty_layout);
                    let len = enum_ty_layout.size.bytes_usize();
                    let tag_length;
                    let data = if len == 0 {
                        tag_length = 0;
                        0
                    } else if len < 2 {
                        tag_length = 1;
                        bytes[0] as u128
                    } else if len < 4 {
                        tag_length = 2;
                        u16::from_ne_bytes(*bytes.array_chunks().next().unwrap()) as u128
                    } else if len < 8 {
                        tag_length = 4;
                        u32::from_ne_bytes(*bytes.array_chunks().next().unwrap()) as u128
                    } else if len < 16 {
                        tag_length = 8;
                        u64::from_ne_bytes(*bytes.array_chunks().next().unwrap()) as u128
                    } else {
                        tag_length = 16;
                        u128::from_ne_bytes(*bytes.array_chunks().next().unwrap())
                    };
                    let (discr_signed, discr_bits, discr_index, discr_has_data) =
                        self.get_discriminator_info(data, &enum_ty_layout);
                    if !discr_has_data {
                        bytes_left_to_deserialize = &bytes[tag_length..];
                    }
                    let discr_path = Path::new_discriminant(target_path.clone());
                    let discr_data = if discr_signed {
                        self.body_visitor.get_i128_const_val(discr_bits as i128)
                    } else {
                        self.body_visitor.get_u128_const_val(discr_bits)
                    };
                    self.body_visitor.state.update_value_at(discr_path, discr_data);
                    if discr_has_data {
                        let variant = &def.variants()[discr_index];
                        trace!("deserializing variant {:?}", variant);
                        for (i, field) in variant.fields.iter().enumerate() {
                            trace!("deserializing field({}) {:?}", i, field);
                            trace!("bytes_left_deserialize {:?}", bytes_left_to_deserialize);
                            let field_path = Path::new_field(target_path.clone(), i);
                            let field_ty = field.ty(self.body_visitor.context.tcx, args);
                            trace!(
                                "field ty layout {:?}",
                                self.body_visitor.type_visitor.layout_of(field_ty)
                            );
                            bytes_left_to_deserialize = self.deserialize_constant_bytes(
                                field_path,
                                bytes_left_to_deserialize,
                                field_ty,
                            );
                        }
                    }
                }
                bytes_left_to_deserialize
            }
            TyKind::Adt(def, args) => {
                trace!("deserializing {:?} {:?}", def, args);
                let mut bytes_left_to_deserialize = bytes;
                for variant in def.variants().iter() {
                    trace!("deserializing variant {:?}", variant);
                    bytes_left_to_deserialize = bytes;
                    for (i, field) in variant.fields.iter().enumerate() {
                        trace!("deserializing field({}) {:?}", i, field);
                        trace!("bytes_left_deserialize {:?}", bytes_left_to_deserialize);
                        let field_path = Path::new_field(target_path.clone(), i);
                        let field_ty = field.ty(self.body_visitor.context.tcx, args);
                        trace!(
                            "field ty layout {:?}",
                            self.body_visitor.type_visitor.layout_of(field_ty)
                        );
                        bytes_left_to_deserialize = self.deserialize_constant_bytes(
                            field_path,
                            bytes_left_to_deserialize,
                            field_ty,
                        );
                    }
                }
                bytes_left_to_deserialize
            }
            TyKind::Array(elem_type, length) => {
                let length = self.body_visitor.get_array_length(length);
                self.deserialize_constant_array(target_path, bytes, length, *elem_type)
            }
            TyKind::Bool => {
                let val = if bytes[0] == 0 {
                    SymbolicValue::new_true()
                    // abstract_value::FALSE
                } else {                    
                    SymbolicValue::new_false()
                };
                self.body_visitor.state.update_value_at(target_path, Rc::new(val));
                &bytes[1..]
            }
            // TyKind::Char => unsafe {
            //     let ch_ptr = bytes.as_ptr() as *const char;
            //     let ch = self
            //         .body_visitor
            //         .cv
            //         .constant_value_cache
            //         .get_char_for(*ch_ptr)
            //         .clone();
            //     self.body_visitor.state.update_value_at(target_path, Rc::new(ch.into()));
            //     &bytes[4..]
            // },
            TyKind::Int(IntTy::Isize) => unsafe {
                let int_ptr = bytes.as_ptr() as *const isize;
                let i = self.body_visitor.get_i128_const_val((*int_ptr) as i128);
                self.body_visitor.state.update_value_at(target_path, i);
                let size = std::mem::size_of::<isize>();
                &bytes[size..]
            },
            TyKind::Int(IntTy::I8) => unsafe {
                let int_ptr = bytes.as_ptr() as *const i8;
                let i = self.body_visitor.get_i128_const_val((*int_ptr) as i128);
                self.body_visitor.state.update_value_at(target_path, i);
                &bytes[1..]
            },
            TyKind::Int(IntTy::I16) => unsafe {
                let int_ptr = bytes.as_ptr() as *const i16;
                let i = self.body_visitor.get_i128_const_val((*int_ptr) as i128);
                self.body_visitor.state.update_value_at(target_path, i);
                &bytes[2..]
            },
            TyKind::Int(IntTy::I32) => unsafe {
                let int_ptr = bytes.as_ptr() as *const i32;
                let i = self.body_visitor.get_i128_const_val((*int_ptr) as i128);
                self.body_visitor.state.update_value_at(target_path, i);
                &bytes[4..]
            },
            TyKind::Int(IntTy::I64) => unsafe {
                let int_ptr = bytes.as_ptr() as *const i64;
                let i = self.body_visitor.get_i128_const_val((*int_ptr) as i128);
                self.body_visitor.state.update_value_at(target_path, i);
                &bytes[8..]
            },
            TyKind::Int(IntTy::I128) => unsafe {
                let int_ptr = bytes.as_ptr() as *const i128;
                let i = self.body_visitor.get_i128_const_val(*int_ptr);
                self.body_visitor.state.update_value_at(target_path, i);
                &bytes[16..]
            },
            TyKind::Uint(UintTy::Usize) => unsafe {
                let uint_ptr = bytes.as_ptr() as *const usize;
                let u = self.body_visitor.get_u128_const_val((*uint_ptr) as u128);
                self.body_visitor.state.update_value_at(target_path, u);
                let size = std::mem::size_of::<isize>();
                &bytes[size..]
            },
            TyKind::Uint(UintTy::U8) => unsafe {
                let uint_ptr = bytes.as_ptr();
                let u = self.body_visitor.get_u128_const_val((*uint_ptr) as u128);
                self.body_visitor.state.update_value_at(target_path, u);
                &bytes[1..]
            },
            TyKind::Uint(UintTy::U16) => unsafe {
                let uint_ptr = bytes.as_ptr() as *const u16;
                let u = self.body_visitor.get_u128_const_val((*uint_ptr) as u128);
                self.body_visitor.state.update_value_at(target_path, u);
                &bytes[2..]
            },
            TyKind::Uint(UintTy::U32) => unsafe {
                let uint_ptr = bytes.as_ptr() as *const u32;
                let u = self.body_visitor.get_u128_const_val((*uint_ptr) as u128);
                self.body_visitor.state.update_value_at(target_path, u);
                &bytes[4..]
            },
            TyKind::Uint(UintTy::U64) => unsafe {
                let uint_ptr = bytes.as_ptr() as *const u64;
                let u = self.body_visitor.get_u128_const_val((*uint_ptr) as u128);
                self.body_visitor.state.update_value_at(target_path, u);
                &bytes[8..]
            },
            TyKind::Uint(UintTy::U128) => unsafe {
                let uint_ptr = bytes.as_ptr() as *const u128;
                let u = self.body_visitor.get_u128_const_val(*uint_ptr);
                self.body_visitor.state.update_value_at(target_path, u);
                &bytes[16..]
            },
            // TyKind::Float(FloatTy::F32) => unsafe {
            //     let uint_ptr = bytes.as_ptr() as *const u32;
            //     let f = self
            //         .body_visitor
            //         .cv
            //         .constant_value_cache
            //         .get_f32_for(*uint_ptr)
            //         .clone();
            //     self.body_visitor.state.update_value_at(target_path, Rc::new(f.into()));
            //     &bytes[4..]
            // },
            // TyKind::Float(FloatTy::F64) => unsafe {
            //     let uint_ptr = bytes.as_ptr() as *const u64;
            //     let f = self
            //         .body_visitor
                    
            //         .constant_value_cache
            //         .get_f64_for(*uint_ptr)
            //         .clone();
            //     self.body_visitor.state.update_value_at(target_path, Rc::new(f.into()));
            //     &bytes[8..]
            // },
            // TyKind::Ref(_, t, _) if matches!(t.kind(), TyKind::Str) => {
            //     let s = std::str::from_utf8(bytes).expect("string should be serialized as utf8");
            //     let string_const = &mut self.body_visitor.cv.constant_value_cache.get_string_for(s);
            //     let string_val: Rc<AbstractValue> = Rc::new(string_const.clone().into());
            //     let len_val: Rc<AbstractValue> =
            //         Rc::new(ConstantDomain::U128(s.len() as u128).into());

            //     let str_path = Path::new_computed(string_val.clone());
            //     self.body_visitor.state.update_value_at(str_path.clone(), string_val);

            //     let len_path = Path::new_length(str_path.clone());
            //     self.body_visitor.state.update_value_at(len_path, len_val);

            //     self.body_visitor
            //         .update_value_at(target_path, AbstractValue::make_reference(str_path));
            //     &[]
            // }
            TyKind::RawPtr(..) | TyKind::Ref(..) => {
                // serialized pointers are not the values pointed to, just some number.
                // todo: figure out how to deference that number and deserialize the
                // value to which this pointer refers.
                self.deserialize_constant_bytes(target_path, bytes, self.body_visitor.context.tcx.types.usize)
            }
            TyKind::Slice(elem_type) => {
                let elem_size = self.body_visitor.type_visitor.get_type_size(*elem_type) as usize;
                assert!(elem_size > 0); // serializing a slice of zero sized elements makes no sense
                let num_elems = bytes.len() / elem_size;
                self.deserialize_constant_array(target_path, bytes, num_elems, *elem_type)
            }
            // TyKind::Str => {
            //     let s = std::str::from_utf8(bytes).expect("string should be serialized as utf8");
            //     let string_const = &mut self.body_visitor.cv.constant_value_cache.get_string_for(s);
            //     let string_val: Rc<AbstractValue> = Rc::new(string_const.clone().into());
            //     let len_val: Rc<AbstractValue> =
            //         Rc::new(ConstantDomain::U128(s.len() as u128).into());

            //     let str_path = Path::new_computed(string_val.clone());
            //     self.body_visitor.state.update_value_at(str_path.clone(), string_val);

            //     let len_path = Path::new_length(str_path.clone());
            //     self.body_visitor.state.update_value_at(len_path, len_val);

            //     self.body_visitor
            //         .update_value_at(target_path, AbstractValue::make_reference(str_path));
            //     &[]
            // }
            TyKind::Tuple(types) => {
                let mut bytes_left_deserialize = bytes;
                for (i, field_ty) in types.iter().enumerate() {
                    let field_path = Path::new_field(target_path.clone(), i);
                    bytes_left_deserialize = self.deserialize_constant_bytes(
                        field_path,
                        bytes_left_deserialize,
                        field_ty,
                    );
                }
                bytes_left_deserialize
            }
            // todo: bytes is the serialization of the captured state of a closure/generator
            // deserialize that and return an heap block that represents the closure state + func ptr
            TyKind::Closure(def_id, args)
            | TyKind::FnDef(def_id, args)
            | TyKind::Coroutine(def_id, args, ..)
            | TyKind::Alias(
                rustc_middle::ty::Opaque,
                rustc_middle::ty::AliasTy { def_id, args, .. },
            ) => {
                let specialized_ty = self.body_visitor.type_visitor.specialize_generic_argument_type(
                    ty,
                    &self.body_visitor.type_visitor.generic_argument_map,
                );
                let specialized_args = self
                    .body_visitor.type_visitor
                    .specialize_generic_args(args, &self.body_visitor.type_visitor.generic_argument_map);
                let func_val = Rc::new(
                    self.visit_function_reference(*def_id, specialized_ty, Some(specialized_args))
                        .clone()
                        .into(),
                );
                self.body_visitor.state.update_value_at(target_path, func_val);
                &[]
            }
            _ => {
                debug!("Type {:?} is not expected to be serializable", ty.kind());
                // self.body_visitor
                //     .state
                //     .update_value_at(target_path, Rc::new(ConstantDomain::Unimplemented.into()));
                &[]
            }
        }
    }

    fn get_discriminator_info(
        &mut self,
        data: u128,
        enum_ty_layout: &rustc_middle::ty::layout::TyAndLayout<'tcx>,
    ) -> (bool, u128, VariantIdx, bool) {
        let discr_signed; // Whether the discriminant tag is signed or not
        let discr_bits; // The actual representation of the discriminant tag
        let discr_index; // The index of the discriminant in the enum definition
        let discr_has_data; // A flag indicating if the enum constant has a sub-component

        trace!("enum_ty_layout.ty {:?}", enum_ty_layout.ty);
        let discr_ty = enum_ty_layout.ty.discriminant_ty(self.body_visitor.context.tcx);
        trace!("discr_ty {:?}", discr_ty);
        let discr_ty_layout = self.body_visitor.type_visitor.layout_of(discr_ty).unwrap();
        trace!("discr_ty_layout {:?}", discr_ty_layout);
        match enum_ty_layout.variants {
            Variants::Empty => {
                discr_signed = false;
                discr_bits = 0;
                discr_index = VariantIdx::new(0);
                discr_has_data = false;
            }
            Variants::Single { index } => {
                // The enum only contains one variant.

                // Truncates the value of the discriminant to fit into the layout.
                discr_signed = discr_ty_layout.backend_repr.is_signed();
                discr_bits = match enum_ty_layout
                    .ty
                    .discriminant_for_variant(self.body_visitor.context.tcx, index)
                {
                    Some(discr) => {
                        if discr_signed {
                            discr_ty_layout.size.sign_extend(discr.val) as u128
                        } else {
                            discr_ty_layout.size.truncate(discr.val)
                        }
                    }
                    None => discr_ty_layout.size.truncate(index.as_u32() as u128),
                };
                discr_index = index;
                // A single-variant enum can have niches if and only if this variant has a sub-component
                // of some special types (such as char).
                discr_has_data = enum_ty_layout.largest_niche.is_some();
            }
            Variants::Multiple {
                ref tag,
                ref tag_encoding,
                ref variants,
                ..
            } => {
                // The enum contains multiple (more than one) variants.
                let tag_primitive = tag.primitive();
                discr_signed = matches!(tag_primitive, Primitive::Int(_, true));
                match *tag_encoding {
                    TagEncoding::Direct => {
                        discr_bits = if discr_signed {
                            tag_primitive.size(&self.body_visitor.context.tcx).sign_extend(data) as u128
                        } else {
                            data
                        };

                        // The discriminator value is not the index, so
                        // iterate through all the variant definitions to find the actual index.
                        discr_index = match enum_ty_layout.ty.kind() {
                            TyKind::Adt(adt_def, _) => adt_def
                                .discriminants(self.body_visitor.context.tcx)
                                .find(|(_, var)| var.val == data),
                            TyKind::Coroutine(def_id, args) => {
                                let generator = args.as_coroutine();
                                generator
                                    .discriminants(*def_id, self.body_visitor.context.tcx)
                                    .find(|(_, var)| var.val == data)
                            }
                            _ => panic!(),
                        }
                        .map(|i| i.0)
                        .unwrap_or_else(|| VariantIdx::new(0));

                        discr_has_data = false;
                    }
                    TagEncoding::Niche {
                        untagged_variant,
                        ref niche_variants,
                        niche_start,
                    } => {
                        // Niche (values invalid for a type) encoding the discriminant:
                        // Discriminant and variant index coincide.
                        // The variant `dataful_variant` contains a niche at an arbitrary
                        // offset (field `tag_field` of the enum), which for a variant with
                        // discriminant `d` is set to
                        // `(d - niche_variants.start).wrapping_add(niche_start)`.
                        //
                        // For example, `Option<(usize, &T)>`  is represented such that
                        // `None` has a null pointer for the second tuple field, and
                        // `Some` is the identity function (with a non-null reference).
                        trace!("untagged_variant {:?}", untagged_variant);
                        trace!("niche_start {:?}", niche_start);
                        let variants_start = niche_variants.start().as_u32();
                        let variants_end = niche_variants.end().as_u32();
                        let variant = if data >= niche_start
                            && variants_end >= variants_start
                            && (data - niche_start) <= u128::from(variants_end - variants_start)
                        {
                            trace!("data {:?}", data);
                            discr_has_data = false;
                            let variant_index_relative = (data - niche_start) as u32;
                            let variant_index = variants_start + variant_index_relative;
                            VariantIdx::from_u32(variant_index)
                        } else {
                            trace!("data {:?}", data);
                            discr_has_data = true;
                            let fields = &variants[untagged_variant].fields;
                            assert!(
                                fields.count() == 1
                                    && fields.offset(0).bytes() == 0
                                    && fields.memory_index(0) == 0,
                                "the data containing variant should contain a single sub-component"
                            );
                            untagged_variant
                        };
                        discr_bits = discr_ty_layout.size.truncate(variant.as_u32() as u128);
                        discr_index = variant;
                    }
                }
            }
        };
        (discr_signed, discr_bits, discr_index, discr_has_data)
    }


    /// Allocates a new heap block with length and alignment obtained from the given array
    /// or array slice type.
    fn get_heap_array_and_path(
        &mut self,
        array_type: Ty<'tcx>,
        size_in_bytes: usize,
    ) -> Rc<SymbolicValue> {
        let element_type = get_element_type(array_type);
        let (_, elem_alignment) = self.body_visitor.type_visitor
            .get_type_size_and_alignment(element_type);
        let alignment = self.body_visitor.get_u128_const_val(elem_alignment);
        let byte_len_value = self.body_visitor.get_u128_const_val(size_in_bytes as u128);
        self.body_visitor
            .get_new_heap_block(byte_len_value, alignment, array_type)
    }

    // TODO: this may have bugs
    /// path = &place
    fn visit_address_of(&mut self, path: Rc<Path>, place: &mir::Place<'tcx>) {
        let target_type = self
            .body_visitor
            .type_visitor
            .get_rustc_place_type(place, self.body_visitor.current_span);
        let value_path = self.visit_place(place).refine_paths(&self.state());
        debug!(
            "In handling `path = &place`, get path of place={:?}",
            value_path
        );
        // Compute the RHS value
        let value = match &value_path.value {
            // If `place` is a dereference, i.e., `path = &(*qualifier)`, this is basically `path = qualifier`
            PathEnum::QualifiedPath {
                qualifier,
                selector,
                ..
            } if *selector.as_ref() == PathSelector::Deref => {
                self.copy_or_move_elements(
                    path,
                    qualifier.refine_paths(&self.state()),
                    target_type,
                    false,
                );
                return;
            }
            // If `place` is qualified (but not a dereference)
            PathEnum::QualifiedPath { .. } => {
                SymbolicValue::make_reference(value_path.refine_paths(&self.state()))
            }
            PathEnum::PromotedConstant { .. } => {
                if let Some(val) = self.state().value_at(&value_path) {
                    if let Expression::HeapBlock { .. } = &val.expression {
                        let heap_path = Rc::new(PathEnum::HeapBlock { value: val.clone() }.into());
                        SymbolicValue::make_reference(heap_path)
                    } else {
                        SymbolicValue::make_reference(value_path)
                    }
                } else {
                    SymbolicValue::make_reference(value_path)
                }
            }
            // If `place` is a heap block, i.e., `path = &<heap>`, the RHS value is simply the heap value itself
            PathEnum::HeapBlock { value } => value.clone(),
            // For others, the RHS value is simply a symbolic value `&value_path`
            _ => SymbolicValue::make_reference(value_path),
        };
        debug!(
            "In visit_address_of, updating value at path={:?}, value={:?}",
            path, value
        );
        self.body_visitor.state.update_value_at(path, value);
    }

    fn visit_use(&mut self, path: Rc<Path>, operand: &mir::Operand<'tcx>) {
        match operand {
            mir::Operand::Copy(place) => {
                self.visit_used_copy(path, place);
            }
            mir::Operand::Move(place) => {
                self.visit_used_move(path, place);
            }
            mir::Operand::Constant(constant) => {
                let mir::ConstOperand { const_, .. } = constant.borrow();
                let rh_type = const_.ty();
                debug!(
                    "constant: {:?}, const_: {:?}, rh_type: {:?}",
                    constant, const_, rh_type
                );
                let const_value = self.visit_literal(const_);
                if const_value.expression.infer_type() == ExpressionType::NonPrimitive {
                    if let Expression::Reference(rpath) | Expression::Variable { path: rpath, .. } =
                        &const_value.expression
                    {
                        self.copy_or_move_elements(path, rpath.clone(), rh_type, false);
                        return;
                    }
                }
                match &const_value.expression {
                    Expression::HeapBlock { .. } => {
                        let rpath = Rc::new(
                            PathEnum::HeapBlock {
                                value: const_value.clone(),
                            }
                            .into(),
                        );
                        self.copy_or_move_elements(path, rpath, rh_type, false);
                    }
                    _ => {
                        let rpath = Path::new_alias(const_value.clone());
                        self.copy_or_move_elements(path, rpath, rh_type, false);
                    }
                }
            }
        };
    }

    pub fn visit_used_copy(&mut self, target_path: Rc<Path>, place: &mir::Place<'tcx>) {
        let rpath = self.visit_place(place);
        debug!("Get copy RPath={:?}", rpath);
        let rtype = self
            .body_visitor
            .type_visitor
            .get_rustc_place_type(place, self.body_visitor.current_span);
        self.copy_or_move_elements(target_path, rpath, rtype, false);
    }

    pub fn visit_used_move(&mut self, target_path: Rc<Path>, place: &mir::Place<'tcx>) {
        let rpath = self.visit_place(place);
        debug!("Get move RPath={:?}", rpath);
        let rtype = self
            .body_visitor
            .type_visitor
            .get_rustc_place_type(place, self.body_visitor.current_span);
        self.copy_or_move_elements(target_path, rpath, rtype, true);
    }

    // path = Len(place)
    #[allow(dead_code)]
    fn visit_len(&mut self, path: Rc<Path>, place: &mir::Place<'tcx>) {
        let value_path = self.visit_place(place);
        let len_value = self.get_len(value_path);
        self.body_visitor.state.update_value_at(path, len_value);
    }

    fn get_len(&mut self, path: Rc<Path>) -> Rc<SymbolicValue> {
        let length_path = Path::new_length(path).refine_paths(&self.state());
        self.body_visitor
            .lookup_path_and_refine_result(length_path, self.body_visitor.context.tcx.types.usize)
    }

    // TODO check this
    // This has a bug, when target_path=local_4, source_path=<heap0>, if copies <heap0> to local_4.[0], local_4.[1], etc.
    // Another bug, when target_path=local2, source_path=local1, if copies local1: NonPrimitive to local2.1, local2[0], local2[1], etc.
    /// Copy or move: `target_path = source_path`
    pub fn copy_or_move_elements(
        &mut self,
        target_path: Rc<Path>,
        source_path: Rc<Path>,
        target_rustc_type: Ty<'tcx>,
        is_move: bool,
    ) {
        debug!(
            "In copy or move elements, target_path={:?}, source_path={:?}",
            target_path, source_path
        );
        // First handle two special cases where LHS or RHS path contains constant indexing
        // If LHS path contains constant indexing
        if let PathEnum::QualifiedPath {
            ref qualifier,
            ref selector,
            ..
        } = &source_path.value
        {
            match **selector {
                // If index is a constant integer
                PathSelector::ConstantIndex {
                    offset, from_end, ..
                } => {
                    let index = if from_end {
                        // Compute index inversely
                        let len_value = self.get_len(qualifier.clone());
                        if let SymbolicValue {
                            expression: Expression::CompileTimeConstant(ConstantValue::Int(len)),
                            ..
                        } = len_value.as_ref()
                        {
                            len.clone() - Integer::from(offset)
                        } else {
                            unreachable!("PathSelector::ConstantIndex implies the length of the value is known");
                        }
                    } else {
                        Integer::from(offset)
                    };
                    let index_val = Rc::new(ConstantValue::Int(index).into());
                    let index_path =
                        Path::new_index(qualifier.clone(), index_val).refine_paths(&self.state());
                    self.copy_or_move_elements(target_path, index_path, target_rustc_type, is_move);
                    return;
                }
                _ => (),
            }
        };
        // Finish handling constant indexing in source_path

        // Handing constant indexing in RHS
        if let PathEnum::QualifiedPath {
            ref qualifier,
            ref selector,
            ..
        } = &target_path.value
        {
            match &**selector {
                PathSelector::Index(value) => {
                    if let Expression::CompileTimeConstant(..) = &value.expression {
                        // fall through, the target path is unique
                    } else {
                        // TODO: implement weak updates or can we use other method?
                        // and now fall through for a strong update of target_path
                    }
                }
                PathSelector::Slice(count) => {
                    // if the count is known at this point, expand it like a pattern.
                    if let Expression::CompileTimeConstant(ConstantValue::Int(val)) =
                        &count.expression
                    {
                        self.copy_or_move_subslice(
                            qualifier.clone(),
                            target_rustc_type,
                            is_move,
                            &source_path,
                            0,
                            val.to_u64().unwrap(),
                            false,
                        );
                    } else {
                        //todo: just add target_path[0..count], lookup(source_path[0..count]) to the environment
                        //When that gets refined into a constant slice, then get back here.
                        // We do, however, have to havoc all of the existing bindings, conditionally,
                        // using index < count as the condition.
                    }
                    // fall through
                }
                _ => {
                    // fall through
                }
            }
        }
        // Finish handing constant indexing in target_path

        // Get here for paths that are not patterns.
        let is_closure = matches!(&target_rustc_type.kind(), TyKind::Closure(..));
        let value = self
            .body_visitor
            .lookup_path_and_refine_result(source_path.clone(), target_rustc_type);
        let val_type = value.expression.infer_type();
        debug!(
            "After lookup_path_and_refine_result: {:?}, value type: {:?}",
            value, val_type
        );
        let mut no_children = true;
        if matches!(source_path.value, PathEnum::HeapBlock { .. }) {
            if is_move {
                debug!("moving {:?} to {:?}", value, target_path);
                // value_map.remove(&source_path);
                self.body_visitor.state.rename(&source_path, &target_path);
            } else {
                debug!("copying {:?} to {:?}", value, target_path);
                self.body_visitor
                    .state
                    .update_value_at(target_path.clone(), value);
            }
        }
        // If value type is neither an integer nor a reference, i.e., it is a NonPrimitive
        else if val_type == ExpressionType::NonPrimitive || is_closure {
            for path in self
                .state()
                .get_paths_iter()
                .iter()
                .filter(|p| p.is_rooted_by(&source_path))
            {
                let qualified_path = path.replace_root(&source_path, target_path.clone());
                if is_move {
                    debug!("Moving child {:?} to {:?}", path, qualified_path);
                    self.body_visitor.state.rename(path, &qualified_path);
                } else {
                    debug!("Copying child {:?} to {:?}", path, qualified_path);
                    self.body_visitor.state.duplicate(path, &qualified_path);
                };
                // having children means there exists a path that is rooted by source_path
                no_children = false;
            }
        }
        let target_type: ExpressionType = (target_rustc_type.kind()).into();
        // If target is not a NonPrimitive, i.e., it is a normal integer or reference
        if target_type != ExpressionType::NonPrimitive || no_children {
            let value = self
                .body_visitor
                .lookup_path_and_refine_result(source_path.clone(), target_rustc_type);
            // Just copy/move (rpath, value) itself.
            if is_move {
                debug!("moving {:?} to {:?}", value, target_path);
                // value_map.remove(&source_path);
                self.body_visitor.state.rename(&source_path, &target_path);
            } else {
                debug!("copying {:?} to {:?}", value, target_path);
                self.body_visitor.state.update_value_at(target_path, value);
            }
            return;
        }
    }

    fn copy_or_move_subslice(
        &mut self,
        target_path: Rc<Path>,
        target_type: Ty<'tcx>,
        is_move: bool,
        qualifier: &Rc<Path>,
        from: u64,
        to: u64,
        from_end: bool,
    ) {
        let to = {
            if from_end {
                let len_value = self.get_len(qualifier.clone());
                if let SymbolicValue {
                    expression: Expression::CompileTimeConstant(ConstantValue::Int(len)),
                    ..
                } = len_value.as_ref()
                {
                    u64::try_from(len).unwrap() - to
                } else {
                    debug!("PathSelector::Subslice implies the length of the value is known");
                    unreachable!();
                }
            } else {
                to
            }
        };
        let elem_size = self
            .body_visitor
            .type_visitor
            .get_elem_type_size(target_type);
        let length = self
            .body_visitor
            .get_u128_const_val(u128::from((to - from) as u64 * elem_size));
        let alignment = Rc::new(1u128.into());
        let slice_value = self
            .body_visitor
            .get_new_heap_block(length, alignment, target_type);
        self.body_visitor
            .state
            .update_value_at(target_path.clone(), slice_value.clone());
        let slice_path = Rc::new(PathEnum::HeapBlock { value: slice_value }.into());
        let slice_len_path = Path::new_length(slice_path);
        let len_value = self.body_visitor.get_u128_const_val(u128::from(to - from));
        self.body_visitor
            .state
            .update_value_at(slice_len_path, len_value);
        for i in from..to {
            let index_val = self.body_visitor.get_u128_const_val(u128::from(i));
            let index_path =
                Path::new_index(qualifier.clone(), index_val).refine_paths(&self.state());
            let target_index_val = self
                .body_visitor
                .get_u128_const_val(u128::try_from(i - from).unwrap());
            let indexed_target =
                Path::new_index(target_path.clone(), target_index_val).refine_paths(&self.state());
            self.copy_or_move_elements(indexed_target, index_path, target_type, is_move);
        }
    }

    // TODO: Check this
    pub fn transfer_and_refine(
        &mut self,
        effects: &[(Rc<Path>, Rc<SymbolicValue>)],
        target_path: Rc<Path>,
        source_path: &Rc<Path>,
        arguments: &[(Rc<Path>, Rc<SymbolicValue>)],
    ) {
        debug!("In transfer and refine, effects: {:?}, target_path: {:?}, source_path: {:?}, arguments: {:?}", effects, target_path, source_path, arguments);
        // Only do transfer and refine if effects are not empty
        for (path, value) in effects
            .iter()
            .filter(|(p, _)| (*p) == *source_path || p.is_rooted_by(source_path))
        // Only consider paths that are rooted by `source_path`
        {
            debug!("effect {:?} {:?}", path, value);
            let dummy_root = Path::new_local(999, 0);
            let refined_dummy_root = Path::new_local(999, self.body_visitor.fresh_variable_offset);
            let tpath = path
                .replace_root(source_path, dummy_root)
                .refine_parameters(arguments)
                .replace_root(&refined_dummy_root, target_path.clone())
                .refine_paths(&self.state());
            let rvalue = value
                .refine_parameters(arguments)
                .refine_paths(&self.state());
            debug!("refined effect {:?} {:?}", tpath, rvalue);
            self.body_visitor.state.remove(path);
            let rtype = rvalue.expression.infer_type();
            match &rvalue.expression {
                Expression::HeapBlock { .. } => {
                    if let PathEnum::QualifiedPath { selector, .. } = &tpath.value {
                        if let PathSelector::Slice(..) = selector.as_ref() {
                            let source_path = Path::get_as_path(rvalue.clone());
                            let target_type = type_visitor::get_element_type(
                                self.body_visitor.type_visitor.get_path_rustc_type(
                                    &target_path,
                                    self.body_visitor.current_span,
                                ),
                            );
                            self.copy_or_move_elements(
                                tpath.clone(),
                                source_path,
                                target_type,
                                false,
                            );
                            continue;
                        }
                    }
                    self.body_visitor.state.update_value_at(tpath, rvalue);
                    continue;
                }
                Expression::Variable { path, .. } => {
                    let target_type = self
                        .body_visitor
                        .type_visitor
                        .get_path_rustc_type(&tpath, self.body_visitor.current_span);
                    if let PathEnum::LocalVariable { ordinal } = &path.value {
                        if *ordinal >= self.body_visitor.fresh_variable_offset {
                            // A fresh variable from the callee adds no information that is not
                            // already inherent in the target location.
                            // TODO: Do we need to directly access the symbolic domain?
                            self.body_visitor
                                .state
                                .symbolic_domain
                                .value_map
                                .remove(&tpath);
                            continue;
                        }
                        if rtype == ExpressionType::NonPrimitive {
                            self.copy_or_move_elements(
                                tpath.clone(),
                                path.clone(),
                                target_type,
                                false,
                            );
                        }
                    } else if path.is_rooted_by_parameter() {
                        self.body_visitor.state.update_value_at(tpath, rvalue);
                        continue;
                    } else if rtype == ExpressionType::NonPrimitive {
                        self.copy_or_move_elements(tpath.clone(), path.clone(), target_type, false);
                    }
                }
                Expression::Widen { operand, .. } => {
                    let rvalue = operand.widen(&tpath);
                    self.body_visitor.state.update_value_at(tpath, rvalue);
                    continue;
                }
                _ => {}
            }
            if rtype != ExpressionType::NonPrimitive {
                self.body_visitor.state.update_value_at(tpath, rvalue);
            }
            // check_for_early_return!(self);
        }
    }

    /// Check if the given condition is reachable and true.
    /// If not issue a warning if the function is public and return the warning message, if
    /// the condition is not a post condition.
    pub fn check_condition(
        &mut self,
        cond: &Rc<SymbolicValue>,
        message: Rc<String>,
        _is_post_condition: bool,
    ) -> Option<String> {
        let cond_as_bool = self.check_condition_value(cond);

        match cond_as_bool {
            Some(true) => {
                // If the condition is always true when we get here there is nothing to report
                None
            }
            Some(false) => {
                // If the condition is always false, give an error
                let span = self.body_visitor.current_span;
                let error = self
                    .body_visitor
                    .context
                    .session
                    .dcx()
                    .struct_span_warn(span, "provably false verification condition");
                self.body_visitor
                    .emit_diagnostic(error, false, DiagnosticCause::Other);
                None
            }
            None => {
                let warning = format!("possible {}", message);
                // We might get here, or not, and the condition might be false, or not.
                // Give a warning if we don't know all of the callers, or if we run into a k-limit
                if self.function_being_analyzed_is_root() {
                    // We expect public functions to have programmer supplied preconditions
                    // that preclude any assertions from failing. So, at this stage we get to
                    // complain a bit.
                    let span = self.body_visitor.current_span;
                    let warning = self
                        .body_visitor
                        .context
                        .session
                        .dcx()
                        .struct_span_warn(span, warning.clone());
                    self.body_visitor
                        .emit_diagnostic(warning, false, DiagnosticCause::Other);
                }
                Some(warning)
            }
        }
    }

    /// Returns true if the function being analyzed is an analysis root.
    pub fn function_being_analyzed_is_root(&mut self) -> bool {
        self.body_visitor.call_stack.len() <= 1
    }

    /// Checks the given condition value and also checks if the current entry condition can be true.
    /// If the abstract domains are undecided, resort to using the SMT solver.
    /// Only call this when doing actual error checking, since this is expensive.
    pub fn check_condition_value(&mut self, cond_val: &Rc<SymbolicValue>) -> Option<bool> {
        // Check if the condition is always true (or false)
        let mut cond_as_bool = cond_val.as_bool_if_known();
        // If the condition is unknown, try SMT solver
        if cond_as_bool.is_none() {
            cond_as_bool = self.solve_condition(cond_val);
        }
        cond_as_bool
    }

    fn solve_condition(&mut self, cond_val: &Rc<SymbolicValue>) -> Option<bool> {
        let constraint_system = LinearConstraintSystem::from(&self.state().numerical_domain);

        let sat;
        let solver = &self.body_visitor.z3_solver;
        for cst in &constraint_system {
            debug!("Adding numerical constraint to SMT solver: {:?}", cst);
            solver.assert(&solver.get_as_z3_expression(cst));
        }

        let z3_cond_expr =
            solver.convert_to_bool_sort(solver.get_symbolic_as_z3_expression(cond_val));

        match solver.solve_expression(&z3_cond_expr) {
            SmtResult::Unsat => {
                // `cond_val` is always false
                sat = Some(false);
            }
            SmtResult::Sat => {
                // `cond_val` is satisfiable, now check whether `not cond_val` is always false
                // cst = cst.negate();
                let cst = solver.make_not_z3_expression(z3_cond_expr);
                if solver.solve_expression(&cst) == SmtResult::Unsat {
                    // `not cond_val` is always false, so `cond_val` is always true
                    sat = Some(true);
                } else {
                    sat = None
                }
            }
            SmtResult::Unknown => {
                sat = None;
            }
        }
        solver.reset();

        sat
    }
}
