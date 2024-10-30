use crate::analysis::abstract_domain::{self, AbstractDomain};
use crate::analysis::diagnostics::DiagnosticCause;
use crate::analysis::memory::constant_value::ConstantValue;
use crate::analysis::memory::expression::{Expression, ExpressionType};
use crate::analysis::memory::path::{Path, PathEnum, PathSelector};
use crate::analysis::memory::symbolic_value::SymbolicValue;
use crate::analysis::mir_visitor::block_visitor::BlockVisitor;
use crate::analysis::mir_visitor::body_visitor::WtoFixPointIterator;
use crate::analysis::numerical::apron_domain::{
    ApronAbstractDomain, ApronDomainType, GetManagerTrait,
};
use crate::analysis::numerical::linear_constraint::{
    LinearConstraint, LinearConstraintSystem, LinearExpression,
};
use crate::analysis::z3_solver::SmtResult;
use crate::analysis::z3_solver::Z3Solver;
use crate::checker::checker_trait::CheckerTrait;
use itertools::Itertools;
use log::debug;
use rug::Integer;
use rustc_middle::mir;
use rustc_middle::mir::{Terminator, TerminatorKind};
use rustc_middle::ty::Ty;
use rustc_span::Span;
use std::cmp::PartialEq;
use std::convert::From;
use std::option::Option::{self, None};
use std::rc::Rc;
use std::{fmt, format, path, print, usize};

pub struct UnsafeFuncChecker<'tcx, 'a, 'b, 'compiler, DomainType>
where
    DomainType: ApronDomainType,
    ApronAbstractDomain<DomainType>: GetManagerTrait,
{
    body_visitor: &'b mut WtoFixPointIterator<'tcx, 'a, 'compiler, DomainType>,
}

impl<'tcx, 'a, 'b, 'compiler, DomainType> CheckerTrait<'tcx, 'a, 'b, 'compiler, DomainType>
    for UnsafeFuncChecker<'tcx, 'a, 'b, 'compiler, DomainType>
where
    DomainType: ApronDomainType,
    ApronAbstractDomain<DomainType>: GetManagerTrait,
{
    fn new(body_visitor: &'b mut WtoFixPointIterator<'tcx, 'a, 'compiler, DomainType>) -> Self {
        Self { body_visitor }
    }

    fn run(&mut self) {
        info!("====== UnsafeFunc Checker starts ======");
        let basic_blocks = self.body_visitor.wto.basic_blocks().clone();
        for (bb, bb_data) in basic_blocks.iter_enumerated() {
            let term = bb_data.terminator();
            let post = self.body_visitor.post.clone();
            if let Some(s) = post.get(&bb) {
                self.run_terminator(term, s);
            }
        }
        info!("====== UnsafeFunc Checker ends ======");
    }
}

pub enum CheckerResult {
    Safe,    // Proved to be safe
    Unsafe,  // Proved to be unsafe
    Warning, // Do not know whether safe or not
}

pub enum UnsafeFuncType {
    Offset,
}

impl<'tcx, 'a, 'b, 'compiler, DomainType> UnsafeFuncChecker<'tcx, 'a, 'b, 'compiler, DomainType>
where
    DomainType: ApronDomainType,
    ApronAbstractDomain<DomainType>: GetManagerTrait,
{
    fn get_unsafe_func(&self, func_str: String) -> Option<UnsafeFuncType> {
        if func_str.starts_with("std::ptr::mut_ptr::") && func_str.ends_with("::offset") {
            return Some(UnsafeFuncType::Offset);
        }
        None
    }

    fn run_terminator(
        &mut self,
        term: &Terminator<'tcx>,
        abstract_value: &AbstractDomain<DomainType>,
    ) {
        let Terminator { source_info, kind } = term;
        let span = source_info.span;
        if let TerminatorKind::Call { func, args, .. } = &kind {
            // 检测是否为offset函数，
            debug!("current func is {:?} and span is {:?}", func, span,);
            // TODO:额外的匹配单元
            let func_str = format!("{:?}", func);
            let mut check_result = CheckerResult::Safe;

            if let Some(unsafe_func_type) = self.get_unsafe_func(func_str) {
                check_result = match unsafe_func_type {
                    UnsafeFuncType::Offset => {
                        self.str_ptr_mut_ptr_offset_handler(args, &span, abstract_value)
                    }
                }
            }

            match check_result {
                CheckerResult::Safe => (),
                CheckerResult::Unsafe => {
                    let error = self.body_visitor.context.session.dcx().struct_span_warn(
                        span,
                        format!("[MirChecker] Provably error: buffer overflow",).as_str(),
                    );
                    self.body_visitor.emit_diagnostic(
                        error,
                        true,
                        DiagnosticCause::from(DiagnosticCause::Memory),
                    );
                }
                CheckerResult::Warning => {
                    let warning = self.body_visitor.context.session.dcx().struct_span_warn(
                        span,
                        format!("[MirChecker] Possible error: buffer overflow",).as_str(),
                    );
                    self.body_visitor.emit_diagnostic(
                        warning,
                        true,
                        DiagnosticCause::from(DiagnosticCause::Memory),
                    );
                }
            }
        }
    }

    fn str_ptr_mut_ptr_offset_handler(
        &mut self,
        args: &Vec<mir::Operand<'tcx>>,
        span: &Span,
        abstract_value: &AbstractDomain<DomainType>,
    ) -> CheckerResult {
        assert!(
            args.len() == 2,
            "Expected exactly one argument, but got {}",
            args.len()
        );
        if let Some(path_vec) = self.body_visitor.terminator_to_place.get(&span) {
            debug!("path_vec is {:?}", path_vec);
            let array_path = self.refine_arg_path(&path_vec[0]);
            let offset_path = self.refine_arg_path(&path_vec[1]);

            let array_len_path: Rc<Path> = Path::new_field(array_path.clone(), 1);

            return self.check_less(array_len_path, offset_path, abstract_value);
        }
        CheckerResult::Safe
    }

    fn refine_arg_path(&self, path_and_value: &(Rc<Path>, Rc<SymbolicValue>)) -> Rc<Path> {
        match &path_and_value.1.expression {
            Expression::CompileTimeConstant(ConstantValue::Int(_constant)) => {
                path_and_value.0.clone()
            }
            Expression::Reference(old_path) => old_path.clone(),
            _ => {
                debug!(
                    "Unexpected Expression Type occures! It's {:?}",
                    path_and_value.1.expression,
                );
                path_and_value.0.clone()
            }
        }
    }

    // 输入为两个符号值,如 lhs: &local_1, rhs: 5,检查path1 < path2是不是成立
    //
    fn check_less(
        &self,
        lhs: Rc<Path>,
        rhs: Rc<Path>,
        abstract_value: &AbstractDomain<DomainType>,
    ) -> CheckerResult {
        debug!(
            "lhs in env is {:?}, rhs in env is {:?}",
            abstract_value.value_at(&lhs),
            abstract_value.value_at(&rhs),
        );
        if let (Some(lhs_value), Some(rhs_value)) =
            (abstract_value.value_at(&lhs), abstract_value.value_at(&rhs))
        {
            if lhs_value <= rhs_value {
                return CheckerResult::Unsafe;
            } else {
                return CheckerResult::Safe;
            }
        }
        return CheckerResult::Safe;
    }

    #[allow(unused)]
    fn check_within_range(&self) -> CheckerResult {
        CheckerResult::Safe
    }
}
