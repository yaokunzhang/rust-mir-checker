use rustc_errors::Diag;
use rustc_hir::def_id::DefId;
use rustc_middle::mir;
use std::cmp::Ordering;
use std::collections::HashMap;

/// Define the cause of a diagnostic message
/// Used to provide user options to suppress some specific kinds of warnings
/// So that we can decrease the false-positive rate
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum DiagnosticCause {
    Bitwise,    // Bit-wise overflow
    Arithmetic, // Arithmetic overflow
    Assembly,   // Inline assembly
    Comparison, // Comparison operations
    DivZero,    // Division by zero / remainder by zero
    Memory,     // Memory-safety issues
    Panic,      // Run into panic code
    Index,      // Out-of-bounds access
    Other,      // Other
}

/// Extract the cause of a diagnostic message from an assertion statement
impl<O> From<&mir::AssertKind<O>> for DiagnosticCause {
    fn from(assert_kind: &mir::AssertKind<O>) -> DiagnosticCause {
        use mir::BinOp::*;
        match assert_kind {
            mir::AssertKind::BoundsCheck { .. } => DiagnosticCause::Index,
            mir::AssertKind::Overflow(bin_op, ..) => match bin_op {
                Add | Sub | Mul | Div | Rem | AddUnchecked | SubUnchecked | MulUnchecked
                | AddWithOverflow | SubWithOverflow | MulWithOverflow => DiagnosticCause::Arithmetic,
                Shr | Shl | BitXor | BitAnd | BitOr | ShlUnchecked | ShrUnchecked => DiagnosticCause::Bitwise,
                Eq | Lt | Le | Ne | Ge | Gt | Cmp=> DiagnosticCause::Comparison,
                Offset => DiagnosticCause::Index,
            },
            mir::AssertKind::OverflowNeg(..) => DiagnosticCause::Arithmetic,
            mir::AssertKind::DivisionByZero(..) | mir::AssertKind::RemainderByZero(..) => {
                DiagnosticCause::DivZero
            }
            _ => DiagnosticCause::Other,
        }
    }
}

/// A diagnosis, which consists of the `Diag` and more information about it
// #[derive(Clone)]
pub struct Diagnostic<'compiler> {
    pub builder: Diag<'compiler, ()>,
    pub is_memory_safety: bool,
    pub cause: DiagnosticCause,
}

impl<'compiler> Diagnostic<'compiler> {
    pub fn new(
        builder: Diag<'compiler, ()>,
        is_memory_safety: bool,
        cause: DiagnosticCause,
    ) -> Self {
        Self {
            builder,
            is_memory_safety,
            cause,
        }
    }

    pub fn cancel(self) {
        self.builder.cancel();
    }

    pub fn emit(self) {
        self.builder.emit();
    }

    pub fn compare(x: & Diagnostic<'compiler>, y: & Diagnostic<'compiler>) -> Ordering {
        if x.builder
            .span
            .primary_spans()
            .lt(&y.builder.span.primary_spans())
        {
            Ordering::Less
        } else if x
            .builder
            .span
            .primary_spans()
            .gt(&y.builder.span.primary_spans())
        {
            Ordering::Greater
        } else {
            Ordering::Equal
        }
    }
}

/// Store all the diagnoses generated for each `DefId`
pub struct DiagnosticsForDefId<'compiler> {
    pub map: HashMap<DefId, Vec<Option<Diagnostic<'compiler>>>>,
}

impl<'compiler> Default for DiagnosticsForDefId<'compiler> {
    fn default() -> Self {
        Self {
            map: HashMap::new(),
        }
    }
}

impl<'compiler> DiagnosticsForDefId<'compiler> {
    pub fn insert(&mut self, id: DefId, diags: Vec<Option<Diagnostic<'compiler>>>) {
        self.map.insert(id, diags);
    }
}
