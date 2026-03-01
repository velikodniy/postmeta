//! Shared expression payload for interpreter and capsule tokens.

use crate::equation::{DepList, VarId, const_dep, single_dep};
use crate::types::{Type, Value};

/// Expression value with type and dependency metadata.
#[derive(Debug, Clone)]
pub struct ExprValue {
    pub exp: Value,
    pub ty: Type,
    pub dep: Option<DepList>,
    pub pair_dep: Option<(DepList, DepList)>,
}

impl ExprValue {
    #[must_use]
    pub const fn vacuous() -> Self {
        Self {
            exp: Value::Vacuous,
            ty: Type::Vacuous,
            dep: None,
            pair_dep: None,
        }
    }

    #[must_use]
    pub const fn typed(exp: Value, ty: Type) -> Self {
        Self {
            ty,
            exp,
            dep: None,
            pair_dep: None,
        }
    }

    #[must_use]
    pub const fn plain(exp: Value) -> Self {
        let ty = exp.ty();
        Self::typed(exp, ty)
    }

    #[must_use]
    pub fn numeric_known(v: f64) -> Self {
        Self {
            exp: Value::Numeric(v),
            ty: Type::Known,
            dep: Some(const_dep(v)),
            pair_dep: None,
        }
    }

    #[must_use]
    pub fn numeric_independent(id: VarId) -> Self {
        Self {
            exp: Value::Numeric(0.0),
            ty: Type::Independent,
            dep: Some(single_dep(id)),
            pair_dep: None,
        }
    }

    #[must_use]
    pub fn numeric_dependent(dep: DepList) -> Self {
        Self {
            exp: Value::Numeric(crate::equation::constant_value(&dep).unwrap_or(0.0)),
            ty: Type::Dependent,
            dep: Some(dep),
            pair_dep: None,
        }
    }
}
