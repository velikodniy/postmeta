//! Linear equation solver for `MetaPost`'s declarative equation system.
//!
//! `MetaPost`'s key feature is that you can write `x + y = 5; x - y = 1;`
//! and the system solves for `x = 3, y = 2`. This module implements the
//! dependency-list-based equation solver from `mp.web` §24.
//!
//! # Value lifecycle
//!
//! Numeric variables progress through states:
//! `Undefined → Numeric → Independent → Dependent → Known`
//!
//! An **independent** variable has a serial number and no constraints yet.
//! A **dependent** variable is a linear combination of independents:
//! `α₁v₁ + α₂v₂ + ... + αₖvₖ + β`
//!
//! When an equation fully constrains a variable, it becomes **known**.
//!
//! # Data structures
//!
//! A dependency list is a `Vec<DepTerm>` where each term has a coefficient
//! and a reference to an independent variable. The last term has
//! `var_id = None` and holds the constant.

use postmeta_graphics::types::Scalar;

// ---------------------------------------------------------------------------
// Variable identifier for the equation system
// ---------------------------------------------------------------------------

/// Identifies a numeric variable in the equation system.
///
/// This is an opaque handle into the variable storage. The equation solver
/// uses these to track which variables are independent, dependent, or known.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct VarId(pub u32);

// ---------------------------------------------------------------------------
// Dependency terms
// ---------------------------------------------------------------------------

/// One term in a dependency list: `coefficient * variable`.
///
/// A term with `var_id = None` is the constant term and must be last.
#[derive(Debug, Clone)]
pub struct DepTerm {
    /// The coefficient (fraction or scaled depending on dep type).
    pub coeff: Scalar,
    /// The independent variable, or `None` for the constant term.
    pub var_id: Option<VarId>,
}

/// A dependency list: a linear combination of independent variables.
///
/// Stored as a vector of terms sorted by decreasing serial number of
/// the independent variable, with the constant term last.
pub type DepList = Vec<DepTerm>;

/// Create a dependency list for a single known constant.
#[must_use]
pub fn const_dep(value: Scalar) -> DepList {
    vec![DepTerm {
        coeff: value,
        var_id: None,
    }]
}

/// Create a dependency list for a single independent variable with
/// coefficient 1.
#[must_use]
pub fn single_dep(var_id: VarId) -> DepList {
    vec![
        DepTerm {
            coeff: 1.0,
            var_id: Some(var_id),
        },
        DepTerm {
            coeff: 0.0,
            var_id: None,
        },
    ]
}

/// Check if a dependency list has reduced to just a constant.
#[must_use]
pub fn is_constant(dep: &DepList) -> bool {
    dep.len() == 1 && dep[0].var_id.is_none()
}

/// Get the constant value from a constant dependency list.
///
/// Returns `None` if the list has non-constant terms.
#[must_use]
pub fn constant_value(dep: &DepList) -> Option<Scalar> {
    if is_constant(dep) {
        Some(dep[0].coeff)
    } else {
        None
    }
}

/// Negate all terms in a dependency list.
pub fn negate(dep: &mut DepList) {
    for term in dep {
        term.coeff = -term.coeff;
    }
}

// ---------------------------------------------------------------------------
// Dependency arithmetic
// ---------------------------------------------------------------------------

/// Threshold below which a coefficient is treated as zero.
const COEFF_THRESHOLD: Scalar = 1e-9;

/// Add two dependency lists: `result = a + b`.
///
/// Both lists must be sorted by decreasing serial number.
/// The result is also sorted and cleaned of near-zero coefficients.
#[must_use]
pub fn dep_add(a: &DepList, b: &DepList) -> DepList {
    dep_add_scaled(a, b, 1.0)
}

/// Compute `a + f * b` (add `b` scaled by `f` to `a`).
///
/// Both lists must be sorted by decreasing serial number.
#[must_use]
pub fn dep_add_scaled(a: &DepList, b: &DepList, f: Scalar) -> DepList {
    let mut result = Vec::with_capacity(a.len() + b.len());
    let mut ai = 0;
    let mut bi = 0;

    // Merge-sort style addition of two sorted lists
    while ai < a.len() && bi < b.len() {
        match (a[ai].var_id, b[bi].var_id) {
            (None, _) => {
                // a's constant term — b might still have variable terms
                // Add remaining b terms first
                while bi < b.len() && b[bi].var_id.is_some() {
                    let c = f * b[bi].coeff;
                    if c.abs() > COEFF_THRESHOLD {
                        result.push(DepTerm {
                            coeff: c,
                            var_id: b[bi].var_id,
                        });
                    }
                    bi += 1;
                }
                // Now add the constant terms
                let c = if bi < b.len() {
                    f.mul_add(b[bi].coeff, a[ai].coeff)
                } else {
                    a[ai].coeff
                };
                result.push(DepTerm {
                    coeff: c,
                    var_id: None,
                });
                return result;
            }
            (_, None) => {
                // b's constant — a still has variable terms
                let c = a[ai].coeff;
                if c.abs() > COEFF_THRESHOLD {
                    result.push(DepTerm {
                        coeff: c,
                        var_id: a[ai].var_id,
                    });
                }
                ai += 1;
            }
            (Some(va), Some(vb)) => match va.0.cmp(&vb.0) {
                std::cmp::Ordering::Greater => {
                    // a's variable comes first (higher serial)
                    let c = a[ai].coeff;
                    if c.abs() > COEFF_THRESHOLD {
                        result.push(DepTerm {
                            coeff: c,
                            var_id: Some(va),
                        });
                    }
                    ai += 1;
                }
                std::cmp::Ordering::Less => {
                    // b's variable comes first
                    let c = f * b[bi].coeff;
                    if c.abs() > COEFF_THRESHOLD {
                        result.push(DepTerm {
                            coeff: c,
                            var_id: Some(vb),
                        });
                    }
                    bi += 1;
                }
                std::cmp::Ordering::Equal => {
                    // Same variable — add coefficients
                    let c = f.mul_add(b[bi].coeff, a[ai].coeff);
                    if c.abs() > COEFF_THRESHOLD {
                        result.push(DepTerm {
                            coeff: c,
                            var_id: Some(va),
                        });
                    }
                    ai += 1;
                    bi += 1;
                }
            },
        }
    }

    drain_remaining(&mut result, a, ai, b, bi, f);
    ensure_constant_term(&mut result);
    result
}

/// Drain remaining terms from both input lists into the result.
fn drain_remaining(
    result: &mut DepList,
    a: &DepList,
    mut ai: usize,
    b: &DepList,
    mut bi: usize,
    f: Scalar,
) {
    while ai < a.len() {
        let c = a[ai].coeff;
        if a[ai].var_id.is_some() && c.abs() <= COEFF_THRESHOLD {
            ai += 1;
            continue;
        }
        result.push(a[ai].clone());
        ai += 1;
    }
    while bi < b.len() {
        if b[bi].var_id.is_some() {
            let c = f * b[bi].coeff;
            if c.abs() > COEFF_THRESHOLD {
                result.push(DepTerm {
                    coeff: c,
                    var_id: b[bi].var_id,
                });
            }
        } else {
            result.push(DepTerm {
                coeff: f * b[bi].coeff,
                var_id: None,
            });
        }
        bi += 1;
    }
}

/// Ensure the dependency list ends with a constant term.
fn ensure_constant_term(result: &mut DepList) {
    if result.is_empty() || result.last().is_some_and(|t| t.var_id.is_some()) {
        result.push(DepTerm {
            coeff: 0.0,
            var_id: None,
        });
    }
}

/// Multiply all terms by a scalar constant.
pub fn dep_scale(dep: &mut DepList, factor: Scalar) {
    for term in dep {
        term.coeff *= factor;
    }
}

/// Substitute `var_id = replacement` into a dependency list.
///
/// If `dep` contains a term `c * var_id`, that term is replaced by
/// `c * replacement`. The result is re-sorted and cleaned.
#[must_use]
pub fn dep_substitute(dep: &DepList, var_id: VarId, replacement: &DepList) -> DepList {
    // Find the coefficient of var_id in dep
    let mut coeff = 0.0;
    let mut rest = Vec::with_capacity(dep.len());

    for term in dep {
        if term.var_id == Some(var_id) {
            coeff = term.coeff;
        } else {
            rest.push(term.clone());
        }
    }

    if coeff.abs() <= COEFF_THRESHOLD {
        // Variable not in this dep list
        return dep.clone();
    }

    // Ensure rest has a constant term
    if rest.is_empty() || rest.last().is_some_and(|t| t.var_id.is_some()) {
        rest.push(DepTerm {
            coeff: 0.0,
            var_id: None,
        });
    }

    dep_add_scaled(&rest, replacement, coeff)
}

// ---------------------------------------------------------------------------
// Equation solver
// ---------------------------------------------------------------------------

/// Result of solving a linear equation.
#[derive(Debug)]
pub enum SolveResult {
    /// A variable became known with the given value.
    Solved {
        /// The variable that was determined.
        var_id: VarId,
        /// Its dependency list (may be constant or still dependent).
        dep: DepList,
    },
    /// The equation was redundant (e.g. `0 = 0`).
    Redundant,
    /// The equation was inconsistent (e.g. `0 = 5`).
    Inconsistent(Scalar),
}

/// Solve a linear equation expressed as "dep = 0".
///
/// Finds the term with the largest absolute coefficient, pivots on it
/// (making that variable dependent on the others), and returns the
/// result. The caller is responsible for substituting into all other
/// dependency lists.
///
/// This is the core of `mp.web`'s `linear_eq` procedure.
#[must_use]
pub fn solve_equation(dep: &DepList) -> SolveResult {
    // If dep is just a constant, it's redundant or inconsistent
    if is_constant(dep) {
        let c = dep[0].coeff;
        if c.abs() > COEFF_THRESHOLD * 64.0 {
            return SolveResult::Inconsistent(c);
        }
        return SolveResult::Redundant;
    }

    // Find the term with the largest absolute coefficient
    let (pivot_idx, _) = dep
        .iter()
        .enumerate()
        .filter(|(_, t)| t.var_id.is_some())
        .max_by(|(_, a), (_, b)| {
            a.coeff
                .abs()
                .partial_cmp(&b.coeff.abs())
                .unwrap_or(std::cmp::Ordering::Equal)
        })
        .unwrap_or((0, &dep[0])); // safe: we checked non-constant above

    let pivot_var = dep[pivot_idx].var_id;
    let pivot_coeff = dep[pivot_idx].coeff;

    // Build the result: pivot_var = -(remaining terms) / pivot_coeff
    let mut result = Vec::with_capacity(dep.len() - 1);
    for (i, term) in dep.iter().enumerate() {
        if i == pivot_idx {
            continue;
        }
        result.push(DepTerm {
            coeff: -term.coeff / pivot_coeff,
            var_id: term.var_id,
        });
    }

    // Ensure constant term is last
    if result.is_empty() || result.last().is_some_and(|t| t.var_id.is_some()) {
        result.push(DepTerm {
            coeff: 0.0,
            var_id: None,
        });
    }

    SolveResult::Solved {
        var_id: pivot_var.unwrap_or(VarId(0)),
        dep: result,
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn const_dep_is_constant() {
        let d = const_dep(42.0);
        assert!(is_constant(&d));
        assert!((constant_value(&d).unwrap() - 42.0).abs() < f64::EPSILON);
    }

    #[test]
    fn single_dep_not_constant() {
        let d = single_dep(VarId(1));
        assert!(!is_constant(&d));
        assert!(constant_value(&d).is_none());
    }

    #[test]
    fn negate_dep() {
        let mut d = vec![
            DepTerm {
                coeff: 3.0,
                var_id: Some(VarId(1)),
            },
            DepTerm {
                coeff: 5.0,
                var_id: None,
            },
        ];
        negate(&mut d);
        assert!((d[0].coeff - (-3.0)).abs() < f64::EPSILON);
        assert!((d[1].coeff - (-5.0)).abs() < f64::EPSILON);
    }

    #[test]
    fn add_two_deps() {
        // a = 2*v1 + 3
        let a = vec![
            DepTerm {
                coeff: 2.0,
                var_id: Some(VarId(1)),
            },
            DepTerm {
                coeff: 3.0,
                var_id: None,
            },
        ];
        // b = 4*v1 + 1
        let b = vec![
            DepTerm {
                coeff: 4.0,
                var_id: Some(VarId(1)),
            },
            DepTerm {
                coeff: 1.0,
                var_id: None,
            },
        ];
        let result = dep_add(&a, &b);
        // Should be 6*v1 + 4
        assert_eq!(result.len(), 2);
        assert_eq!(result[0].var_id, Some(VarId(1)));
        assert!((result[0].coeff - 6.0).abs() < f64::EPSILON);
        assert!((result[1].coeff - 4.0).abs() < f64::EPSILON);
    }

    #[test]
    fn add_different_vars() {
        // a = 2*v2 + 1
        let a = vec![
            DepTerm {
                coeff: 2.0,
                var_id: Some(VarId(2)),
            },
            DepTerm {
                coeff: 1.0,
                var_id: None,
            },
        ];
        // b = 3*v1 + 2
        let b = vec![
            DepTerm {
                coeff: 3.0,
                var_id: Some(VarId(1)),
            },
            DepTerm {
                coeff: 2.0,
                var_id: None,
            },
        ];
        let result = dep_add(&a, &b);
        // Should be 2*v2 + 3*v1 + 3
        assert_eq!(result.len(), 3);
        assert_eq!(result[0].var_id, Some(VarId(2)));
        assert!((result[0].coeff - 2.0).abs() < f64::EPSILON);
        assert_eq!(result[1].var_id, Some(VarId(1)));
        assert!((result[1].coeff - 3.0).abs() < f64::EPSILON);
        assert!((result[2].coeff - 3.0).abs() < f64::EPSILON);
    }

    #[test]
    fn cancel_terms() {
        // a = 5*v1 + 1
        let a = vec![
            DepTerm {
                coeff: 5.0,
                var_id: Some(VarId(1)),
            },
            DepTerm {
                coeff: 1.0,
                var_id: None,
            },
        ];
        // b = -5*v1 + 2
        let b = vec![
            DepTerm {
                coeff: -5.0,
                var_id: Some(VarId(1)),
            },
            DepTerm {
                coeff: 2.0,
                var_id: None,
            },
        ];
        let result = dep_add(&a, &b);
        // Should be just 3 (constant)
        assert!(is_constant(&result));
        assert!((result[0].coeff - 3.0).abs() < f64::EPSILON);
    }

    #[test]
    fn substitute_into_dep() {
        // dep = 3*v1 + 2*v2 + 5
        let dep = vec![
            DepTerm {
                coeff: 3.0,
                var_id: Some(VarId(2)),
            },
            DepTerm {
                coeff: 2.0,
                var_id: Some(VarId(1)),
            },
            DepTerm {
                coeff: 5.0,
                var_id: None,
            },
        ];
        // v1 = 4*v3 + 7
        let replacement = vec![
            DepTerm {
                coeff: 4.0,
                var_id: Some(VarId(3)),
            },
            DepTerm {
                coeff: 7.0,
                var_id: None,
            },
        ];
        let result = dep_substitute(&dep, VarId(1), &replacement);
        // Should be 3*v2 + 8*v3 + 19
        // (5 + 2*7 = 19; 2*4 = 8; 3*v2 unchanged)
        assert_eq!(result.len(), 3);

        // Find each term
        let v2_coeff = result
            .iter()
            .find(|t| t.var_id == Some(VarId(2)))
            .unwrap()
            .coeff;
        let v3_coeff = result
            .iter()
            .find(|t| t.var_id == Some(VarId(3)))
            .unwrap()
            .coeff;
        let constant = result.iter().find(|t| t.var_id.is_none()).unwrap().coeff;

        assert!((v2_coeff - 3.0).abs() < f64::EPSILON);
        assert!((v3_coeff - 8.0).abs() < f64::EPSILON);
        assert!((constant - 19.0).abs() < f64::EPSILON);
    }

    #[test]
    fn solve_x_plus_y_eq_5() {
        // Equation: x + y - 5 = 0
        // where x = VarId(1), y = VarId(2)
        let dep = vec![
            DepTerm {
                coeff: 1.0,
                var_id: Some(VarId(2)),
            },
            DepTerm {
                coeff: 1.0,
                var_id: Some(VarId(1)),
            },
            DepTerm {
                coeff: -5.0,
                var_id: None,
            },
        ];
        match solve_equation(&dep) {
            SolveResult::Solved { var_id, dep } => {
                // One variable should be expressed in terms of the other
                // e.g. v2 = -v1 + 5 (or v1 = -v2 + 5)
                assert!(var_id == VarId(1) || var_id == VarId(2));
                assert!(!is_constant(&dep));
            }
            _ => panic!("expected Solved"),
        }
    }

    #[test]
    fn solve_x_eq_3() {
        // Equation: x - 3 = 0
        let dep = vec![
            DepTerm {
                coeff: 1.0,
                var_id: Some(VarId(1)),
            },
            DepTerm {
                coeff: -3.0,
                var_id: None,
            },
        ];
        match solve_equation(&dep) {
            SolveResult::Solved { var_id, dep } => {
                assert_eq!(var_id, VarId(1));
                assert!(is_constant(&dep));
                assert!((constant_value(&dep).unwrap() - 3.0).abs() < f64::EPSILON);
            }
            _ => panic!("expected Solved"),
        }
    }

    #[test]
    fn solve_inconsistent() {
        // Equation: 5 = 0 (no variables)
        let dep = const_dep(5.0);
        match solve_equation(&dep) {
            SolveResult::Inconsistent(v) => {
                assert!((v - 5.0).abs() < f64::EPSILON);
            }
            _ => panic!("expected Inconsistent"),
        }
    }

    #[test]
    fn solve_redundant() {
        // Equation: 0 = 0
        let dep = const_dep(0.0);
        assert!(matches!(solve_equation(&dep), SolveResult::Redundant));
    }

    #[test]
    fn solve_two_equations() {
        // System: x + y = 5, x - y = 1
        // First equation: x + y - 5 = 0
        let eq1 = vec![
            DepTerm {
                coeff: 1.0,
                var_id: Some(VarId(2)),
            },
            DepTerm {
                coeff: 1.0,
                var_id: Some(VarId(1)),
            },
            DepTerm {
                coeff: -5.0,
                var_id: None,
            },
        ];

        let result1 = solve_equation(&eq1);
        let (pivot1, dep1) = match result1 {
            SolveResult::Solved { var_id, dep } => (var_id, dep),
            _ => panic!("expected Solved"),
        };

        // Second equation: x - y - 1 = 0
        let eq2 = vec![
            DepTerm {
                coeff: -1.0,
                var_id: Some(VarId(2)),
            },
            DepTerm {
                coeff: 1.0,
                var_id: Some(VarId(1)),
            },
            DepTerm {
                coeff: -1.0,
                var_id: None,
            },
        ];

        // Substitute the first result into the second equation
        let eq2_subst = dep_substitute(&eq2, pivot1, &dep1);

        let result2 = solve_equation(&eq2_subst);
        let (pivot2, dep2) = match result2 {
            SolveResult::Solved { var_id, dep } => (var_id, dep),
            _ => panic!("expected Solved for eq2"),
        };

        // One should solve to a constant
        assert!(is_constant(&dep2), "second solve should be constant");

        // Now substitute back to find the first variable
        let dep1_final = dep_substitute(&dep1, pivot2, &dep2);
        assert!(
            is_constant(&dep1_final),
            "first should be constant after backsubst"
        );

        // Check values: x = 3, y = 2
        let val1 = constant_value(&dep1_final).unwrap();
        let val2 = constant_value(&dep2).unwrap();

        let (x, y) = if pivot1 == VarId(1) {
            (val1, val2)
        } else {
            (val2, val1)
        };

        assert!((x - 3.0).abs() < 1e-6, "x = {x}, expected 3");
        assert!((y - 2.0).abs() < 1e-6, "y = {y}, expected 2");
    }
}
