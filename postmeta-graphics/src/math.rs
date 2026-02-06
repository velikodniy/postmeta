//! `MetaPost` mathematical primitives.
//!
//! These correspond to the built-in numeric operators in the `MetaPost` engine:
//! `sind`, `cosd`, `sqrt`, `mexp`, `mlog`, `angle`, `floor`,
//! `uniformdeviate`, `normaldeviate`, Pythagorean addition (`++`)
//! and subtraction (`+-+`).

use crate::types::Scalar;

/// Sine of an angle in degrees.
#[inline]
pub fn sind(degrees: Scalar) -> Scalar {
    degrees.to_radians().sin()
}

/// Cosine of an angle in degrees.
#[inline]
pub fn cosd(degrees: Scalar) -> Scalar {
    degrees.to_radians().cos()
}

/// Angle of the vector (x, y) in degrees, in the range (-180, 180].
///
/// This corresponds to `MetaPost`'s `angle` operator.
/// Returns 0 for the zero vector (`MetaPost` would give an error, but
/// we choose a safe default).
pub fn angle(x: Scalar, y: Scalar) -> Scalar {
    if x == 0.0 && y == 0.0 {
        return 0.0;
    }
    y.atan2(x).to_degrees()
}

/// `MetaPost`'s `mexp`: `mexp(x) = 2^(x/256)`.
///
/// This is `MetaPost`'s internal exponential function, where the base is
/// `2^(1/256)`. It maps 0 → 1, 256 → 2, 512 → 4, etc.
#[inline]
pub fn mexp(x: Scalar) -> Scalar {
    (x / 256.0 * core::f64::consts::LN_2).exp()
}

/// `MetaPost`'s `mlog`: inverse of `mexp`, so `mlog(x) = 256 * log2(x)`.
///
/// Returns 0 for non-positive input (`MetaPost` would error).
#[inline]
pub fn mlog(x: Scalar) -> Scalar {
    if x <= 0.0 {
        return 0.0;
    }
    256.0 * x.log2()
}

/// Pythagorean addition: `a ++ b = sqrt(a² + b²)`.
#[inline]
pub fn pyth_add(a: Scalar, b: Scalar) -> Scalar {
    a.hypot(b)
}

/// Pythagorean subtraction: `a +-+ b = sqrt(a² - b²)`.
///
/// Returns 0 if `a² < b²`.
#[inline]
pub fn pyth_sub(a: Scalar, b: Scalar) -> Scalar {
    let sq = a.mul_add(a, -(b * b));
    if sq <= 0.0 {
        0.0
    } else {
        sq.sqrt()
    }
}

/// Floor function (`MetaPost`'s `floor`).
#[inline]
pub fn floor(x: Scalar) -> Scalar {
    x.floor()
}

/// Uniform random deviate in [0, x).
///
/// Uses a simple xorshift for reproducibility. The `seed` is mutated.
pub fn uniform_deviate(x: Scalar, seed: &mut u64) -> Scalar {
    *seed ^= *seed << 13;
    *seed ^= *seed >> 7;
    *seed ^= *seed << 17;
    let frac = (*seed as Scalar) / (u64::MAX as Scalar);
    frac * x
}

/// Normal deviate (Gaussian, mean 0, standard deviation 1).
///
/// Uses the Box-Muller transform. The `seed` is mutated.
pub fn normal_deviate(seed: &mut u64) -> Scalar {
    let u1 = uniform_deviate(1.0, seed).max(1e-30);
    let u2 = uniform_deviate(1.0, seed);
    (-2.0 * u1.ln()).sqrt() * (2.0 * core::f64::consts::PI * u2).cos()
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
#[allow(clippy::float_cmp)]
mod tests {
    use super::*;
    use crate::types::EPSILON;

    #[test]
    fn test_sind_cosd_basic() {
        assert!((sind(0.0)).abs() < EPSILON);
        assert!((sind(90.0) - 1.0).abs() < EPSILON);
        assert!((sind(180.0)).abs() < EPSILON);
        assert!((sind(270.0) + 1.0).abs() < EPSILON);

        assert!((cosd(0.0) - 1.0).abs() < EPSILON);
        assert!((cosd(90.0)).abs() < EPSILON);
        assert!((cosd(180.0) + 1.0).abs() < EPSILON);
    }

    #[test]
    fn test_sind_cosd_identity() {
        // sin²(x) + cos²(x) = 1
        for deg in [0.0, 30.0, 45.0, 60.0, 90.0, 135.0, 210.0, 330.0] {
            let s = sind(deg);
            let c = cosd(deg);
            assert!(
                (s.mul_add(s, c * c) - 1.0).abs() < 1e-12,
                "failed for {deg}°"
            );
        }
    }

    #[test]
    fn test_angle() {
        assert!((angle(1.0, 0.0)).abs() < EPSILON);
        assert!((angle(0.0, 1.0) - 90.0).abs() < EPSILON);
        assert!((angle(-1.0, 0.0) - 180.0).abs() < EPSILON);
        assert!((angle(0.0, -1.0) + 90.0).abs() < EPSILON);
        assert!((angle(1.0, 1.0) - 45.0).abs() < EPSILON);
    }

    #[test]
    fn test_angle_zero_vector() {
        assert_eq!(angle(0.0, 0.0), 0.0);
    }

    #[test]
    fn test_mexp_mlog() {
        // mexp(0) = 1
        assert!((mexp(0.0) - 1.0).abs() < EPSILON);
        // mexp(256) = 2
        assert!((mexp(256.0) - 2.0).abs() < EPSILON);
        // mexp(512) = 4
        assert!((mexp(512.0) - 4.0).abs() < EPSILON);
    }

    #[test]
    fn test_mexp_mlog_roundtrip() {
        for x in [1.0, 2.0, 4.0, 0.5, 10.0, 100.0] {
            let result = mexp(mlog(x));
            assert!((result - x).abs() < 1e-10, "failed for x={x}: got {result}");
        }
    }

    #[test]
    fn test_mlog_nonpositive() {
        assert_eq!(mlog(0.0), 0.0);
        assert_eq!(mlog(-1.0), 0.0);
    }

    #[test]
    fn test_pyth_add() {
        assert!((pyth_add(3.0, 4.0) - 5.0).abs() < EPSILON);
        assert!((pyth_add(0.0, 5.0) - 5.0).abs() < EPSILON);
        assert!((pyth_add(1.0, 0.0) - 1.0).abs() < EPSILON);
    }

    #[test]
    fn test_pyth_sub() {
        assert!((pyth_sub(5.0, 3.0) - 4.0).abs() < EPSILON);
        assert!((pyth_sub(5.0, 4.0) - 3.0).abs() < EPSILON);
        // When a < b, returns 0
        assert_eq!(pyth_sub(3.0, 5.0), 0.0);
    }

    #[test]
    fn test_floor() {
        assert_eq!(floor(3.7), 3.0);
        assert_eq!(floor(-1.2), -2.0);
        assert_eq!(floor(5.0), 5.0);
    }

    #[test]
    fn test_uniform_deviate_range() {
        let mut seed = 42u64;
        for _ in 0..100 {
            let v = uniform_deviate(10.0, &mut seed);
            assert!((0.0..10.0).contains(&v), "out of range: {v}");
        }
    }

    #[test]
    fn test_normal_deviate_distribution() {
        let mut seed = 123_456u64;
        let n = 10_000;
        let sum: Scalar = (0..n).map(|_| normal_deviate(&mut seed)).sum();
        let mean = sum / Scalar::from(n);
        // Mean should be close to 0
        assert!(mean.abs() < 0.1, "mean too far from 0: {mean}");
    }
}
