use postmeta_graphics::path::Path;
use postmeta_graphics::types::{KnotDirection, Scalar};

/// Convert a resolved [`Path`] to an SVG path data string.
///
/// Uses cubic Bezier commands (M, C, Z). All coordinates are f64 with
/// the specified precision. Y coordinates are negated to convert from
/// `MetaPost` (Y-up) to SVG (Y-down).
pub fn path_to_d(path: &Path, precision: usize) -> String {
    if path.knots.is_empty() {
        return String::new();
    }

    let mut d = String::with_capacity(path.knots.len() * 40);
    let p0 = path.knots[0].point;
    d.push('M');
    write_point(&mut d, p0.x, -p0.y, precision);

    let n = path.num_segments();
    for i in 0..n {
        let j = (i + 1) % path.knots.len();
        let k0 = &path.knots[i];
        let k1 = &path.knots[j];

        let cp1 = match k0.right {
            KnotDirection::Explicit(p) => p,
            _ => k0.point,
        };
        let cp2 = match k1.left {
            KnotDirection::Explicit(p) => p,
            _ => k1.point,
        };

        d.push('C');
        write_point(&mut d, cp1.x, -cp1.y, precision);
        d.push(' ');
        write_point(&mut d, cp2.x, -cp2.y, precision);
        d.push(' ');
        write_point(&mut d, k1.point.x, -k1.point.y, precision);
    }

    if path.is_cyclic {
        d.push('Z');
    }

    d
}

/// Write "x,y" to the string with the given precision.
///
/// Normalizes negative zero to positive zero for cleaner output.
fn write_point(d: &mut String, x: Scalar, y: Scalar, precision: usize) {
    use std::fmt::Write;
    let x = if x == 0.0 { 0.0 } else { x };
    let y = if y == 0.0 { 0.0 } else { y };
    let _ = write!(d, "{x:.precision$},{y:.precision$}");
}
