use postmeta_graphics::path::BezierPath;
use postmeta_graphics::types::Scalar;

/// Convert a resolved [`BezierPath`] to an SVG path data string.
///
/// Uses cubic Bezier commands (M, C, Z). All coordinates are f64 with
/// the specified precision. Y coordinates are negated to convert from
/// `MetaPost` (Y-up) to SVG (Y-down).
pub fn path_to_d(path: &BezierPath, precision: usize) -> String {
    if path.num_knots() == 0 {
        return String::new();
    }

    let mut d = String::with_capacity(path.num_knots() * 40);
    let p0 = path.knot_point(0);
    d.push('M');
    write_point(&mut d, p0.x, -p0.y, precision);

    for seg in path.segments() {
        d.push('C');
        write_point(&mut d, seg.p1.x, -seg.p1.y, precision);
        d.push(' ');
        write_point(&mut d, seg.p2.x, -seg.p2.y, precision);
        d.push(' ');
        write_point(&mut d, seg.p3.x, -seg.p3.y, precision);
    }

    if path.is_cyclic() {
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
