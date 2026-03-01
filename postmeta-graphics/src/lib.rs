#![cfg_attr(
    test,
    allow(
        clippy::expect_used,
        clippy::unwrap_used,
        clippy::panic,
        clippy::op_ref,
        clippy::float_cmp,
        clippy::manual_range_contains
    )
)]

pub mod types;

pub mod bbox;
pub mod bezier;
pub mod error;
pub mod intersection;
pub mod math;
pub mod path;
pub mod pen;
pub mod picture;
pub mod transform;
