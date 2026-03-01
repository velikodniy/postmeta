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

pub mod error;
pub mod math;
pub mod path;
pub mod pen;
pub mod transform;
pub mod types;

pub mod bbox;
pub mod bezier;
pub mod intersection;
pub mod picture;
