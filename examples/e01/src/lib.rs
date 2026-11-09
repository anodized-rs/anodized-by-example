#![cfg_attr(anodized_charon, feature(register_tool))]
#![cfg_attr(anodized_charon, register_tool(charon))]

use anodized::spec;

// Fn specs

#[spec(requires: x > 0)]
pub fn f1(x: u8) {}

#[spec(ensures: |output| output == 1)]
pub fn f2() -> u8 {
    1
}

// Input with a precondition: `x > 0` is required so `x - 1` does not underflow.
// The postcondition `*output < x` is a total comparison (no fallible ops in the predicate).
#[spec(
    requires: x > 0,
    ensures: |output| output < x,
)]
pub fn f4(x: u8) -> u8 {
    x - 1
}

// Trait specs

#[spec]
pub trait T {
    #[spec(
        requires: x > 0,
        ensures: |output| output > 0,
    )]
    fn f3(x: u8) -> u8;
}

#[spec]
impl T for u8 {
    #[spec(
        requires: true,
        ensures: |output| output > 1,
    )]
    fn f3(x: u8) -> u8 {
        2
    }
}
