#![cfg_attr(anodized_charon, feature(register_tool))]
#![cfg_attr(anodized_charon, register_tool(charon))]

use anodized::{arithmetic::int, spec};

/// A `FieldElement51` represents an element of the field
/// \\( \mathbb Z / (2\^{255} - 19)\\).
///
/// In the 64-bit implementation, a `FieldElement` is represented in
/// radix \\(2\^{51}\\) as five `u64`s; the coefficients are allowed to
/// grow up to \\(2\^{54}\\) between reductions modulo \\(p\\).
///
/// # Note
///
/// The `curve25519_dalek::field` module provides a type alias
/// `curve25519_dalek::field::FieldElement` to either `FieldElement51`
/// or `FieldElement2625`.
///
/// The backend-specific type `FieldElement51` should not be used
/// outside of the `curve25519_dalek::field` module.
#[derive(Copy, Clone)]
pub struct FieldElement51 {
    pub limbs: [u64; 5],
}

/// Load a `FieldElement51` from the low 255 bits of a 256-bit
/// input.
///
/// # Warning
///
/// This function does not check that the input used the canonical
/// representative.  It masks the high bit, but it will happily
/// decode 2^255 - 18 to 1.  Applications that require a canonical
/// encoding of every field element should decode, re-encode to
/// the canonical encoding, and check that the input was
/// canonical.
#[spec(
    ensures: |field_elem| [
        // Decode bytes to limbs (bit 255 is cleared)
        fe51_as_nat(&field_elem) == u8_32_as_nat(bytes) % pow2(255),
        // Each limb is masked with (2^51 - 1), so bounded by 51 bits
        fe51_limbs_bounded(&field_elem),
    ],
)]
pub fn from_bytes(bytes: &[u8; 32]) -> FieldElement51 {
    const LOW_51_BIT_MASK: u64 = (1 << 51) - 1;
    FieldElement51 {
        limbs: [
            // load bits [  0, 64), no shift
            load8_at(bytes, 0) & LOW_51_BIT_MASK,
            // load bits [ 48,112), shift to [ 51,112)
            (load8_at(bytes, 6) >> 3) & LOW_51_BIT_MASK,
            // load bits [ 96,160), shift to [102,160)
            (load8_at(bytes, 12) >> 6) & LOW_51_BIT_MASK,
            // load bits [152,216), shift to [153,216)
            (load8_at(bytes, 19) >> 1) & LOW_51_BIT_MASK,
            // load bits [192,256), shift to [204,112)
            (load8_at(bytes, 24) >> 12) & LOW_51_BIT_MASK,
        ],
    }
}

#[spec(
    requires: i + 7 < input.len(),
    ensures: |output| int::from(output) == spec_load8_at(input, i),
)]
fn load8_at(input: &[u8], i: usize) -> u64 {
    (input[i] as u64)
        | ((input[i + 1] as u64) << 8)
        | ((input[i + 2] as u64) << 16)
        | ((input[i + 3] as u64) << 24)
        | ((input[i + 4] as u64) << 32)
        | ((input[i + 5] as u64) << 40)
        | ((input[i + 6] as u64) << 48)
        | ((input[i + 7] as u64) << 56)
}

/// Load 8 consecutive bytes from a byte array and interpret as a little-endian u64.
///
/// Returns: bytes[i] + bytes[i+1] * 2^8 + ... + bytes[i+7] * 2^56
///
/// This is commonly used when unpacking byte arrays into larger word-sized limbs.
#[rustfmt::skip]
fn spec_load8_at(input: &[u8], i: usize) -> int {
    pow2(0 * 8) * int::from(input[i + 0]) +
    pow2(1 * 8) * int::from(input[i + 1]) +
    pow2(2 * 8) * int::from(input[i + 2]) +
    pow2(3 * 8) * int::from(input[i + 3]) +
    pow2(4 * 8) * int::from(input[i + 4]) +
    pow2(5 * 8) * int::from(input[i + 5]) +
    pow2(6 * 8) * int::from(input[i + 6]) +
    pow2(7 * 8) * int::from(input[i + 7])
}

fn fe51_as_nat(fe: &FieldElement51) -> int {
    u64_5_as_nat(fe.limbs)
}

/// Spec predicate: all limbs are bounded by a given bit limit.
fn fe51_limbs_bounded(fe: &FieldElement51) -> bool {
    for limb in fe.limbs {
        if limb >= 1u64 << 51 {
            return false;
        }
    }
    true
}

/// Evaluation function, given a field element as limbs, reconstruct the nat value it represents.
#[rustfmt::skip]
fn u64_5_as_nat(limbs: [u64; 5]) -> int {
                int::from(limbs[0]) +
     pow2(51) * int::from(limbs[1]) +
    pow2(102) * int::from(limbs[2]) +
    pow2(153) * int::from(limbs[3]) +
    pow2(204) * int::from(limbs[4])
}

/// Convert a 32-byte array to its natural number representation (little-endian).
///
/// This function interprets a byte array as a 256-bit little-endian integer:
/// bytes[0] + bytes[1] * 2^8 + bytes[2] * 2^16 + ... + bytes[31] * 2^248
fn u8_32_as_nat(bytes: &[u8; 32]) -> int {
    let mut acc = int::from(0);
    for i in 0..bytes.len() {
        acc = acc + pow2(8 * i) * int::from(bytes[i]);
    }
    acc
}

fn pow2(k: usize) -> int {
    let mut p = int::from(1);
    for _ in 0..k {
        p *= 2;
    }
    p
}
