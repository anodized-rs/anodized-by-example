#![cfg_attr(anodized_charon, feature(register_tool))]
#![cfg_attr(anodized_charon, register_tool(charon))]

use anodized::spec;

#[spec(
    // TODO: Use `seq.is_sorted()` once Aeneas has better iterator support.
    requires: slice_is_sorted(seq),
    ensures: |output| match output {
        Some(index) => index < seq.len() && seq[index] == *value,
        None => !seq.contains(value),
    },
)]
pub fn bin_search(seq: &[i32], value: &i32) -> Option<usize> {
    use std::cmp::Ordering::*;
    let mut lo = 0;
    let mut hi = seq.len();
    while lo < hi {
        let mid = lo + (hi - lo) / 2;
        match seq[mid].cmp(value) {
            Less => lo = mid + 1,
            Greater => hi = mid,
            Equal => return Some(mid),
        }
    }
    None
}

fn slice_is_sorted(seq: &[i32]) -> bool {
    for i in 1..seq.len() {
        if let std::cmp::Ordering::Greater = seq[i - 1].cmp(&seq[i]) {
            return false;
        }
    }
    true
}
