use anodized::spec;

#[spec(
    requires: {
        // TODO: Write `seq.is_sorted()` when Aeneas ships support for it.
        for i in 1..seq.len() {
            if seq[i - 1] > seq[i] {
               return false;
            } 
        }
        true
    },
    ensures: |output| match output {
        Some(index) => index < seq.len() && seq[index] == *value,
        None => {
            // TODO: Write `seq.iter().all(|item| item != value)` when Aeneas ships support for it.
            for item in seq {
                if item == value {
                    return false;
                }
            }
            true
        },
    },
)]
pub fn bin_search<T: Ord>(seq: &[T], value: &T) -> Option<usize> {
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
