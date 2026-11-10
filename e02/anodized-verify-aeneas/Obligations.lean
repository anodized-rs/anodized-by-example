import Proofs

open Aeneas Std.Result

/-- The extracted precondition implies the postcondition for `e02::bin_search`. -/
recall fn_pre_implies_post_bin_search :
  ∀ (seq : Aeneas.Std.Slice Std.I32) (value : Std.I32),
    e02.__anodized_fn_requires_bin_search seq value = ok true →
      e02.bin_search seq value ⦃ result =>
        e02.__anodized_fn_ensures_bin_search seq value result = ok true ⦄

/-- info: 'fn_pre_implies_post_bin_search' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms fn_pre_implies_post_bin_search
