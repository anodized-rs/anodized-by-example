import examples.e02.translation.Funs

open Aeneas Std.Result
open e02

/-- The extracted precondition implies the extracted postcondition for binary search. -/
def bin_search_spec : Prop :=
  ∀ (seq : Aeneas.Std.Slice Std.I32) (value : Std.I32),
    __anodized_fn_requires_bin_search seq value = ok true →
      (bin_search seq value) ⦃ result =>
        __anodized_fn_ensures_bin_search seq value result = ok true ⦄
