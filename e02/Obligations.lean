import e02.translation.Funs

open Aeneas Std.Result

namespace Obligations

/-- The extracted precondition implies the postcondition for `e02::bin_search`. -/
def e02_bin_search : Prop :=
  ∀ (seq : Aeneas.Std.Slice Std.I32) (value : Std.I32),
    e02.__anodized_fn_requires_bin_search seq value = ok true →
      e02.bin_search seq value ⦃ result =>
        e02.__anodized_fn_ensures_bin_search seq value result = ok true ⦄

end Obligations
