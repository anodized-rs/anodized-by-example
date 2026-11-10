import examples.e01.translation.Funs
import examples.e02.translation.Funs

open Aeneas Std.Result

namespace Obligations

/-- The extracted precondition implies the postcondition for `e01::f2`. -/
def e01_f2 : Prop :=
  e01.__anodized_fn_requires_f2 = ok true →
    e01.f2 ⦃ result => e01.__anodized_fn_ensures_f2 result = ok true ⦄

/-- The extracted precondition implies the postcondition for `e01::f4`. -/
def e01_f4 : Prop :=
  ∀ x, e01.__anodized_fn_requires_f4 x = ok true →
    e01.f4 x ⦃ result => e01.__anodized_fn_ensures_f4 x result = ok true ⦄

/-- The extracted precondition implies the postcondition for `e02::bin_search`. -/
def e02_bin_search : Prop :=
  ∀ (seq : Aeneas.Std.Slice Std.I32) (value : Std.I32),
    e02.__anodized_fn_requires_bin_search seq value = ok true →
      e02.bin_search seq value ⦃ result =>
        e02.__anodized_fn_ensures_bin_search seq value result = ok true ⦄

end Obligations
