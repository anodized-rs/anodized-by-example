import e01.translation.Funs

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

end Obligations
