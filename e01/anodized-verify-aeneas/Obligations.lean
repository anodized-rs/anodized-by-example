import Proofs

open Aeneas Std.Result

/-- The extracted precondition implies the postcondition for `e01::f1`. -/
recall fn_pre_implies_post_f1 :
  ∀ x, e01.__anodized_fn_requires_f1 x = ok true →
    e01.f1 x ⦃ result => e01.__anodized_fn_ensures_f1 x result = ok true ⦄

/-- info: 'fn_pre_implies_post_f1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms fn_pre_implies_post_f1

/-- The extracted precondition implies the postcondition for `e01::f2`. -/
recall fn_pre_implies_post_f2 :
  e01.__anodized_fn_requires_f2 = ok true →
    e01.f2 ⦃ result => e01.__anodized_fn_ensures_f2 result = ok true ⦄

/-- info: 'fn_pre_implies_post_f2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms fn_pre_implies_post_f2

/-- The extracted precondition implies the postcondition for `e01::f4`. -/
recall fn_pre_implies_post_f4 :
  ∀ x, e01.__anodized_fn_requires_f4 x = ok true →
    e01.f4 x ⦃ result => e01.__anodized_fn_ensures_f4 x result = ok true ⦄

/-- info: 'fn_pre_implies_post_f4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms fn_pre_implies_post_f4
