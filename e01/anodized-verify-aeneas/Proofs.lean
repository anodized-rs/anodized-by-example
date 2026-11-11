import translation.Funs

open Aeneas Std.Result
open e01

attribute [step_simps] e01.anodized.__.eval e01.anodized.__.eval_once
  e01.anodized.__.apply_keep
  __anodized_fn_requires_f1 __anodized_fn_ensures_f1
  __anodized_fn_requires_f2 __anodized_fn_ensures_f2
  __anodized_fn_requires_f4 __anodized_fn_ensures_f4
  __anodized_fn_requires_f4.closure.Insts.CoreOpsFunctionFnTupleBool.call
  __anodized_fn_ensures_f2.closure.Insts.CoreOpsFunctionFnOnceTupleU8.call_once
  __anodized_fn_ensures_f2.closure_1.Insts.CoreOpsFunctionFnTupleU8PairBoolU8.call
  __anodized_fn_ensures_f2.closure_1.closure.Insts.CoreOpsFunctionFnTupleBool.call
  __anodized_fn_ensures_f4.closure.Insts.CoreOpsFunctionFnOnceTupleU8.call_once
  __anodized_fn_ensures_f4.closure_1.Insts.CoreOpsFunctionFnTupleU8PairBoolU8.call
  __anodized_fn_ensures_f4.closure_1.closure.Insts.CoreOpsFunctionFnTupleBool.call

theorem fn_pre_implies_post_f1 : ∀ x, __anodized_fn_requires_f1 x = ok true →
    f1 x ⦃ result => __anodized_fn_ensures_f1 x result = ok true ⦄ := by
  intro x _
  simp [f1, __anodized_fn_ensures_f1, anodized.__.eval_once,
    __anodized_fn_ensures_f1.closure.Insts.CoreOpsFunctionFnOnceTupleTuple.call_once]

theorem fn_pre_implies_post_f2 : __anodized_fn_requires_f2 = ok true →
    f2 ⦃ result => __anodized_fn_ensures_f2 result = ok true ⦄ := by
  intro _
  unfold f2
  step*

theorem fn_pre_implies_post_f4 : ∀ x, __anodized_fn_requires_f4 x = ok true →
    f4 x ⦃ result => __anodized_fn_ensures_f4 x result = ok true ⦄ := by
  intro x hx
  -- precondition `x > 0`
  simp only [step_simps] at hx
  unfold f4
  step*
