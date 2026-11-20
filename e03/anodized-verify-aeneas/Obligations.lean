import Proofs

open Aeneas Std.Result

/-- The extracted precondition implies the postcondition for `e03::from_bytes`. -/
recall fn_pre_implies_post_from_bytes :
  ∀ (bytes : Aeneas.Std.Array Std.U8 32#usize),
    e03.__anodized_fn_requires_from_bytes bytes = ok true →
      e03.from_bytes bytes ⦃ result =>
        e03.__anodized_fn_ensures_from_bytes bytes result = ok true ⦄

/-- The extracted precondition implies the postcondition for `e03::load8_at`. -/
recall fn_pre_implies_post_load8_at :
  ∀ (input : Aeneas.Std.Slice Std.U8) (i : Std.Usize),
    e03.__anodized_fn_requires_load8_at input i = ok true →
      e03.load8_at input i ⦃ result =>
        e03.__anodized_fn_ensures_load8_at input i result = ok true ⦄

/-- info: 'fn_pre_implies_post_load8_at' depends on axioms: [int_add_int_step,
 int_eq_int_step,
 int_from_i32_step,
 int_from_u64_step,
 int_from_u8_step,
 int_mul_assign_i32_step,
 int_mul_int_step,
 propext,
 Classical.choice,
 Quot.sound,
 anodized_logic.arithmetic.int,
 anodized_logic.arithmetic.int.toInt,
 anodized_logic.arithmetic.int.Insts.CoreCmpPartialEqint.eq,
 anodized_logic.arithmetic.int.Insts.CoreConvertFromI32.from,
 anodized_logic.arithmetic.int.Insts.CoreConvertFromU64.from,
 anodized_logic.arithmetic.int.Insts.CoreConvertFromU8.from,
 anodized_logic.arithmetic.int.Insts.CoreOpsArithAddintint.add,
 anodized_logic.arithmetic.int.Insts.CoreOpsArithMulAssignI32.mul_assign,
 anodized_logic.arithmetic.int.Insts.CoreOpsArithMulintint.mul] -/
#guard_msgs in #print axioms fn_pre_implies_post_load8_at
