import translation.FunsExternal

/-!
Value model for Anodized's unbounded integer and specifications for the external
operations used by e03, following Proofs/IntExternal.lean at commit 062e041.

These are trusted assumptions about the Rust implementation, not proved facts
about the opaque extracted type. In particular, remainder truncates toward zero
(BigInt semantics), rather than using Lean's Euclidean remainder.
This file stays outside translation/ so regeneration preserves the model.
-/

open Aeneas Std Result
open anodized_logic.arithmetic (int)

/-- The mathematical integer represented by an Anodized logical integer. -/
axiom anodized_logic.arithmetic.int.toInt : int → Int

@[step] axiom int_from_i32_step (x : Std.I32) :
  (int.Insts.CoreConvertFromI32.from x) ⦃ z => z.toInt = x.val ⦄

@[step] axiom int_from_u8_step (x : Std.U8) :
  (int.Insts.CoreConvertFromU8.from x) ⦃ z => z.toInt = (x.val : Int) ⦄

@[step] axiom int_from_u64_step (x : Std.U64) :
  (int.Insts.CoreConvertFromU64.from x) ⦃ z => z.toInt = (x.val : Int) ⦄

@[step] axiom int_eq_int_step (x y : int) :
  (int.Insts.CoreCmpPartialEqint.eq x y) ⦃ b => b = decide (x.toInt = y.toInt) ⦄

@[step] axiom int_add_int_step (x y : int) :
  (int.Insts.CoreOpsArithAddintint.add x y) ⦃ z => z.toInt = x.toInt + y.toInt ⦄

@[step] axiom int_mul_int_step (x y : int) :
  (int.Insts.CoreOpsArithMulintint.mul x y) ⦃ z => z.toInt = x.toInt * y.toInt ⦄

@[step] axiom int_mul_assign_i32_step (x : int) (y : Std.I32) :
  (int.Insts.CoreOpsArithMulAssignI32.mul_assign x y) ⦃ z => z.toInt = x.toInt * y.val ⦄

@[step] axiom int_rem_int_step (x y : int) (h : y.toInt ≠ 0) :
  (int.Insts.CoreOpsArithRemintint.rem x y) ⦃ z => z.toInt = Int.tmod x.toInt y.toInt ⦄
