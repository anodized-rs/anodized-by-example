import translation.Funs
import IntExternal

set_option maxHeartbeats 2000000

open Aeneas Std Result
open e03
open anodized_logic.arithmetic (int)

theorem eq_ok_iff {α} {m : Result α} {v : α} :
    m = ok v ↔ Std.WP.spec m (fun x => x = v) := by
  cases m <;> simp

@[step] theorem pow2_spec (k : Std.Usize) :
    pow2 k ⦃ z => z.toInt = (2 : Int) ^ k.val ⦄ := by
  unfold pow2
  step
  unfold pow2_loop
  apply Std.loop.spec_decr_nat
    (measure := fun p => p.1.«end».val - p.1.start.val)
    (inv := fun p => p.1.start.val ≤ k.val ∧ p.1.«end» = k ∧
      p.2.toInt = (2 : Int) ^ p.1.start.val)
  · rintro ⟨it, p⟩ ⟨hle, hend, hp⟩
    unfold pow2_loop.body
    by_cases hlt : it.start.val < it.«end».val
    · step with (Std.core.iter.range.IteratorRange.next_Usize_some_spec it hlt)
      step*
    · step with (Std.core.iter.range.IteratorRange.next_Usize_none_spec it (by omega))
      step*
  · simp_all

def byteValue (s : List Std.U8) (start count : Nat) : Nat :=
  ∑ j ∈ Finset.range count, 2 ^ (8 * j) * s[start + j]!.val

@[step] theorem u8_32_as_nat_spec (bytes : Array Std.U8 32#usize) :
    u8_32_as_nat bytes ⦃ z => z.toInt = (byteValue bytes.val 0 32 : Int) ⦄ := by
  unfold u8_32_as_nat
  step*
  unfold u8_32_as_nat_loop
  apply Std.loop.spec_decr_nat
    (measure := fun p => 32 - p.1.start.val)
    (inv := fun p => p.1.start.val ≤ 32 ∧ p.1.«end».val = 32 ∧
      p.2.toInt = (byteValue bytes.val 0 p.1.start.val : Int))
  · rintro ⟨it, acc⟩ ⟨hle, hend, hacc⟩
    dsimp only at hle hend hacc
    unfold u8_32_as_nat_loop.body
    by_cases hlt : it.start.val < it.«end».val
    · step with (Std.core.iter.range.IteratorRange.next_Usize_some_spec it hlt)
      step*
      have hieq : i = it.start := by grind
      subst i
      simp_lists
      all_goals simp_all [byteValue, Finset.sum_range_succ, Nat.cast_add,
        Nat.cast_mul, Nat.cast_pow]
      all_goals rw [List.getElem?_eq_getElem (by simp; omega)]
      all_goals simp
      all_goals omega
    · step with (Std.core.iter.range.IteratorRange.next_Usize_none_spec it (by omega))
      step*
  · simp_all [byteValue]

/-- Disjoint bit ranges combine identically under OR and addition. -/
private theorem or_mul_pow (a b k : Nat) (hk : k = 2 ^ k.log2) (hb : b < k) :
    b ||| a * k = b + a * k := by
  have h := Nat.two_pow_add_eq_or_of_lt (i := k.log2) (by rwa [← hk]) a
  simpa only [← hk, Nat.or_comm, Nat.mul_comm, Nat.add_comm] using h.symm

@[step] theorem spec_load8_at_spec (input : Aeneas.Std.Slice Std.U8) (i : Std.Usize)
    (hi : i.val + 7 < input.length) :
    spec_load8_at input i ⦃ z => z.toInt = (byteValue input.val i.val 8 : Int) ⦄ := by
  change i.val + 7 < input.val.length at hi
  unfold spec_load8_at
  step*
  norm_num [byteValue, Finset.sum_range_succ, Nat.cast_add, Nat.cast_mul]
  simp (disch := omega) only [List.getElem?_eq_getElem, Option.getD_some]
  simp_all

@[step] theorem load8_at_spec (input : Aeneas.Std.Slice Std.U8) (i : Std.Usize)
    (hi : i.val + 7 < input.length) :
    load8_at input i ⦃ z => z.val = byteValue input.val i.val 8 ⦄ := by
  change i.val + 7 < input.val.length at hi
  unfold load8_at
  step*
  norm_num [byteValue, Finset.sum_range_succ]
  simp (disch := omega) only [List.getElem?_eq_getElem, Option.getD_some]
  simp_all only [UScalar.cast_val_eq, UScalar.cast_bv_eq]
  simp_all [Nat.shiftLeft_eq]
  norm_num [UScalar.size, UScalarTy.numBits, U64.size, U64.numBits] at *
  simp (disch := scalar_tac) only [Nat.mod_eq_of_lt] at *
  simp (disch := first | decide | (clear * - input i hi; scalar_tac)) only [or_mul_pow]
  omega

/-- The five overlapping byte windows partition the low 255 bits into 51-bit limbs. -/
theorem decode_windows (bytes : Array U8 32#usize) :
    byteValue bytes.val 0 8 % 2 ^ 51 +
      2 ^ 51 * (byteValue bytes.val 6 8 / 2 ^ 3 % 2 ^ 51) +
      2 ^ 102 * (byteValue bytes.val 12 8 / 2 ^ 6 % 2 ^ 51) +
      2 ^ 153 * (byteValue bytes.val 19 8 / 2 % 2 ^ 51) +
      2 ^ 204 * (byteValue bytes.val 24 8 / 2 ^ 12 % 2 ^ 51) =
        byteValue bytes.val 0 32 % 2 ^ 255 := by
  norm_num [byteValue, Finset.sum_range_succ]
  scalar_tac

attribute [step_simps] e03.anodized.__.eval e03.anodized.__.eval_once
  e03.anodized.__.apply_keep
  __anodized_fn_ensures_load8_at
  __anodized_fn_ensures_load8_at.closure.Insts.CoreOpsFunctionFnOnceTupleU64.call_once
  __anodized_fn_ensures_load8_at.closure_1.Insts.CoreOpsFunctionFnTupleU64PairBoolU64.call
  __anodized_fn_ensures_load8_at.closure_1.closure.Insts.CoreOpsFunctionFnTupleBool.call

theorem fn_pre_implies_post_load8_at :
    ∀ (input : Aeneas.Std.Slice Std.U8) (i : Std.Usize),
      __anodized_fn_requires_load8_at input i = ok true →
        load8_at input i ⦃ result => __anodized_fn_ensures_load8_at input i result = ok true ⦄ := by
  intro input i pre
  have hi : i.val + 7 < input.length := by
    simp only [__anodized_fn_requires_load8_at, e03.anodized.__.eval,
      __anodized_fn_requires_load8_at.closure.Insts.CoreOpsFunctionFnTupleBool.call] at pre
    unfold HAdd.hAdd instHAddUScalarResult UScalar.add UScalar.tryMk UScalar.tryMkOpt at pre
    dsimp only at pre
    by_cases hb : UScalar.check_bounds .Usize (i.val + (7#usize).val) = true
    · simp_all [Result.ofOption]
    · simp_all [Result.ofOption]
      simp [Nat.not_lt.mpr hb] at pre
  step with (load8_at_spec input i hi)
  rw [eq_ok_iff]
  step*

def limbValue (limbs : List Std.U64) : Nat :=
  limbs[0]!.val + 2 ^ 51 * limbs[1]!.val + 2 ^ 102 * limbs[2]!.val +
    2 ^ 153 * limbs[3]!.val + 2 ^ 204 * limbs[4]!.val

@[step] theorem fe51_as_nat_spec (fe : FieldElement51) :
    fe51_as_nat fe ⦃ z => z.toInt = (limbValue fe.limbs.val : Int) ⦄ := by
  unfold fe51_as_nat u64_5_as_nat
  step*
  simp_all [limbValue, Nat.cast_add, Nat.cast_mul]

@[step] theorem fe51_limbs_bounded_spec (fe : FieldElement51)
    (hb : ∀ j, j < fe.limbs.val.length → fe.limbs.val[j]!.val < 2 ^ 51) :
    fe51_limbs_bounded fe ⦃ b => b = true ⦄ := by
  unfold fe51_limbs_bounded
  step
  unfold fe51_limbs_bounded_loop
  apply Std.loop.spec_decr_nat
    (measure := fun it => it.slice.val.length - it.i)
    (inv := fun it => it.slice.val = fe.limbs.val ∧ it.i ≤ it.slice.val.length)
  · intro it ⟨hs, hi⟩
    unfold fe51_limbs_bounded_loop.body core.slice.iter.IteratorSliceIter.next
    by_cases hlt : it.i < it.slice.val.length
    · simp only [Slice.len_val, hlt, ↓reduceDIte, bind_ok]
      have hbound : it.slice.val[it.i].val < 2 ^ 51 := by
        have h := hb it.i (by simpa [← hs] using hlt)
        rw [← hs] at h
        simpa only [List.getElem!_eq_getElem?_getD,
          List.getElem?_eq_getElem hlt, Option.getD_some] using h
      step*
    · simp [hlt]
  · simp_all

@[step] private theorem low_mask_spec :
    from_bytes.LOW_51_BIT_MASK ⦃ m => m.val = 2 ^ 51 - 1 ⦄ := by
  unfold from_bytes.LOW_51_BIT_MASK
  step*

private theorem mask_val (n : Nat) :
    n &&& 2251799813685247 = n % 2251799813685248 := by
  simpa using Nat.and_two_pow_sub_one_eq_mod n 51

private theorem from_bytes_correct (bytes : Array Std.U8 32#usize) :
    from_bytes bytes ⦃ fe =>
      limbValue fe.limbs.val = byteValue bytes.val 0 32 % 2 ^ 255 ∧
      ∀ j, j < fe.limbs.val.length → fe.limbs.val[j]!.val < 2 ^ 51 ⦄ := by
  unfold from_bytes
  step*
  simp_lists
  simp_all [limbValue]
  simp only [mask_val, Nat.shiftRight_eq_div_pow] at *
  constructor
  · simpa using decode_windows bytes
  · intro j hj
    have hjcases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega
    rcases hjcases with h | h | h | h | h <;> subst j <;> simp_all <;> omega

attribute [step_simps] __anodized_fn_ensures_from_bytes
  __anodized_fn_ensures_from_bytes.closure.Insts.CoreOpsFunctionFnOnceTupleFieldElement51.call_once
  __anodized_fn_ensures_from_bytes.closure_1.Insts.CoreOpsFunctionFnTupleFieldElement51PairBoolFieldElement51.call
  __anodized_fn_ensures_from_bytes.closure_1.closure.Insts.CoreOpsFunctionFnTupleBool.call
  __anodized_fn_ensures_from_bytes.closure_2.Insts.CoreOpsFunctionFnTupleFieldElement51PairBoolFieldElement51.call
  __anodized_fn_ensures_from_bytes.closure_2.closure.Insts.CoreOpsFunctionFnTupleBool.call

/-- Both extracted postconditions hold: decoding preserves the low 255 bits and
every output limb fits in 51 bits. -/
theorem fn_pre_implies_post_from_bytes :
    ∀ (bytes : Array Std.U8 32#usize),
      __anodized_fn_requires_from_bytes bytes = ok true →
        from_bytes bytes ⦃ result => __anodized_fn_ensures_from_bytes bytes result = ok true ⦄ := by
  intro bytes _
  apply Std.WP.spec_mono (from_bytes_correct bytes)
  intro fe ⟨hvalue, hbounded⟩
  rw [eq_ok_iff]
  step with (fe51_as_nat_spec fe) as ⟨v, hv⟩
  step with (u8_32_as_nat_spec bytes) as ⟨n, hn⟩
  step with (pow2_spec 255#usize) as ⟨divisor, hdivisor⟩
  step with (int_rem_int_step n divisor (by rw [hdivisor]; norm_num)) as ⟨r, hr⟩
  step with (int_eq_int_step v r) as ⟨eq, heq⟩
  step with (fe51_limbs_bounded_spec fe hbounded) as ⟨b, hb⟩
  have hcast : (limbValue fe.limbs.val : Int) =
      Int.tmod (byteValue bytes.val 0 32 : Int) ((2 : Int) ^ 255) := by
    rw [hvalue]
    exact Int.ofNat_tmod (byteValue bytes.val 0 32) (2 ^ 255)
  simp only [hb, heq, hr, hv, hn, hdivisor]
  simp only [hcast, decide_true, Bool.and_true]
