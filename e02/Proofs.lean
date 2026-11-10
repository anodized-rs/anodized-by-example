import e02.Obligations

open Aeneas Std Result
open e02

private theorem bin_search_loop_body_done
    (s : Aeneas.Std.Slice Std.I32) (v : Std.I32) (lo hi : Std.Usize) (h : ¬ lo < hi) :
    bin_search_loop.body s v lo hi = ok (.done none) := by
  simp [bin_search_loop.body, h]

private theorem bin_search_body_progress
    (s : Aeneas.Std.Slice Std.I32) (v : Std.I32) (lo hi : Std.Usize)
    (bounds : lo.val < hi.val ∧ hi.val ≤ s.length) :
    (bin_search_loop.body s v lo hi) ⦃ r => match r with
      | .cont (l, h) => l.val ≤ h.val ∧ h.val ≤ s.length ∧ h.val - l.val < hi.val - lo.val
      | .done (some i) => i.val < s.length
      | .done none => False ⦄ := by
  unfold bin_search_loop.body
  step*
  simp only [Std.lift]
  step* <;> omega

private theorem bin_search_body_correct
    (s : Aeneas.Std.Slice Std.I32) (v : Std.I32) (lo hi : Std.Usize)
    (bounds : lo.val < hi.val ∧ hi.val ≤ s.length)
    (sorted : ∀ i j, i < s.length → j < s.length → i ≤ j → s[i]! ≤ s[j]!)
    (excluded : ∀ i, i < s.length → (i < lo.val ∨ hi.val ≤ i) → s[i]! ≠ v) :
    (bin_search_loop.body s v lo hi) ⦃ r => match r with
      | .cont (l, h) => ∀ i, i < s.length → (i < l.val ∨ h.val ≤ i) → s[i]! ≠ v
      | .done (some i) => i.val < s.length ∧ s[i.val]! = v
      | .done none => False ⦄ := by
  unfold bin_search_loop.body
  step*
  simp only [Std.lift]
  step*
  all_goals simp_all [Std.core.cmp.impls.OrdI32.cmp, Int.compare_eq_lt, Int.compare_eq_gt]
  · rename_i hcmp
    intro j hj hjout
    have hm : lo.val + (hi.val - lo.val) / 2 < s.val.length := by
      simp only [Aeneas.Std.Slice.length] at bounds
      omega
    rcases hjout with hjle | hjge
    · have hs := sorted j (lo.val + (hi.val - lo.val) / 2) hj hm hjle
      omega
    · exact excluded j hj (Or.inr hjge)
  · rename_i hcmp
    have hm : lo.val + (hi.val - lo.val) / 2 < s.val.length := by
      simp only [Aeneas.Std.Slice.length] at bounds
      omega
    constructor
    · exact hm
    · simpa [hm] using Std.IScalar.eq_of_val_eq hcmp
  · rename_i hcmp
    intro j hj hjout
    have hm : lo.val + (hi.val - lo.val) / 2 < s.val.length := by
      simp only [Aeneas.Std.Slice.length] at bounds
      omega
    rcases hjout with hjlt | hjge
    · exact excluded j hj (Or.inl hjlt)
    · have hs := sorted (lo.val + (hi.val - lo.val) / 2) j hm hj hjge
      omega

private theorem bin_search_loop_correct
    (s : Aeneas.Std.Slice Std.I32) (v : Std.I32) (lo hi : Std.Usize)
    (bounds : lo.val ≤ hi.val ∧ hi.val ≤ s.length)
    (sorted : ∀ i j, i < s.length → j < s.length → i ≤ j → s[i]! ≤ s[j]!)
    (excluded : ∀ i, i < s.length → (i < lo.val ∨ hi.val ≤ i) → s[i]! ≠ v) :
    (bin_search_loop s v lo hi) ⦃ r => match r with
      | some i => i.val < s.length ∧ s[i.val]! = v
      | none => ∀ i, i < s.length → s[i]! ≠ v ⦄ := by
  unfold bin_search_loop
  apply Std.loop.spec_decr_nat
    (measure := fun p => p.2.val - p.1.val)
    (inv := fun p => p.1.val ≤ p.2.val ∧ p.2.val ≤ s.length ∧
      ∀ i, i < s.length → (i < p.1.val ∨ p.2.val ≤ i) → s[i]! ≠ v)
  · rintro ⟨l, h⟩ ⟨hle, hbound, hexcluded⟩
    by_cases hlt : l.val < h.val
    · have hp := bin_search_body_progress s v l h ⟨hlt, hbound⟩
      have hc := bin_search_body_correct s v l h ⟨hlt, hbound⟩ sorted hexcluded
      apply Std.WP.spec_mono (Std.WP.spec_and hp hc)
      intro r hr
      cases r with
      | cont p =>
        rcases p with ⟨a, b⟩
        exact ⟨⟨hr.1.1, hr.1.2.1, hr.2⟩, hr.1.2.2⟩
      | done r =>
        cases r with
        | none => exact False.elim hr.1
        | some x => exact hr.2
    · dsimp only
      rw [bin_search_loop_body_done s v l h (by scalar_tac)]
      simp only [Std.WP.spec_ok]
      intro i hi
      apply hexcluded i hi
      simp only
      omega
  · exact ⟨bounds.1, bounds.2, excluded⟩

private theorem slice_sorted_adjacent (s : Aeneas.Std.Slice Std.I32) :
    slice_is_sorted s ⦃ b => b = true →
      ∀ i, 0 < i → i < s.length → s[i - 1]! ≤ s[i]! ⦄ := by
  unfold slice_is_sorted slice_is_sorted_loop
  apply Std.loop.spec_decr_nat
    (measure := fun it => s.length - it.start.val)
    (inv := fun it => it.«end».val = s.length ∧ 1 ≤ it.start.val ∧
      ∀ i, 0 < i → i < it.start.val → i < s.length → s[i - 1]! ≤ s[i]!)
  · intro it ⟨hend, hlo, hinv⟩
    unfold slice_is_sorted_loop.body
    by_cases hlt : it.start.val < it.«end».val
    · step with (Std.core.iter.range.IteratorRange.next_Usize_some_spec it hlt)
      step*
      simp only [Std.lift]
      step*
      all_goals
        have hieq : i = it.start := by grind
        subst i
        simp_all [Std.core.cmp.impls.OrdI32.cmp, Int.compare_eq_lt]
        constructor
        · intro j hj hjle hjbound
          by_cases hje : j = it.start.val
          · subst j
            have hprev : it.start.val - 1 < s.val.length := by
              have he : it.«end».val = s.val.length := hend
              omega
            first | (simp_all; done) | (simp_all; omega)
          · exact hinv j hj (by omega) hjbound
        · have he : it.«end».val = s.val.length := hend
          omega
    · step with (Std.core.iter.range.IteratorRange.next_Usize_none_spec it (by omega))
      step*
  · simp; omega

private theorem adjacent_implies_sorted (s : Aeneas.Std.Slice Std.I32)
    (adj : ∀ i, 0 < i → i < s.length → s[i - 1]! ≤ s[i]!) :
    ∀ i j, i < s.length → j < s.length → i ≤ j → s[i]! ≤ s[j]! := by
  intro i j hi hj hij
  induction j using Nat.strong_induction_on generalizing i with
  | h j ih =>
    by_cases heq : i = j
    · subst j; exact _root_.le_refl _
    · have hp : 0 < j := by omega
      exact _root_.le_trans (ih (j - 1) (by omega) i hi (by omega) (by omega)) (adj j hp hj)

private theorem contains_eq (s : Aeneas.Std.Slice Std.I32) (v : Std.I32) :
    core.slice.Slice.contains core.cmp.PartialEqI32 s v = ok (decide (v ∈ s.val)) := by
  unfold core.slice.Slice.contains
  induction s.val with
  | nil => rfl
  | cons a xs ih =>
    by_cases h : v = a <;> simp [List.anyM, Std.liftFun2, ih, h, pure]

private theorem ensures_eq (s : Aeneas.Std.Slice Std.I32) (v : Std.I32) (r : Option Std.Usize) :
    __anodized_fn_ensures_bin_search s v r =
      __anodized_fn_ensures_bin_search.closure_1.closure.Insts.CoreOpsFunctionFnTupleBool.call
        (r, s, v) () := by
  simp [__anodized_fn_ensures_bin_search, e02.anodized.__.eval_once,
    e02.anodized.__.apply_keep, e02.anodized.__.eval,
    __anodized_fn_ensures_bin_search.closure.Insts.CoreOpsFunctionFnOnceTupleOptionUsize.call_once,
    __anodized_fn_ensures_bin_search.closure_1.Insts.CoreOpsFunctionFnTupleOptionUsizePairBoolOptionUsize.call]

theorem bin_search_spec : Obligations.fn_pre_implies_post_bin_search := by
  intro s v pre
  have sorted_pre : slice_is_sorted s = ok true := by
    simpa [__anodized_fn_requires_bin_search, e02.anodized.__.eval,
      __anodized_fn_requires_bin_search.closure.Insts.CoreOpsFunctionFnTupleBool.call] using pre
  have adj : ∀ i, 0 < i → i < s.length → s[i - 1]! ≤ s[i]! := by
    have h := slice_sorted_adjacent s
    rw [sorted_pre, Std.WP.spec_ok] at h
    exact h rfl
  have sorted := adjacent_implies_sorted s adj
  unfold bin_search
  apply Std.WP.spec_mono (bin_search_loop_correct s v 0#usize (Aeneas.Std.Slice.len s)
    (by simp) sorted (by simp [Aeneas.Std.Slice.length]; omega))
  intro r hr
  rw [ensures_eq]
  cases r with
  | some i =>
    simp only [__anodized_fn_ensures_bin_search.closure_1.closure.Insts.CoreOpsFunctionFnTupleBool.call]
    change (if i < Aeneas.Std.Slice.len s then (do let x ← s.index_usize i; ok (x = v)) else ok false) = ok true
    have hi : i < Aeneas.Std.Slice.len s := by scalar_tac
    simp only [hi, ↓reduceIte]
    simp [Aeneas.Std.Slice.index_usize] at *
    simp_all
  | none =>
    simp only [__anodized_fn_ensures_bin_search.closure_1.closure.Insts.CoreOpsFunctionFnTupleBool.call]
    change (do let b ← core.slice.Slice.contains core.cmp.PartialEqI32 s v; ok (!b)) = ok true
    rw [contains_eq]
    simp
    intro hmem
    obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp hmem
    have hn := hr i hi
    apply hn
    simp_lists [heq]
