import examples.e02.translation.Funs

/-! Binary search correctness, conditional on consistent Rust comparison and equality
and soundness of the extracted sortedness check. These are explicit hypotheses
of the final theorem. -/

open Aeneas Std Result
open e02

theorem bin_search_loop_body_done {T : Type} (ord : core.cmp.Ord T)
    (s : Aeneas.Std.Slice T) (v : T) (lo hi : Std.Usize) (h : ¬ lo < hi) :
    bin_search_loop.body
      ord s v lo hi = ok (.done none) := by
  simp [bin_search_loop.body, h]

theorem midpoint_bounds (lo hi : Nat) (h : lo < hi) :
  lo ≤ lo + (hi - lo) / 2 ∧ lo + (hi - lo) / 2 < hi := by omega

theorem bin_search_body_progress {T : Type} (ord : core.cmp.Ord T) (s : Aeneas.Std.Slice T) (v : T)
    (lo hi : Std.Usize) (bounds : lo.val < hi.val ∧ hi.val ≤ s.length)
    (cmp_ok : ∀ x, (ord.cmp x v) ⦃ _ => True ⦄) :
    (bin_search_loop.body
      ord s v lo hi) ⦃ r => match r with
      | .cont (l, h) => l.val ≤ h.val ∧ h.val ≤ s.length ∧ h.val - l.val < hi.val - lo.val
      | .done (some i) => i.val < s.length
      | .done none => False ⦄ := by
  unfold bin_search_loop.body
  step* <;> omega


theorem bin_search_loop_terminates {T : Type} (ord : core.cmp.Ord T)
    (s : Aeneas.Std.Slice T) (v : T) (lo hi : Std.Usize)
    (bounds : lo.val ≤ hi.val ∧ hi.val ≤ s.length)
    (cmp_ok : ∀ x, (ord.cmp x v) ⦃ _ => True ⦄) :
    (bin_search_loop
      ord s v lo hi) ⦃ _ => True ⦄ := by
  unfold bin_search_loop
  apply Std.loop.spec_decr_nat
    (measure := fun p => p.2.val - p.1.val)
    (inv := fun p => p.1.val ≤ p.2.val ∧ p.2.val ≤ s.length)
  · rintro ⟨l, h⟩ ⟨hle, hbound⟩
    by_cases hlt : l.val < h.val
    · apply Std.WP.spec_mono (bin_search_body_progress ord s v l h ⟨hlt, hbound⟩ cmp_ok)
      intro r hr
      cases r with
      | cont p => rcases p with ⟨a, b⟩; exact ⟨⟨hr.1, hr.2.1⟩, hr.2.2⟩
      | done r => trivial
    · dsimp only
      rw [bin_search_loop_body_done ord s v l h (by scalar_tac)]
      simp
  · exact bounds

theorem bin_search_body_correct {T : Type} [LinearOrder T] [Inhabited T] (ord : core.cmp.Ord T)
    (s : Aeneas.Std.Slice T) (v : T) (lo hi : Std.Usize)
    (bounds : lo.val < hi.val ∧ hi.val ≤ s.length)
    (sorted : ∀ i j, i < s.length → j < s.length → i ≤ j → s[i]! ≤ s[j]!)
    (excluded : ∀ i, i < s.length → (i < lo.val ∨ hi.val ≤ i) → s[i]! ≠ v)
    (cmp_ok : ∀ x, (ord.cmp x v) ⦃ o => (o = .lt → x < v) ∧ (o = .eq → x = v) ∧ (o = .gt → v < x) ⦄) :
    (bin_search_loop.body
      ord s v lo hi) ⦃ r => match r with
      | .cont (l, h) => ∀ i, i < s.length → (i < l.val ∨ h.val ≤ i) → s[i]! ≠ v
      | .done (some i) => i.val < s.length ∧ s[i.val]! = v
      | .done none => False ⦄ := by
  unfold bin_search_loop.body
  step*
  all_goals simp_all
  · intro j hj hjout
    have hm : lo.val + (hi.val - lo.val) / 2 < s.val.length := by
      simp only [Aeneas.Std.Slice.length] at bounds
      omega
    rcases hjout with hjle | hjge
    · have hs := sorted j (lo.val + (hi.val - lo.val) / 2) hj hm hjle
      exact _root_.ne_of_lt (_root_.lt_of_le_of_lt hs o_post)
    · exact excluded j hj (Or.inr hjge)
  · have hm : lo.val + (hi.val - lo.val) / 2 < s.val.length := by
      simp only [Aeneas.Std.Slice.length] at bounds
      omega
    simp [hm]
  · intro j hj hjout
    have hm : lo.val + (hi.val - lo.val) / 2 < s.val.length := by
      simp only [Aeneas.Std.Slice.length] at bounds
      omega
    rcases hjout with hjlt | hjge
    · exact excluded j hj (Or.inl hjlt)
    · have hs := sorted (lo.val + (hi.val - lo.val) / 2) j hm hj hjge
      exact _root_.ne_of_gt (_root_.lt_of_lt_of_le o_post2 hs)


theorem bin_search_loop_correct {T : Type} [LinearOrder T] [Inhabited T]
    (ord : core.cmp.Ord T) (s : Aeneas.Std.Slice T) (v : T) (lo hi : Std.Usize)
    (bounds : lo.val ≤ hi.val ∧ hi.val ≤ s.length)
    (sorted : ∀ i j, i < s.length → j < s.length → i ≤ j → s[i]! ≤ s[j]!)
    (excluded : ∀ i, i < s.length → (i < lo.val ∨ hi.val ≤ i) → s[i]! ≠ v)
    (cmp_ok : ∀ x, (ord.cmp x v) ⦃ o => (o = .lt → x < v) ∧ (o = .eq → x = v) ∧ (o = .gt → v < x) ⦄) :
    (bin_search_loop
      ord s v lo hi) ⦃ r => match r with
      | some i => i.val < s.length ∧ s[i.val]! = v
      | none => ∀ i, i < s.length → s[i]! ≠ v ⦄ := by
  have cmp_total (x : T) : (ord.cmp x v) ⦃ _ => True ⦄ := by
    apply Std.WP.spec_mono (cmp_ok x)
    intros; trivial
  unfold bin_search_loop
  apply Std.loop.spec_decr_nat
    (measure := fun p => p.2.val - p.1.val)
    (inv := fun p => p.1.val ≤ p.2.val ∧ p.2.val ≤ s.length ∧
      ∀ i, i < s.length → (i < p.1.val ∨ p.2.val ≤ i) → s[i]! ≠ v)
  · rintro ⟨l, h⟩ ⟨hle, hbound, hexcluded⟩
    by_cases hlt : l.val < h.val
    · have hp := bin_search_body_progress ord s v l h ⟨hlt, hbound⟩ cmp_total
      have hc := bin_search_body_correct ord s v l h ⟨hlt, hbound⟩ sorted hexcluded cmp_ok
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
      rw [bin_search_loop_body_done ord s v l h (by scalar_tac)]
      simp only [Std.WP.spec_ok]
      intro i hi
      apply hexcluded i hi
      simp only
      omega
  · exact ⟨bounds.1, bounds.2, excluded⟩

/-- Functional correctness under the supplied order and sortedness. -/
theorem bin_search_correct {T : Type} [LinearOrder T] [Inhabited T]
    (ord : core.cmp.Ord T) (s : Aeneas.Std.Slice T) (v : T)
    (sorted : ∀ i j, i < s.length → j < s.length → i ≤ j → s[i]! ≤ s[j]!)
    (cmp_ok : ∀ x, (ord.cmp x v) ⦃ o => (o = .lt → x < v) ∧ (o = .eq → x = v) ∧ (o = .gt → v < x) ⦄)
    :
    (bin_search ord s v) ⦃ r => match r with
      | some i => i.val < s.length ∧ s[i.val]! = v
      | none => ∀ i, i < s.length → s[i]! ≠ v ⦄ := by
  unfold bin_search
  exact bin_search_loop_correct ord s v 0#usize (Aeneas.Std.Slice.len s)
    (by simp) sorted (by simp [Aeneas.Std.Slice.length]; omega) cmp_ok

theorem contains_model_derived {T : Type} [DecidableEq T]
    (ord : core.cmp.Ord T) (s : Aeneas.Std.Slice T) (v : T)
    (heq : ∀ x y, ord.eqInst.partialEqInst.eq x y = ok (decide (x = y))) :
    core.slice.Slice.contains ord.eqInst.partialEqInst s v = ok (decide (v ∈ s.val)) := by
  unfold core.slice.Slice.contains
  induction s.val with
  | nil => rfl
  | cons a xs ih =>
    by_cases h : v = a <;> simp [List.anyM, heq, ih, h, pure]

/-- The extracted postcondition evaluates its predicate on the returned value. -/
theorem bin_search_ensures_eq {T : Type} (ord : core.cmp.Ord T)
    (s : Aeneas.Std.Slice T) (v : T) (r : Option Std.Usize) :
    __anodized_fn_ensures_bin_search ord s v r =
      __anodized_fn_ensures_bin_search.closure_1.closure.Insts.CoreOpsFunctionFnTupleBool.call
        ord (r, s, v) () := by
  simp [__anodized_fn_ensures_bin_search, e02.anodized.__.eval_once,
    e02.anodized.__.apply_keep, e02.anodized.__.eval,
    __anodized_fn_ensures_bin_search.closure.Insts.CoreOpsFunctionFnOnceTupleOptionUsize.call_once,
    __anodized_fn_ensures_bin_search.closure_1.Insts.CoreOpsFunctionFnTupleOptionUsizePairBoolOptionUsize.call]


theorem bin_search_contract {T : Type} [LinearOrder T] [Inhabited T]
    (ord : core.cmp.Ord T) (s : Aeneas.Std.Slice T) (v : T)
    (pre : __anodized_fn_requires_bin_search ord s v = ok true)
    (sorted_sound : slice_is_sorted ord s = ok true →
      ∀ i j, i < s.length → j < s.length → i ≤ j → s[i]! ≤ s[j]!)
    (cmp_ok : ∀ x, (ord.cmp x v) ⦃ o => (o = .lt → x < v) ∧ (o = .eq → x = v) ∧ (o = .gt → v < x) ⦄)
    (eq_model : ∀ x y, ord.eqInst.partialEqInst.eq x y = ok (decide (x = y))) :
    (bin_search ord s v) ⦃ r =>
      __anodized_fn_ensures_bin_search ord s v r = ok true ⦄ := by
  have sorted_pre : slice_is_sorted ord s = ok true := by
    simpa [__anodized_fn_requires_bin_search, e02.anodized.__.eval,
      __anodized_fn_requires_bin_search.closure.Insts.CoreOpsFunctionFnTupleBool.call] using pre
  apply Std.WP.spec_mono (bin_search_correct ord s v (sorted_sound sorted_pre) cmp_ok)
  intro r hr
  rw [bin_search_ensures_eq]
  cases r with
  | some i =>
    simp only [__anodized_fn_ensures_bin_search.closure_1.closure.Insts.CoreOpsFunctionFnTupleBool.call]
    change (if i < Aeneas.Std.Slice.len s then (do let x ← s.index_usize i; ord.eqInst.partialEqInst.eq x v) else ok false) = ok true
    have hi : i < Aeneas.Std.Slice.len s := by scalar_tac
    simp only [hi, ↓reduceIte]
    simp [Aeneas.Std.Slice.index_usize, eq_model] at *
    simp_all
  | none =>
    simp only [__anodized_fn_ensures_bin_search.closure_1.closure.Insts.CoreOpsFunctionFnTupleBool.call]
    change (do let b ← core.slice.Slice.contains ord.eqInst.partialEqInst s v; ok (!b)) = ok true
    rw [contains_model_derived ord s v eq_model]
    simp
    intro hmem
    obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp hmem
    have hn := hr i hi
    apply hn
    simp_lists [heq]
