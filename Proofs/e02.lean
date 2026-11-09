import examples.e02.translation.Funs

/-! The binary-search proof is incomplete. This lemma establishes the loop's
exit case; the search invariant, ordering assumptions, and external Anodized
helper models are still needed to prove the full specification. -/

open Aeneas Std Result
open e02

theorem bin_search_loop_body_done {T : Type} (ord : core.cmp.Ord T)
    (s : Aeneas.Std.Slice T) (v : T) (lo hi : Std.Usize) (h : ¬ lo < hi) :
    bin_search.closure_1.Insts.CoreOpsFunctionFnOnceTupleOptionUsize.call_once_loop.body
      ord s v lo hi = ok (.done none) := by
  simp [bin_search.closure_1.Insts.CoreOpsFunctionFnOnceTupleOptionUsize.call_once_loop.body, h]
