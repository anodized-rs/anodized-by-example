import Obligations
import Anodized

open Aeneas Std.Result
open e01

register_anodized_simps
attribute [step_simps] e01.anodized.__.eval e01.anodized.__.eval_once
  e01.anodized.__.apply_keep

theorem f2_spec : Obligations.e01_f2 := by
  intro _
  unfold f2
  step*

theorem f4_spec : Obligations.e01_f4 := by
  intro x hx
  -- precondition `x > 0`
  simp only [step_simps] at hx
  unfold f4
  step*

