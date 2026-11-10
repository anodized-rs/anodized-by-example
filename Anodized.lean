import Aeneas

/-- Tag every extracted `__anodized_fn_{requires,ensures}_*` declaration with `@[step_simps]`
so that `step*` unfolds the spec predicates (and their closure machinery, which shares the
name prefix) automatically — avoiding manual `unfold __anodized_fn_ensures_… .closure.…call`.

Call once per proof file, *after* importing the crate's translation. Idempotent: re-tagging
a declaration is a no-op, so calling it from several files is harmless. -/
elab "register_anodized_simps" : command => do
  let env ← Lean.getEnv
  let mut ids : Array Lean.Ident := #[]
  for (n, _) in env.constants.toList do
    let s := n.toString
    if (s.splitOn "__anodized_fn_ensures").length ≥ 2 ||
       (s.splitOn "__anodized_fn_requires").length ≥ 2 then
      ids := ids.push (Lean.mkIdent n)
  if ids.isEmpty then return
  Lean.Elab.Command.elabCommand (← `(attribute [step_simps] $ids*))

