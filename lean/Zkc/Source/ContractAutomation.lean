module

public import Zkc.Semantics.ExactRefinement
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FailIfNoProgress

@[expose] public section

/-! Reusable proof search for exposed open-process contract equations.

The caller chooses the contract and unfolds its definitions. This tactic only
proposes equality proofs: it recurses through the same effect constructor and
uses the established ring/group normalizers for pure leaves. It cannot invent
an experiment, an effect law or an unproved provider assumption. Unsupported
forms leave an ordinary Lean goal. No security theorem is selected here.
-/

macro "zkc_contract" : tactic => `(tactic|
  all_goals repeat' first
    | rfl
    | (apply PIR.Proc.call_congr; intro reply)
    | (solve | ring1)
    | (solve | abel1)
    | fail_if_no_progress congr 1)
