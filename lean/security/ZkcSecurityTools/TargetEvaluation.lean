module

public import ZkcSecurity.Bindings.Subjects.ABI
public import Zkc.Construction.TargetElaboration
public import Zkc.Source.Structured.Algebra
public meta import Mathlib.Tactic.Tauto
public meta import ZkcSecurityTools.InputLaws

@[expose] public meta section

/-! Close a concrete retained target from its checked argument read and a
mathematical formula equation. Both laws are explicit inputs, and every extra
evaluation premise must be proved. The result remains the actual source target;
no independently chosen proposition replaces it. -/
namespace ZkcSecurity.Tools.TargetEvaluation

open Lean Meta Elab Tactic

elab "prove_retained_target " "[" scalar:term "," group:term "]"
    " reading " read:term " evaluating " equation:term " solving " side:tactic : tactic =>
    withMainContext <| Term.withoutErrToSorry <| withoutRecover do
  let pending := (← getGoals).tail
  setGoals [(← getMainGoal)]
  evalTactic (← `(tactic|
    first
    | apply (ZkcSecurity.Claims.Domain.Subject.holds_iff_of_read _ _ _ _ $read).mpr
    | apply (ZkcSecurity.Claims.HonestPair.Subject.relation_iff_of_read _ _ _ $read).mpr))
  evalTactic (← `(tactic|
    rw [Zkc.Source.Structured.RelationMeaning.formula_exact _ (by bind_contract)]))
  evalTactic (← `(tactic| erw [$equation:term]))
  for goal in ← getGoals do
    setGoals [goal]
    let saved ← saveState
    let mut sideError : MessageData := m!"side tactic left goals"
    let solved ← try
      evalTactic side
      pure (← getGoals).isEmpty
    catch error =>
      sideError := error.toMessageData
      pure false
    if !solved then
      saved.restore
      try
        evalTactic (← `(tactic|
          change _ = (PIR.Process.done (.cons true .nil) :
            Zkc.Source.Structured.Closed (Zkc.Source.Values
              (Zkc.Source.Structured.assignment $scalar $group) [.boolean]))))
        let steps ← #[
          `(tactic| simp only [PIR.Process.done.injEq]),
          `(tactic| change ((Zkc.Source.Values.cons _ .nil : Zkc.Source.Values
            (Zkc.Source.Structured.assignment $scalar $group) [.boolean]) = .cons true .nil)),
          `(tactic| simp only [Zkc.Source.Values.cons.injEq, and_true, Bool.and_eq_true, decide_eq_true_eq]),
          `(tactic| first | rfl | tauto)].mapM id
        for step in steps do
          unless (← getGoals).isEmpty do evalTactic step
      catch error =>
        throwError "target evaluation failed: {error.toMessageData}\nside condition: {sideError}"
    unless (← getGoals).isEmpty do throwError "target evaluation remains unproved"
  setGoals pending

/-- Derive honest mathematical facts from the same retained formula equation
used by adversarial assembly. The policy supplies evaluation premises only on
the honest side. No root-specific relation-transport theorem is required. -/
elab "prepare_target_readback " "[" scalar:term "," group:term "]"
    " for " subject:term " using " policy:term " reading " read:term
    " evaluating " equation:term : tactic =>
    withMainContext <| Term.withoutErrToSorry <| withoutRecover do
  let pending := (← getGoals).tail
  setGoals [(← getMainGoal)]
  let _ ← InputLaws.forwardIff policy
  InputLaws.splitFacts
  let law ← `(ZkcSecurity.Claims.HonestPair.Subject.relation_iff_of_read
    $subject _ _ $read)
  let fact ← InputLaws.forwardIff law
  withMainContext do
    let name := mkIdent (← fact.getDecl).userName
    evalTactic (← `(tactic|
      rw [Zkc.Source.Structured.RelationMeaning.formula_exact _ (by bind_contract)] at $name:ident))
    evalTactic (← `(tactic| erw [$equation:term] at $name:ident))
    let main ← getMainGoal
    for premise in (← getGoals).tail do
      premise.assumption
    setGoals [main]
    evalTactic (← `(tactic|
      change _ = (PIR.Process.done (.cons true .nil) : Zkc.Source.Structured.Closed
        (Zkc.Source.Values (Zkc.Source.Structured.assignment $scalar $group) [.boolean])) at $name:ident))
    evalTactic (← `(tactic| simp only [PIR.Process.done.injEq] at $name:ident))
    evalTactic (← `(tactic|
      change ((Zkc.Source.Values.cons _ .nil : Zkc.Source.Values
        (Zkc.Source.Structured.assignment $scalar $group) [.boolean]) = .cons true .nil) at $name:ident))
    evalTactic (← `(tactic|
      simp only [Zkc.Source.Values.cons.injEq, and_true, Bool.and_eq_true, decide_eq_true_eq] at $name:ident))
  InputLaws.splitFacts
  evalTactic (← `(tactic| subst_vars))
  setGoals ((← getGoals) ++ pending)

end ZkcSecurity.Tools.TargetEvaluation
