module

public import Zkc.Source.Structured.NormalizedRoot
public meta import ZkcTools.StructuredSource.Composition

/-! Composition must check complete branch results and every application. -/
section
variable {I : PIR.Signature} {A B C : Type}
  (first : PIR.Process I A) (next : A → PIR.Process I B)
  (finish : B → PIR.Process I C)

example (choice : Option Bool) :
    (match choice with
      | none => (first.bind next).bind finish
      | some enabled => if enabled then (first.bind next).bind finish
          else first.bind (fun value => (next value).bind finish)) =
    (match choice with
      | none => first.bind (fun value => (next value).bind finish)
      | some enabled => if enabled then first.bind (fun value => (next value).bind finish)
          else (first.bind next).bind finish) := by
  source_composition_equation atoms []

example (choice : Option Bool) :
    ((match choice with
      | none => first.bind next
      | some _ => first.bind next).bind finish) =
    (match choice with
      | none => first.bind (fun value => (next value).bind finish)
      | some _ => first.bind (fun value => (next value).bind finish)) := by
  source_composition_equation atoms []

example (value : A) : (PIR.Process.done value : PIR.Process I A) = .done value := by
  -- A failed proposal cannot authorize different complete returned values.
  fail_if_success
    have : (PIR.Process.done (true, value) : PIR.Process I (Bool × A)) = .done (false, value) := by
      source_composition_equation atoms []
  rfl
end

section
open Zkc.Source Zkc.Source.Structured
variable {I : PIR.Signature} {Value : Ty → Type} {ty : Ty}
example (process : PIR.Process I (Values Value [ty])) :
    (process.bind fun out => .done (.cons (out.get .here) .nil)) = process := by
  source_composition_equation atoms []
end

/- The actual template matcher's recovery boundary permits ordinary mismatch,
rolls back speculative assignments, and propagates implementation failures. -/
open Lean Meta Elab Command ZkcTools.StructuredSource.Composition in
run_elab do
  let failureId ← Lean.registerInternalExceptionId `sourceCompositionControl
  let pending ← mkFreshExprMVar (mkConst ``Nat)
  let missing ← attemptTemplate (α := Nat) do
    pending.mvarId!.assign (mkNatLit 7)
    throwError "ordinary template mismatch"
  unless missing.isNone && !(← pending.mvarId!.isAssigned) do
    throwError "template mismatch did not restore speculative assignments"
  let selected ← attemptTemplate (pure (11 : Nat))
  unless selected == some 11 do throwError "matching template was not retained"
  let propagated ← try
    let _ ← attemptTemplate (α := Nat) do
      throw (.internal failureId)
    pure false
  catch error =>
    match error with
    | .internal id _ =>
      if id == failureId then pure true else throw error
    | .error .. => throw error
  unless propagated do throwError "internal template failure was swallowed"
