module

public meta import ZkcTools.Companions

public meta section

/-! Method selection for one already-fixed authoring obligation. An explicit
companion overrides ordered default proposals. A missing companion permits the
defaults; an incomplete or ill-typed explicit companion does not silently change
method. These are authoring results, never canonical receipt statuses. -/
set_option autoImplicit false
namespace ZkcTools.Companions
open Lean Meta Elab Term

structure DefaultMethod where
  name : String
  proof : TSyntax `term

structure Attempt where
  method : String
  reason : String
  deriving ToJson

inductive Assembly where
  | discharged (value : Expr) (method : String) (attempts : Array Attempt)
  | openObligation (reason : String) (attempts : Array Attempt)
  | refused (reason : String) (attempts : Array Attempt)

/-- A proposer may use any Lean method. It must return the requested type,
without residual metavariables or a transitive `sorry`. The final declaration
still passes the kernel, and the owning receipt audit still checks assumptions. -/
def assemble (selections : Array Selection) (expected : Expr)
    (defaults : Array DefaultMethod) : TermElabM Assembly := do
  let expected ← instantiateMVars expected
  if expected.hasExprMVar then
    throwError "companion assembly requires the complete expected type before proof selection"
  match ← resolve selections expected with
  | .matched identity _ value => return .discharged value ("companion:" ++ identity) #[]
  | .incomplete identity _ reason => return .openObligation reason #[⟨"companion:" ++ identity, reason⟩]
  | .refused identity reason => return .refused reason #[⟨"companion:" ++ identity, reason⟩]
  | .missing => pure ()
  let mut attempts : Array Attempt := #[]
  for method in defaults do
    let saved ← saveState
    try
      let value ← Term.withoutErrToSorry <| elabTermEnsuringType method.proof expected
      Term.synthesizeSyntheticMVarsNoPostponing
      let value ← instantiateMVars value
      if value.hasMVar then throwError "default method leaves unsolved arguments"
      for used in value.getUsedConstants do
        if (← collectAxioms used).contains ``sorryAx then
          throwError "default method depends on sorry"
      return .discharged value method.name attempts
    catch error =>
      if error.isRuntime then throw error
      if let .internal _ _ := error then throw error
      let reason ← error.toMessageData.toString
      saved.restore
      attempts := attempts.push ⟨method.name, reason⟩
  return .openObligation "no available method discharged the fixed obligation" attempts

end ZkcTools.Companions
