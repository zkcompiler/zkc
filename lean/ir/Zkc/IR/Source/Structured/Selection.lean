module

public import Zkc.IR.Source.Structured.ProtocolOperations
public import Zkc.IR.Source.Structured.ProtocolScopes

@[expose] public section

namespace Zkc.Source.Structured

/-- The selected callback keeps the actual captures, effects and stops. Absence
of an active selector is incomplete; an inactive participant executes neither arm. -/
def denoteBranch {V : Ty → Type} {I : PIR.Signature}
    (condition : V .boolean → Option Bool) (spec : BranchSpec)
    (context : ProtocolContext) (self : Nat) (selector : Component V .boolean)
    (captures : Values (Component V) spec.captures)
    (yes no : RegionFunction (Component V) I (spec.captures, spec.outputs)) :
    PIR.Process I (Values (Component V) spec.outputs) :=
  if (spec.roles.map context.roles).contains self then
    match selector.bind condition with
    | none => .halt .incomplete
    | some selected =>
      (if selected then yes captures else no captures).bind fun results ↦
        .done (maskValues self (context.mapScopes spec.outputScopes) results)
  else .done (Values.absent V spec.outputs)

/-- Interpretation commutes with the selected arm and cannot execute the other arm. -/
theorem denoteBranch_interpret {V : Ty → Type} {I J : PIR.Signature}
    (operations : PIR.OperationInterpretation I J)
    (condition : V .boolean → Option Bool) (spec : BranchSpec)
    (context : ProtocolContext) (self : Nat) (selector : Component V .boolean)
    (captures : Values (Component V) spec.captures)
    (yes no : RegionFunction (Component V) I (spec.captures, spec.outputs)) :
    (denoteBranch condition spec context self selector captures yes no).interpret operations =
      denoteBranch condition spec context self selector captures
        (fun values ↦ (yes values).interpret operations)
        (fun values ↦ (no values).interpret operations) := by
  unfold denoteBranch
  split
  · cases selector.bind condition with
    | none => rfl
    | some selected =>
      cases selected <;> simp only [Bool.false_eq_true, ↓reduceIte,
        PIR.Process.interpret_bind, PIR.Process.interpret]
  · rfl

end Zkc.Source.Structured
