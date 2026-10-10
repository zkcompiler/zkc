import Zkc.Source.Program
import Zkc.Semantics.Boundary

/-! Public interface-call bounds, conditional on uniform operation contracts.

Typing alone proves neither protocol phase conformance nor a machine resource
bound. This module counts interpreted interface calls, including both sides of
a branch conservatively and each public loop iteration.
-/

set_option autoImplicit false

namespace Zkc.Source

variable {language : Language} {interface : PIR.Signature}

def Program.callBound (operationBound : language.Op → Nat) {Γ ty} :
    Program language Γ ty → Nat
  | .ret _ | .stop _ => 0
  | .letOp op _ next => operationBound op + next.callBound operationBound
  | .branch _ yes no => max (yes.callBound operationBound) (no.callBound operationBound)
  | .iterate count _ body next =>
    count * body.callBound operationBound + next.callBound operationBound

theorem Program.denote_within (meaning : Interpretation language interface)
    (operationBound : language.Op → Nat)
    (operations : ∀ op args, PIR.Within (operationBound op) (meaning.operation op args))
    {Γ ty} (program : Program language Γ ty) (env : Environment meaning.Value Γ) :
    PIR.Within (program.callBound operationBound) (program.denote meaning env) := by
  induction program with
  | ret value => trivial
  | stop reason => trivial
  | letOp op arguments next ih =>
    exact PIR.Boundary.within_bind _ _ _ _ (operations op _) (fun value => ih (env.push value))
  | branch condition yes no yesIH noIH =>
    simp only [denote]
    split
    · exact PIR.Boundary.within_mono _ _ _ (Nat.le_max_left _ _) (yesIH env)
    · exact PIR.Boundary.within_mono _ _ _ (Nat.le_max_right _ _) (noIH env)
  | iterate count initial body next bodyIH nextIH =>
    exact PIR.Boundary.within_bind _ _ _ _
      (PIR.Boundary.repeat_bound _ _ (fun value => bodyIH (env.push value)) count _)
      (fun value => nextIH (env.push value))

end Zkc.Source
