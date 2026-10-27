module

public import Zkc.Obligations.Component

public section

/-! Structural assembly is a library of rules over actual Process bind, not a
second interpreter. The independent prefix law is essential when only a later
claim is false. Root coverage and the final acceptance law remain explicit.
-/

namespace Zkc.Obligations.Assembly
open Zkc.Transcript

variable {I : PIR.Signature} {E P A B C : Type} {Raw : E → Type}
  {absorb : Interface I E P Raw} {escape : EscapeJudgment E Raw}

/-- A two-claim conjunction. Actual return values, reached histories, stops and
continuation effects are retained. `frame` must hold independently of either
claim's falsity; an input-No-conditioned family result cannot supply it.

This rule is independent of the family, representation, error distribution and
acceptance encoding. More than two claims reuse it through composite contracts;
loops use Derivation.repeatN rather than being flattened into call lists. -/
noncomputable def rejection
    (first : PIR.Process I A) (next : A → PIR.Process I B)
    (finish : A → B → PIR.Process I C)
    (Left Right : Prop) (Frame LeftRejected : A → Prop) (RightRejected : B → Prop)
    (Post : List E → C → Prop) (history : List E)
    (covered : ¬ (Left ∧ Right))
    (frame : Derivation absorb escape (fun _ value => Frame value) history first)
    (left : ¬ Left → Derivation absorb escape
      (fun _ value => Frame value ∧ LeftRejected value) history first)
    (right : ¬ Right → ∀ reached value, Frame value →
      Derivation absorb escape (fun _ result => RightRejected result) reached (next value))
    (pass : ∀ reached value, Frame value →
      Derivation absorb escape (fun _ _ => True) reached (next value))
    (terminal : ∀ reached value result, LeftRejected value ∨ RightRejected result →
      Derivation absorb escape Post reached (finish value result)) :
    Derivation absorb escape Post history (first.bind fun value => (next value).bind (finish value)) := by
  classical
  by_cases holds : Left
  · have wrong : ¬ Right := fun yes => covered ⟨holds, yes⟩
    exact frame.bind _ fun reached value preserved =>
      (right wrong reached value preserved).bind _ fun final result rejected =>
        terminal final value result (.inr rejected)
  · exact (left holds).bind _ fun reached value preserved =>
      (pass reached value preserved.1).bind _ fun final result _ =>
        terminal final value result (.inl preserved.2)

/-- A returned-state law can be used on a claim-free or true prefix. Its proof
does not depend on a mathematical No premise. `unrestricted` is supplied by
the selected escape interpretation, keeping probability out of this module. -/
noncomputable def preserve {first : PIR.Process I A} {history : List E}
    (interaction : PIR.Interaction I) (phase : interaction.Phase) (Frame : A → Prop)
    (returns : PIR.Boundary.Returns interaction (fun value _ => Frame value) first phase)
    (unrestricted : Derivation absorb escape (fun _ _ => True) history first) :
    Derivation absorb escape (fun _ value => Frame value) history first :=
  (unrestricted.frameReturns interaction Frame phase returns).consequence fun _ _ holds => holds.2

end Zkc.Obligations.Assembly
