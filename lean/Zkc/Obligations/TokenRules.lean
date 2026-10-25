module

public import Zkc.Obligations.Token
public import Zkc.Obligations.Derivation

public section

/-! Token rules use established facts separately from live promises. The
direction of entry and exit is backward safety; a promise gap stays a gap.
-/

set_option autoImplicit false
namespace Zkc.Obligations.Derivation
open Zkc.Transcript
variable {I : PIR.Signature} {E P A S : Type} {Raw : E → Type}
  {absorb : Interface I E P Raw} {escape : EscapeJudgment E Raw}

def backwardReturn {before : Bundle S} {after : Bundle A} {transition : S → A → Prop}
    (law : Bundle.Backward before after transition) {old : S} {returned : A}
    (actual : transition old returned) (bad : before.Doomed old) (history : List E) :
    Derivation absorb escape (fun _ value => after.Doomed value) history (.done returned) :=
  .done (law.doomed actual bad)

/-- A framed call transports all live No obligations through the actual
callee relation. Both the body and frame laws are required at every reached
history. The binding is an equation over the whole callee process. -/
def callTokens {B : Type} {before frameBefore : Bundle S} {after frameAfter : Bundle A}
    {actual component : PIR.Process I A} (binding : actual = component)
    (transition : List E → S → A → Prop)
    (bodyLaw : ∀ reached, Bundle.Backward before after (transition reached))
    (frameLaw : ∀ reached, Bundle.Backward frameBefore frameAfter (transition reached))
    (old : S) (bad : (before ++ frameBefore).Doomed old) (history : List E)
    (callee : Derivation absorb escape (fun reached value => transition reached old value) history component)
    (next : A → PIR.Process I B) {Final : List E → B → Prop}
    (seam : ∀ reached value, (after ++ frameAfter).Doomed value →
      Derivation absorb escape Final reached (next value)) :
    Derivation absorb escape Final history (actual.bind next) :=
  call binding
    (callee.consequence fun reached _ taken => ((bodyLaw reached).frame (frameLaw reached)).doomed taken bad)
    next seam

/-- Separate entry, body and exit obligations at the actual carried states.
For zero rounds only entry and exit are used.
-/
def repeatTokens (step : A → PIR.Process I A)
    (facts : List E → Nat → A → Prop) (cut : List E → Nat → Bundle A)
    (incoming outgoing : Bundle A) (count : Nat)
    (entry : ∀ history value, facts history count value →
      Bundle.Backward incoming (cut history count) (fun old new => old = value ∧ new = value))
    (body : ∀ history remaining value, facts history (remaining + 1) value →
      (cut history (remaining + 1)).Doomed value →
      Derivation absorb escape
        (fun reached result => facts reached remaining result ∧ (cut reached remaining).Doomed result)
        history (step value))
    (exit : ∀ history value, facts history 0 value →
      Bundle.Backward (cut history 0) outgoing (fun old new => old = value ∧ new = value))
    (history : List E) (value : A) (established : facts history count value)
    (bad : incoming.Doomed value) :
    Derivation absorb escape (fun _ result => outgoing.Doomed result) history
      (PIR.repeatN count step value) :=
  (repeatN step
    (fun reached remaining result => facts reached remaining result ∧ (cut reached remaining).Doomed result)
    (fun reached remaining result valid => body reached remaining result valid.1 valid.2)
    count history value ⟨established, (entry history value established).doomed ⟨rfl, rfl⟩ bad⟩).consequence
    (fun reached result valid => (exit reached result valid.1).doomed ⟨rfl, rfl⟩ valid.2)

end Zkc.Obligations.Derivation
