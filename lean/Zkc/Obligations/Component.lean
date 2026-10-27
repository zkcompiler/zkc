module

public import Zkc.Obligations.ClaimRelation
public import Zkc.Obligations.Derivation

public section

/-! Component contracts over the existing process semantics. Runtime dataflow
and mathematical readback are distinct. The body cannot inspect the logical
parameter assignment. Contracts and connections are explicit indexed evidence,
not type-class search or a second language of executable protocols.
-/

namespace Zkc.Obligations
open Zkc.Transcript

structure ComponentInterface (I : PIR.Signature) (Event Runtime Result : Type) where
  Parameters : Type
  Input : Type
  InputWitness : Type
  Output : Type
  OutputWitness : Type
  input : ClaimRelation Input InputWitness
  output : ClaimRelation Output OutputWitness
  body : Runtime → PIR.Process I Result
  Scope : Parameters → Runtime → List Event → Prop
  inputView : Parameters → Runtime → List Event → Option Input
  outputView : Parameters → Runtime → List Event → Result → Option Output

namespace ComponentInterface
variable {I : PIR.Signature} {E R A : Type}

@[expose] def InputYes (component : ComponentInterface I E R A)
    (parameters : component.Parameters) (runtime : R) (history : List E) : Prop :=
  ReadbackHolds component.input.token.Yes (component.inputView parameters runtime history)

@[expose] def OutputYes (component : ComponentInterface I E R A)
    (parameters : component.Parameters) (runtime : R) (history : List E) (value : A) : Prop :=
  ReadbackHolds component.output.token.Yes (component.outputView parameters runtime history value)

@[expose] def InputNo (component : ComponentInterface I E R A)
    (parameters : component.Parameters) (runtime : R) (history : List E) : Prop :=
  ReadbackHolds component.input.No (component.inputView parameters runtime history)

@[expose] def OutputNo (component : ComponentInterface I E R A)
    (parameters : component.Parameters) (runtime : R) (history : List E) (value : A) : Prop :=
  ReadbackHolds component.output.No (component.outputView parameters runtime history value)

end ComponentInterface

variable {I : PIR.Signature} {E P R A : Type} {Raw : E → Type}

/-- The family theorem is conditional on a checked scope and a defined input.
Callers must establish both at the actual occurrence. Completeness and scope
preservation are independent theorems indexed by the same component. -/
@[expose] def SoundnessContract (component : ComponentInterface I E R A)
    (absorb : Interface I E P Raw) (escape : EscapeJudgment E Raw) : Type 1 :=
  ∀ parameters runtime history, component.Scope parameters runtime history →
    component.InputNo parameters runtime history →
    Derivation absorb escape (component.OutputNo parameters runtime) history (component.body runtime)

namespace SoundnessContract

/-- Instantiate existing family mathematics through one exact body equation and
boundary implications. This does not pick a family, model or request meaning. -/
def ofFamily {component : ComponentInterface I E R A}
    {absorb : Interface I E P Raw} {escape : EscapeJudgment E Raw}
    (familyBody : R → PIR.Process I A)
    (binding : ∀ runtime, component.body runtime = familyBody runtime)
    (pre : component.Parameters → R → List E → Prop)
    (post : component.Parameters → R → List E → A → Prop)
    (enter : ∀ parameters runtime history, component.Scope parameters runtime history →
      component.InputNo parameters runtime history → pre parameters runtime history)
    (family : ∀ parameters runtime history, pre parameters runtime history →
      Derivation absorb escape (post parameters runtime) history (familyBody runtime))
    (exit : ∀ parameters runtime history value, post parameters runtime history value →
      component.OutputNo parameters runtime history value) :
    SoundnessContract component absorb escape :=
  fun parameters runtime history scope no =>
    ((family parameters runtime history (enter parameters runtime history scope no)).consequence
      (exit parameters runtime)).transport (binding runtime)

end SoundnessContract

/-- A pure seam maps actual runtime results and mathematical claims separately.
The square includes definedness of the next input. There are no effects in a
connection; a conversion requiring a query belongs to a component. -/
structure Connection {S B : Type}
    (first : ComponentInterface I E R A) (second : ComponentInterface I E S B) where
  parameters : first.Parameters → second.Parameters
  route : R → A → S
  map : first.Output → second.Input
  square : ∀ context runtime history value output,
    first.outputView context runtime history value = some output →
    second.inputView (parameters context) (route runtime value) history = some (map output)

namespace Connection
variable {S B : Type} {first : ComponentInterface I E R A}
  {second : ComponentInterface I E S B}

/-- Honest transport uses the same runtime route and readback square as sound
transport. Actual success and next-scope preservation are separate execution
obligations; this law neither runs the producer nor recovers a witness. -/
theorem input_yes (connection : Connection first second)
    (law : first.output.HonestLink second.input connection.map)
    {parameters : first.Parameters} {runtime : R} {history : List E} {value : A}
    (yes : first.OutputYes parameters runtime history value) :
    second.InputYes (connection.parameters parameters) (connection.route runtime value) history := by
  obtain ⟨output, defined, correct⟩ := yes
  exact ⟨connection.map output, connection.square parameters runtime history value output defined,
    law output correct⟩

theorem input_no (connection : Connection first second)
    (law : first.output.SoundLink second.input connection.map)
    {parameters : first.Parameters} {runtime : R} {history : List E} {value : A}
    (no : first.OutputNo parameters runtime history value) :
    second.InputNo (connection.parameters parameters) (connection.route runtime value) history := by
  obtain ⟨output, defined, wrong⟩ := no
  exact ⟨connection.map output, connection.square parameters runtime history value output defined,
    law output wrong⟩

/-- Compose at the actual reached history. The caller proves next-scope and
the final readback implication. Neither is inferred from matching carrier types.
The resulting derivation can be exported as another SoundnessContract. -/
def bind {absorb : Interface I E P Raw} {escape : EscapeJudgment E Raw}
    (connection : Connection first second)
    (law : first.output.SoundLink second.input connection.map)
    (head : SoundnessContract first absorb escape)
    (tail : SoundnessContract second absorb escape)
    (parameters : first.Parameters) (runtime : R) (history : List E)
    (scope : first.Scope parameters runtime history)
    (no : first.InputNo parameters runtime history)
    (nextScope : ∀ reached value, first.OutputNo parameters runtime reached value →
      second.Scope (connection.parameters parameters) (connection.route runtime value) reached)
    (post : List E → B → Prop)
    (exit : ∀ value reached result,
      second.OutputNo (connection.parameters parameters) (connection.route runtime value) reached result →
      post reached result) :
    Derivation absorb escape post history
      ((first.body runtime).bind fun value => second.body (connection.route runtime value)) :=
  (head parameters runtime history scope no).bind _ fun reached value wrong =>
    (tail (connection.parameters parameters) (connection.route runtime value) reached
      (nextScope reached value wrong) (connection.input_no law wrong)).consequence (exit value)

end Connection
end Zkc.Obligations
