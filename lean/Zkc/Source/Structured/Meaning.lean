module

public import Zkc.Source.Structured.CheckedData
public import Zkc.Source.Structured.Evaluation

@[expose] public section

/-! Named helper closures and closed views of the uniform mathematical meaning.
The arithmetic/control evaluator is shared with open roots. -/

set_option autoImplicit false
namespace Zkc.Source.Structured

namespace Evaluation

variable {F G : Type} {interface : PIR.Signature}
variable [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]

/-- Each body closes over the previously interpreted prefix, so recursion is
impossible and helper syntax is never inlined into callers. -/
def extendMeanings (observations : SiteObservations interface)
    (table : Meanings F G interface) (definition : CheckedDefinition) :
    Meanings F G interface :=
  ⟨definition.helper, fun values =>
    definition.body.denote (meaning observations table) values.get⟩ :: table

def payloadMeanings (observations : SiteObservations interface) (payload : Payload) :
    Meanings F G interface :=
  payload.definitions.foldl (extendMeanings observations) []

def payloadDenote (observations : SiteObservations interface) (payload : Payload)
    (inputs : Values (assignment F G) payload.entry.inputs) :
    PIR.Proc interface (Values (assignment F G) payload.entry.outputs) :=
  payload.entry.body.denote (meaning observations (payloadMeanings observations payload)) inputs.get

end Evaluation

abbrev Meanings (F G : Type) := Evaluation.Meanings F G closedInterface

abbrev meaning (F G : Type) [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] :=
  Evaluation.meaning (F := F) (G := G) SiteObservations.closed

def Payload.meanings (payload : Payload) (F G : Type)
    [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] : Meanings F G :=
  Evaluation.payloadMeanings SiteObservations.closed payload

def Payload.denote (payload : Payload) (F G : Type)
    [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]
    (inputs : Values (assignment F G) payload.entry.inputs) :
    Closed (Values (assignment F G) payload.entry.outputs) :=
  Evaluation.payloadDenote SiteObservations.closed payload inputs

def closedOutcome {A : Type} : Closed A → PIR.Outcome A
  | .done value => .returned value
  | .halt reason => .stopped reason
  | .call impossible _ => nomatch impossible

end Zkc.Source.Structured
