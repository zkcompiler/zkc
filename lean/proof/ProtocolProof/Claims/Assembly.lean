module

public import ProtocolProof.Claims.Closure
public import ProtocolProof.Components.Representation

/-! Reusable exact installation constructors; the request and its observation remain fixed. -/

public section
open PIR MeasureTheory PFunctor

namespace ProtocolProof.Installation
variable {E : Type} {I : Signature} {S T L M : Type}
  [∀ op, MeasurableSpace (I.Reply op)]
  [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace L] [MeasurableSpace M]

/-- A total map on state and event history installs each operation and the whole initial law. -/
noncomputable def ofMap [MeasurableEq (T × List M)]
    (actual : System E I S L) (model : System E I T M)
    (admissible : E → Prop) (encode : E → (S × List L) → (T × List M))
    (hmeasurable : ∀ e, Measurable (encode e))
    (hlocal : ∀ e, admissible e → ∀ op s,
      (actual.accumulatedOperations e op s).map (fun out ↦ (out.1, encode e out.2)) =
        model.accumulatedOperations e op (encode e s))
    (hcoverage : ∀ e, admissible e →
      (actual.initialWithEvents e).map (encode e) = model.initialWithEvents e) :
    Installation actual model admissible (fun e s t ↦ encode e s = t) where
  operations e he := Representation.contractOfMap (actual.accumulatedOperations e)
    (model.accumulatedOperations e) (encode e) (hmeasurable e) (hlocal e he)
  initial e he := Representation.initial_of_map_eq (actual.initialWithEvents e)
    (model.initialWithEvents e) (encode e) (hmeasurable e) (hcoverage e he)

/-- An identity installation is reusable for every Process client of the fixed system. -/
noncomputable def reflexive [MeasurableEq (S × List L)] (system : System E I S L)
    (admissible : E → Prop) : Installation system system admissible (fun _ s t ↦ s = t) :=
  ofMap system system admissible (fun _ ↦ id) (fun _ ↦ measurable_id)
    (fun _ _ _ _ ↦ Measure.map_id) (fun _ _ ↦ Measure.map_id)

end ProtocolProof.Installation
