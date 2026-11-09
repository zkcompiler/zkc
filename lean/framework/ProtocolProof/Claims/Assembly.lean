module

public import ProtocolProof.Claims.Closure
public import ProtocolProof.Components.Representation

/-!
# Reusable assembly helpers

These constructors discharge structural fields once. Authors supply a meaningful state map
and local meaning laws, or reuse an existing connection. Neither the request nor its terminal
claim is synthesized from the evidence. The raw evidence records remain available for other
valid proof methods.
-/

public section

open MeasureTheory PFunctor

universe uE uA uB uS uT

namespace ProtocolProof.Connection

variable {E : Type uE} {P : PFunctor.{uA, uB}} {S : Type uS} {T : Type uT}
  [∀ a, MeasurableSpace (P.B a)] [MeasurableSpace S] [MeasurableSpace T]
  [MeasurableEq T]

/-- One total state representation installs every component operation and covers the root. -/
noncomputable def ofMap (actual : System E P S) (model : System E P T)
    (admissible : E → Prop) (encode : E → S → T)
    (hmeasurable : ∀ e, Measurable (encode e))
    (hlocal : ∀ e, admissible e → ∀ a s,
      (actual.operations e a s).map (fun out ↦ (out.1, encode e out.2)) =
        model.operations e a (encode e s))
    (hcoverage : ∀ e, admissible e → (actual.initial e).map (encode e) = model.initial e) :
    Connection actual model admissible (fun e s t ↦ encode e s = t) where
  operations e he := Representation.contractOfMap (actual.operations e) (model.operations e)
    (encode e) (hmeasurable e) (hlocal e he)
  initial e he := Representation.initial_of_map_eq (actual.initial e) (model.initial e)
    (encode e) (hmeasurable e) (hcoverage e he)

/-- Identical services and initial laws need no authored connection proof. -/
noncomputable def reflexive [MeasurableEq S] (system : System E P S)
    (admissible : E → Prop) : Connection system system admissible (fun _ s t ↦ s = t) :=
  ofMap system system admissible (fun _ ↦ id) (fun _ ↦ measurable_id)
    (fun _ _ _ _ ↦ Measure.map_id) (fun _ _ ↦ Measure.map_id)

end ProtocolProof.Connection
