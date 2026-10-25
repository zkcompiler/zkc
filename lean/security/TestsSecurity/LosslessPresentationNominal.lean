module

import ZkcSecurity.Families.Sumcheck.TableComponentNominalLossless

set_option autoImplicit false
namespace TestsSecurity.LosslessPresentationNominal
open Zkc.Source Zkc.Source.Structured Zkc.Construction Zkc.Transcript
open ZkcSecurity.FiatShamir ZkcSecurity.FiatShamir.Original
open ZkcSecurity.Families.Sumcheck.TableComponent

variable {F G : Type}

def origin (field : String) : Origin :=
  .query "lossless" "challenge" "random" "uniform" "validator" (.draw field)

def frame (field : String) (raw : F) : Domain.Environment (uniformCarriers F G) :=
  [.data (.field field raw), .data (.index 7)]

def source (field : String) (history : Domain.History (uniformCarriers F G)) :
    PIR.Process (Domain.effects (uniformCarriers F G)) Unit :=
  .call (.checkpoint []) fun _ =>
    .call (.query history (origin field)) fun _ => .done ()

def target (field : String) (history : Domain.History (uniformCarriers F G)) :
    PIR.Process (Domain.effects (uniformCarriers F G)) (F × Domain.Environment (uniformCarriers F G)) :=
  .call (.checkpoint [.data (.index 3)]) fun _ =>
    .call (.checkpoint []) fun _ =>
      .call (.query history (origin field)) fun raw =>
        .call (.checkpoint (frame field raw)) fun _ => .done (raw, frame field raw)

def presented (field : String) : PIR.Process (Nominal.signature F field) Unit :=
  .call (.query (origin field) rfl) fun _ => .done ()

def bridge (field : String) (history : Domain.History (uniformCarriers F G)) :
    Original.Bridge (Nominal.interface (G := G) field) (fun _ _ => True) history
      (source field history) (target field history) (presented field)
      (fun _ result => result.2 = frame field result.1) (fun _ _ => True) where
  sourceReading := by
    constructor
    · apply DomainReduction.ReadingTo.checkpoint []
      exact .query (I := Nominal.signature F field) history (origin field) _ (.query (origin field) rfl) _ id rfl rfl
        (fun _ => .done _ _ trivial)
    · exact .checkpoint [] (.query history (origin field) _ rfl (fun _ => .done _ _ trivial))
  simulation := by
    apply Zkc.Construction.Original.Simulation.checkpoint [.data (.index 3)] trivial
    apply Zkc.Construction.Original.Simulation.call (.checkpoint [])
    intro _
    apply Zkc.Construction.Original.Simulation.call (.query history (origin field))
    intro raw
    exact .checkpoint (frame field raw) trivial (.done rfl)

/-- The full target environment depends on the query reply, while every source
return is Unit. Lossless lifting requires no full-result encoder from Unit. -/
example [Field F] (field : String) (history : Domain.History (uniformCarriers F G)) :
    ∃ after : PIR.Process (Nominal.signature F field) (F × Domain.Environment (uniformCarriers F G)),
      Alignment (fun _ result => result.2 = frame field result.1) (presented field) after ∧
      DomainReduction.Bridge (Nominal.interface (G := G) field)
        (fun _ result => ∃ _a : Unit, True ∧ result.2 = frame field result.1)
        history (target field history) after :=
  (bridge field history).exists_lossless_presentation (Nominal.lossless field)

example [Field F] (field : String) :
    ¬ ∃ realize : Unit → F × Domain.Environment (uniformCarriers F G),
      ∀ raw : F, realize () = (raw, frame field raw) := by
  rintro ⟨realize, exactReturn⟩
  have impossible := congrArg Prod.fst ((exactReturn 0).symm.trans (exactReturn 1))
  exact zero_ne_one impossible

/-- An actual receive/observe branch retains the exact payload history. -/
theorem receiveBridge (field : String) (whereAt : Origin) (history : Domain.History (uniformCarriers F G)) :
    DomainReduction.Bridge (Nominal.interface (F := F) (G := G) field) (fun _ _ => True) history
      (.call (.receive (.field field) "message" "schema" "prover") fun value =>
        .call (.observe (.message whereAt (.field field value))) fun _ => .done value)
      (.call (.receive whereAt) fun value => .done value) := by
  constructor
  · apply DomainReduction.ReadingTo.receive (I := Nominal.signature F field)
      (.field field) "message" "schema" "prover"
      _ (.receive whereAt) _ (.message whereAt) (Nominal.received field whereAt) id rfl
      (fun payload => by simp [Nominal.received_message])
    intro payload value decoded
    exact .observe _ (.done _ _ trivial)
  · exact .receive (.field field) "message" "schema" "prover" _
      (fun value => .observe _ (.done _ _ trivial))

example [Field F] (field : String) (whereAt : Origin) (history : Domain.History (uniformCarriers F G)) :
    ∃ after : PIR.Process (Nominal.signature F field) F,
      Alignment (I := Nominal.signature F field) Eq (.call (.receive whereAt)
        fun value => .done value) after ∧
      DomainReduction.Bridge (Nominal.interface (G := G) field)
        (fun _ result => ∃ source : F, True ∧ source = result) history
        (.call (.checkpoint []) fun _ =>
          .call (.receive (.field field) "message" "schema" "prover") fun value =>
            .call (.observe (.message whereAt (.field field value))) fun _ => .done value) after := by
  apply Original.Bridge.exists_lossless_presentation
    (live := fun _ _ => True) (lossless := Nominal.lossless field)
  refine ⟨receiveBridge (F := F) (G := G) field whereAt history, .checkpoint [] trivial ?_⟩
  apply Zkc.Construction.Original.Simulation.call (.receive (.field field) "message" "schema" "prover")
  intro value
  apply Zkc.Construction.Original.Simulation.call (carriers := uniformCarriers F G)
    (.observe (.message whereAt (.field field value)))
  intro _
  exact .done rfl

/-- Lossless nominal sends can precede a stopped actual process. The otherwise
unused nominal replies are all Unit, so all-reply Alignment remains justified. -/
example [Field F] (field : String) (whereAt : Origin) (history : Domain.History (uniformCarriers F G))
    (reason : PIR.Stop) :
    ∃ after : PIR.Process (Nominal.signature F field) Bool,
      Alignment (fun (_ : Unit) (_ : Bool) => False)
        (.call (Nominal.Operation.deliver whereAt (0 : F)) fun _ => .halt reason) after ∧
      DomainReduction.ReadingTo (Nominal.interface (G := G) field)
        (fun _ _value => ∃ _a : Unit, True ∧ False) history
        (.halt reason : PIR.Process (Domain.effects (uniformCarriers F G)) Bool) after := by
  apply exists_lossless_reading (I := Nominal.signature F field) (Nominal.lossless field)
    (Zkc.Construction.Original.Simulation.halt (A := Unit) (live := fun _ _ => True) reason)
  exact .absorbSend (I := Nominal.signature F field) (.deliver whereAt 0) _
    (.message whereAt (.field field 0)) () rfl (.halt _ reason)

/-- Decoder refusal retains malformed proof data rather than consuming it. -/
example (field : String) (whereAt : Origin)
    (query : Domain.History (uniformCarriers F G) →
      (event : Domain.Event (uniformCarriers F G)) → Id (Domain.Raw event))
    (history : Domain.History (uniformCarriers F G)) (suffix : Domain.Proof (uniformCarriers F G)) :
    Zkc.Transcript.transform (Nominal.interface (F := F) (G := G) field) query
      (.call (.receive whereAt) fun value => .done value) history (.boolean true :: suffix) =
      pure (.stopped .refused, .boolean true :: suffix) := by
  simp [Zkc.Transcript.transform, Nominal.interface, Nominal.received, Domain.Payload.value]

/-- Identical host carriers do not authorize a different nominal field. -/
example (field foreign : String) (different : foreign ≠ field) (whereAt : Origin) (value : F) :
    Nominal.received (G := G) field whereAt (.message whereAt (.field foreign value)) = none := by
  simp [Nominal.received_message, Domain.Payload.value, different]

example (field : String) (first second : Origin) (different : first ≠ second) (value : F) :
    Nominal.received (G := G) field first (.message second (.field field value)) = none := by
  simp [Nominal.received, Ne.symm different]

/-- An arbitrary typed reply map at the wrong nominal sort cannot satisfy the
checked decoder equation required by the lossless law. -/
example [Field F] (field foreign : String) (different : field ≠ foreign) (whereAt : Origin) :
    ¬ ∃ reply : (uniformCarriers F G).Value (.field foreign) → F,
      ∀ payload : Domain.Payload (uniformCarriers F G),
        Nominal.received field whereAt (.message whereAt payload) =
          (payload.value (.field foreign)).map reply := by
  rintro ⟨reply, decoded⟩
  have impossible := decoded (.field field 0)
  simp [Nominal.received_message, Domain.Payload.value, different] at impossible

#print axioms Nominal.lossless
#print axioms bridge

end TestsSecurity.LosslessPresentationNominal
