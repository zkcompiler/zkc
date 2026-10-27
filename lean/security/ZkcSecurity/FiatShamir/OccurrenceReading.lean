module
public import Zkc.Construction.Uniform.OccurrenceSourceProcess
public import ZkcSecurity.FiatShamir.NominalField
public import ZkcSecurity.FiatShamir.DomainReduction
public import ZkcSecurity.Obligations.Derivation
@[expose] public section

/-! Nominal presentations of independently routed source processes. These laws
reuse the existing occurrence fold and nominal field interface. Constant-price
rejection and cost proofs transfer from the scalar mathematics while the actual
experiment retains its exact accumulated histories and source occurrences. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 50000
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ZkcSecurity.FiatShamir.OccurrenceReading
open Zkc.Source Zkc.Source.Structured Zkc.Construction Zkc.Transcript
open Zkc.Construction.Uniform.OccurrenceSourceProcess
open ZkcSecurity.FiatShamir.DomainReduction
variable {F G A : Type}

def signature (F : Type) : PIR.Signature where
  Op := Sigma (NominalField.Operation F)
  Reply operation := (NominalField.signature F operation.1).Reply operation.2

def interface : Interface (signature F) (Domain.Event (uniformCarriers F G))
    (Domain.Payload (uniformCarriers F G)) Domain.Raw :=
  fun operation => NominalField.interface (G := G) operation.1 operation.2

def Post (final : Original.Frames) (history : Domain.History (uniformCarriers F G))
    (result : A × Original.State (uniformCarriers F G)) : Prop :=
  result.2.frames = final ∧ result.2.history = history

noncomputable def presentation {routing : Original.Routing} {frames final : Original.Frames}
    {source : PIR.Process (Occurrence.signature (uniformCarriers F G)) A}
    (routed : Routed routing frames final source) (history : Domain.History (uniformCarriers F G)) :
    PIR.Process (signature F) (A × Original.State (uniformCarriers F G)) :=
  match routed with
  | .done frames value => .done (value, ⟨frames, history⟩)
  | .halt _ _ reason => .halt reason
  | .enter _ _ _ tail => presentation tail history
  | .leave _ _ _ _ tail => presentation tail history
  | .receive _ _ _ field _ origin _ _ tail =>
      .call ⟨field, .receive origin⟩ fun value =>
        presentation (tail value) (history ++ [.message origin (.field field value)])
  | .send _ _ _ field _ value origin _ _ tail =>
      .call ⟨field, .deliver origin value⟩ fun _ =>
        presentation tail (history ++ [.message origin (.field field value)])
  | .query _ _ _ field _ origin _ _ request tail =>
      .call ⟨field, .query origin request⟩ fun value =>
        presentation (tail value) (history ++ [.challenge origin])

/-- Exact nominal reading of an independently routed occurrence process.
This proof uses the existing fold and field interfaces; it adds no evaluator. -/
theorem reading {routing : Original.Routing} (mode : routing.mode = .validator)
    (replacement : Replacement) (profileEq : routing.context.profile = .fiatShamir replacement)
    {frames final : Original.Frames}
    {source : PIR.Process (Occurrence.signature (uniformCarriers F G)) A}
    (routed : Routed routing frames final source) (history : Domain.History (uniformCarriers F G)) :
    Bridge interface (Post final) history
        (Original.fold routing source ⟨frames, history⟩) (presentation routed history) := by
  induction routed generalizing history with
  | done frames value =>
      exact .done history _ ⟨rfl, rfl⟩
  | halt frames final reason => exact .halt history reason
  | enter frames final frame tail ih =>
      simpa only [presentation, fold_call, Original.operations, PIR.Process.bind] using ih history
  | leave frames final frame last tail ih =>
      simpa only [presentation, fold_call, Original.operations, last, ↓reduceIte, PIR.Process.bind] using ih history
  | receive frames final site field sender origin route key tail ih =>
      let presented := fun value => presentation (tail value) (history ++ [.message origin (.field field value)])
      have bridge := fun value => ih value (history ++ [.message origin (.field field value)])
      change Bridge (interface (F := F) (G := G)) (Post final) history _ (.call (⟨field, .receive origin⟩ : (signature F).Op) presented)
      rw [fold_call]
      simp only [Original.operations, profileEq, Original.receive, mode, route,
        PIR.Process.bind, Domain.Payload.ofValue, Original.record]
      constructor
      · refine ReadingTo.receive (absorb := interface (F := F) (G := G)) (.field field) site site (routing.context.role sender) _
          (⟨field, .receive origin⟩ : (signature F).Op) presented (.message origin) (NominalField.received field origin)
          id rfl ?_ ?_
        · intro payload
          simpa only [Option.map_id, id_eq] using NominalField.received_message (F := F) (G := G) field origin payload
        · intro payload value decoded
          have same : payload = .field field value :=
            (Domain.Payload.ofValue_value decoded).symm |> Option.some.inj
          subst payload
          exact .observe _ (bridge value).reading
      · refine .receive (.field field) site site (routing.context.role sender) _ ?_
        intro value
        exact .observe _ (bridge value).coherent
  | send frames final site field receiver value origin route key tail ih =>
      have bridge := ih (history ++ [.message origin (.field field value)])
      change Bridge (interface (F := F) (G := G)) (Post final) history _ (.call (⟨field, .deliver origin value⟩ : (signature F).Op) (fun _ => presentation tail (history ++ [.message origin (.field field value)])))
      rw [fold_call]
      simp only [Original.operations, profileEq, Original.send, mode, route,
        Domain.Payload.ofValue, Ty.isService, ↓reduceDIte, Original.record, PIR.Process.bind]
      exact ⟨ReadingTo.absorbSend (absorb := interface (F := F) (G := G)) (⟨field, .deliver origin value⟩ : (signature F).Op) _ _ () rfl (.observe _ bridge.reading),
        .observe _ bridge.coherent⟩
  | query frames final site field handle origin route key request tail ih =>
      let presented := fun value => presentation (tail value) (history ++ [.challenge origin])
      have bridge := fun value => ih value (history ++ [.challenge origin])
      change Bridge (interface (F := F) (G := G)) (Post final) history _ (.call (⟨field, .query origin request⟩ : (signature F).Op) presented)
      rw [fold_call]
      simp only [Original.operations, profileEq]
      rw [Original.public_query routing _ site field handle origin mode route]
      simp only [PIR.Process.bind]
      have supported : Domain.drawRequest origin = true := by
        rcases origin with ⟨entry, events, asked⟩
        change asked = some (.draw field) at request
        subst asked
        rfl
      constructor
      · refine ReadingTo.query (absorb := interface (F := F) (G := G)) history origin _ (⟨field, .query origin request⟩ : (signature F).Op) presented
          (Original.fieldReply (carriers := uniformCarriers F G) origin field request) supported ?_ ?_
        · rfl
        · intro raw
          exact (bridge (Original.fieldReply origin field request raw)).reading
      · exact .query history origin _ supported
          (fun raw => (bridge (Original.fieldReply origin field request raw)).coherent)

variable [Field F]

theorem lossless : ZkcSecurity.FiatShamir.Original.LosslessInterface (interface (F := F) (G := G)) where
  receive := by
    rintro ⟨field, operation⟩ ty event recover reply absorbed decoded
    exact (NominalField.lossless (F := F) (G := G) field).receive operation ty event recover reply absorbed decoded
  query := by
    rintro ⟨field, operation⟩ origin reply absorbed
    exact (NominalField.lossless (F := F) (G := G) field).query operation origin reply absorbed
  send := by
    rintro ⟨field, operation⟩ event value absorbed reply
    exact (NominalField.lossless (F := F) (G := G) field).send operation event value absorbed reply

open Zkc.Obligations ZkcSecurity.Obligations
open OracleComp OracleSpec

variable [SampleableType F]

noncomputable abbrev rawSampleable : (event : Domain.Event (uniformCarriers F G)) → SampleableType (Domain.Raw event)
  | .message .. | .publicBinding _ => inferInstanceAs (SampleableType Unit)
  | .challenge origin => by
      rcases origin with ⟨entry, events, request⟩
      cases request with
      | none => exact inferInstanceAs (SampleableType Unit)
      | some request =>
          rcases request with ⟨method, parameters, sort⟩
          cases sort
          case field identity => exact inferInstanceAs (SampleableType F)
          all_goals exact inferInstanceAs (SampleableType Unit)

attribute [local instance] rawSampleable

omit [Field F] in
theorem charged {routing : Original.Routing} {frames final : Original.Frames}
    {source : PIR.Process (Occurrence.signature (uniformCarriers F G)) A}
    (price : ENNReal) (P : A → Prop)
    (routed : Routed routing frames final source)
    (scalarHistory : History F G) (history : Domain.History (uniformCarriers F G))
    (holds : routing.context.interface.Charged (boundedEscape (fun _ _ => price)) (fun _ => P)
      ((source.interpret Occurrence.erase).interpret CommonAdapter.project) scalarHistory) :
    (interface (F := F) (G := G)).Charged (boundedEscape (fun _ _ => price)) (fun _ result => P result.1)
      (presentation routed history) history := by
  induction routed generalizing scalarHistory history with
  | done frames value => exact holds
  | halt => trivial
  | enter frames final frame tail ih =>
      exact ih scalarHistory history holds
  | leave frames final frame last tail ih =>
      exact ih scalarHistory history holds
  | receive frames final site field sender origin route key tail ih =>
      simp only [PIR.Process.interpret, Occurrence.erase, CommonAdapter.project, PIR.Process.bind,
        Interface.charged_call, Context.interface, Absorption.ChargedNode] at holds
      simp only [presentation, Interface.charged_call, interface, NominalField.interface, Absorption.ChargedNode]
      intro payload value decoded
      have payloadEq : payload = .field field value := by
        rw [NominalField.received_message] at decoded
        exact (Domain.Payload.ofValue_value decoded).symm |> Option.some.inj
      subst payload
      apply ih value _ _
      exact holds (.field field value) value (by simp [Context.receivedValue, Payload.value])
  | send frames final site field receiver value origin route key tail ih =>
      simp only [PIR.Process.interpret, Occurrence.erase, CommonAdapter.project, PIR.Process.bind,
        Interface.charged_call, Context.interface, Payload.ofValue, Absorption.ChargedNode] at holds
      simp only [presentation, Interface.charged_call, interface, NominalField.interface, Absorption.ChargedNode]
      exact ih _ _ holds
  | query frames final site field handle origin route key request tail ih =>
      rcases origin with ⟨entry, events, asked⟩
      change asked = some (.draw field) at request
      subst asked
      simp only [PIR.Process.interpret, Occurrence.erase, CommonAdapter.project, PIR.Process.bind,
        Interface.charged_call, Context.interface, Absorption.ChargedNode] at holds
      simp only [presentation, Interface.charged_call, interface, NominalField.interface, Absorption.ChargedNode,
        Domain.Raw, Request.draw]
      apply (boundedEscape_antitone (fun _ _ => price)) _ _ _ _ ?_ holds
      rintro raw ⟨value, decoded, outside⟩
      cases Option.some.inj decoded
      refine ⟨raw, rfl, ?_⟩
      exact fun inside => outside (ih raw _ _ inside)

omit [Field F] [SampleableType F] in
theorem cost {routing : Original.Routing} {frames final : Original.Frames}
    {source : PIR.Process (Occurrence.signature (uniformCarriers F G)) A}
    (price budget : ENNReal) (routed : Routed routing frames final source)
    (scalarHistory : History F G) (history : Domain.History (uniformCarriers F G))
    (holds : ZkcSecurity.FiatShamir.Typed.ChargedCostBound routing.context.interface (fun _ _ => price)
      ((source.interpret Occurrence.erase).interpret CommonAdapter.project) scalarHistory budget) :
    ZkcSecurity.FiatShamir.Typed.ChargedCostBound (interface (F := F) (G := G)) (fun _ _ => price)
      (presentation routed history) history budget := by
  induction routed generalizing scalarHistory history budget with
  | done => trivial
  | halt => trivial
  | enter frames final frame tail ih => exact ih _ _ _ holds
  | leave frames final frame last tail ih => exact ih _ _ _ holds
  | receive frames final site field sender origin route key tail ih =>
      simp only [PIR.Process.interpret, Occurrence.erase, CommonAdapter.project, PIR.Process.bind,
        ZkcSecurity.FiatShamir.Typed.ChargedCostBound, Context.interface] at holds
      simp only [presentation, ZkcSecurity.FiatShamir.Typed.ChargedCostBound, interface, NominalField.interface]
      intro payload value decoded
      have payloadEq : payload = .field field value := by
        rw [NominalField.received_message] at decoded
        exact (Domain.Payload.ofValue_value decoded).symm |> Option.some.inj
      subst payload
      apply ih value _ _ _
      exact holds (.field field value) value (by simp [Context.receivedValue, Payload.value])
  | send frames final site field receiver value origin route key tail ih =>
      simp only [PIR.Process.interpret, Occurrence.erase, CommonAdapter.project, PIR.Process.bind,
        ZkcSecurity.FiatShamir.Typed.ChargedCostBound, Context.interface, Payload.ofValue] at holds
      simp only [presentation, ZkcSecurity.FiatShamir.Typed.ChargedCostBound, interface, NominalField.interface]
      exact ih _ _ _ holds
  | query frames final site field handle origin route key request tail ih =>
      simp only [PIR.Process.interpret, Occurrence.erase, CommonAdapter.project, PIR.Process.bind,
        ZkcSecurity.FiatShamir.Typed.ChargedCostBound, Context.interface] at holds
      simp only [presentation, ZkcSecurity.FiatShamir.Typed.ChargedCostBound, interface, NominalField.interface]
      obtain ⟨remaining, le, after⟩ := holds
      exact ⟨remaining, le, fun value => ih value _ _ _ (after value)⟩
end ZkcSecurity.FiatShamir.OccurrenceReading
