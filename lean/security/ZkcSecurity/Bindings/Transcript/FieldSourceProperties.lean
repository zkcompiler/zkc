module

public import ZkcSecurity.Bindings.Transcript.FieldSourceSupport
public import ZkcSecurity.Bindings.Transcript.OccurrenceReading
public import ZkcSecurity.ProgramLogic.Transcript.CostComposition

@[expose] public section

/-! Reuse constant-price field mathematics in the ordinary nominal source
presentation. This transports properties, not execution correspondence: the
root still independently supplies coverage, full simulation and source reading.
No route, frame, source equation or protocol identity is supplied to this rule.
-/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace ZkcSecurity.FiatShamir.FieldSourceProperties
open Zkc.Source Zkc.Source.Structured Zkc.Construction Zkc.Transcript
open Zkc.Obligations ZkcSecurity.Obligations
open OracleComp OracleSpec
variable {F G A : Type}

abbrev scalar (source : PIR.Process (Occurrence.signature (uniformCarriers F G)) A) :=
  (source.interpret Occurrence.erase).interpret CommonAdapter.project

variable [SampleableType F]
attribute [local instance] OccurrenceReading.rawSampleable

/-- Constant prices and history-independent postconditions allow the existing
scalar theorem to be reused without erasing the actual nominal execution.
Refusing routes stay stopped. Independent root coverage excludes a vacuous
connection; this property rule itself needs no successful-routing premise. -/
theorem charged (routing : Original.Routing) (mode : routing.mode = .validator)
    (source : PIR.Process (Occurrence.signature (uniformCarriers F G)) A)
    (supported : PIR.OperationSupport FieldSourceSupport.sourceOperation source)
    (price : ENNReal) (P : A → Prop) (scalarHistory : History F G)
    (state : Original.State (uniformCarriers F G))
    (holds : routing.context.interface.Charged (boundedEscape (fun _ _ => price))
      (fun _ => P) (scalar source) scalarHistory) :
    NominalDomain.interface.Charged (boundedEscape (fun _ _ => price))
      (fun _ result => P result.1) (DomainSourceReading.presentation routing source state) state.history := by
  induction source generalizing scalarHistory state with
  | done value => exact holds
  | halt reason => trivial
  | call operation next ih =>
    obtain ⟨allowed, supported⟩ := supported
    cases operation with
    | enter frame => exact ih () (supported ()) scalarHistory _ holds
    | leave frame =>
      simp only [DomainSourceReading.presentation, PIR.Process.interpretState,
        DomainSourceReading.operations]
      split
      · exact ih () (supported ()) scalarHistory _ holds
      · trivial
    | action action =>
      cases action with
      | receive ty site sender =>
        cases ty <;> try exact False.elim allowed
        rename_i field
        simp only [scalar, PIR.Process.interpret, Occurrence.erase, CommonAdapter.project,
          PIR.Process.bind, Interface.charged_call, Context.interface, Absorption.ChargedNode] at holds
        simp only [DomainSourceReading.presentation, PIR.Process.interpretState,
          DomainSourceReading.operations, DomainSourceReading.receive, mode]
        cases route : routing.message state.frames site sender routing.context.validator with
        | none => trivial
        | some origin =>
          simp only [PIR.Process.bind, Interface.charged_call, NominalDomain.interface, Absorption.ChargedNode]
          intro payload value decoded
          have payloadEq : payload = .field field value := by
            rw [NominalDomain.received_message] at decoded
            exact (Domain.Payload.ofValue_value decoded).symm |> Option.some.inj
          subst payload
          simp only [Domain.Payload.ofValue, Interface.charged_call]
          exact ih value (supported value) _ _
            (holds (.field field value) value (by simp [Context.receivedValue, Payload.value]))
      | @send ty site receiver value =>
        cases ty <;> try exact False.elim allowed
        rename_i field
        simp only [scalar, PIR.Process.interpret, Occurrence.erase, CommonAdapter.project,
          PIR.Process.bind, Interface.charged_call, Context.interface, Payload.ofValue, Absorption.ChargedNode] at holds
        simp only [DomainSourceReading.presentation, PIR.Process.interpretState,
          DomainSourceReading.operations, DomainSourceReading.send, mode, Domain.Payload.ofValue]
        cases route : routing.message state.frames site routing.context.validator receiver with
        | none => trivial
        | some origin =>
          simp only [DomainSourceReading.record, PIR.Process.bind, Interface.charged_call,
            NominalDomain.interface, Absorption.ChargedNode]
          exact ih () (supported ()) _ _ holds
      | query site field arguments =>
        cases arguments with
        | cons handle rest =>
          cases rest
          simp only [scalar, PIR.Process.interpret, Occurrence.erase, CommonAdapter.project,
            PIR.Process.bind, Interface.charged_call, Context.interface, Absorption.ChargedNode] at holds
          change NominalDomain.interface.Charged (boundedEscape (fun _ _ => price))
            (fun _ result => P result.1)
            ((DomainSourceReading.query routing state site field handle).bind fun result =>
              DomainSourceReading.presentation routing (next result.1) result.2) state.history
          simp only [DomainSourceReading.query, mode]
          cases route : routing.draw state.frames site field handle with
          | none => trivial
          | some origin =>
            have request := Original.Routing.draw_request route
            rcases origin with ⟨entry, events, asked⟩
            change asked = some (.draw field) at request
            subst asked
            simp only [DomainSourceReading.queryField, ↓reduceDIte, PIR.Process.bind,
              Interface.charged_call, NominalDomain.interface, Absorption.ChargedNode,
              Domain.Raw, Request.draw, Original.fieldReply]
            apply (boundedEscape_antitone (fun _ _ => price)) _ _ _ _ ?_ holds
            rintro raw ⟨value, decoded, outside⟩
            cases Option.some.inj decoded
            exact ⟨raw, rfl, fun inside => outside (ih raw (supported raw) _ _ inside)⟩

omit [SampleableType F] in
/-- Pathwise constant-price cost transport uses the same actual nominal
presentation, arbitrary frames, optional replies and refusal branches. -/
theorem cost (routing : Original.Routing) (mode : routing.mode = .validator)
    (source : PIR.Process (Occurrence.signature (uniformCarriers F G)) A)
    (supported : PIR.OperationSupport FieldSourceSupport.sourceOperation source)
    (price budget : ENNReal) (scalarHistory : History F G)
    (state : Original.State (uniformCarriers F G))
    (holds : Typed.ChargedCostBound routing.context.interface (fun _ _ => price)
      (scalar source) scalarHistory budget) :
    Typed.ChargedCostBound NominalDomain.interface (fun _ _ => price)
      (DomainSourceReading.presentation routing source state) state.history budget := by
  induction source generalizing scalarHistory state budget with
  | done => trivial
  | halt => trivial
  | call operation next ih =>
    obtain ⟨allowed, supported⟩ := supported
    cases operation with
    | enter frame => exact ih () (supported ()) _ _ _ holds
    | leave frame =>
      simp only [DomainSourceReading.presentation, PIR.Process.interpretState,
        DomainSourceReading.operations]
      split
      · exact ih () (supported ()) _ _ _ holds
      · trivial
    | action action =>
      cases action with
      | receive ty site sender =>
        cases ty <;> try exact False.elim allowed
        rename_i field
        simp only [scalar, PIR.Process.interpret, Occurrence.erase, CommonAdapter.project,
          PIR.Process.bind, Typed.ChargedCostBound, Context.interface] at holds
        simp only [DomainSourceReading.presentation, PIR.Process.interpretState,
          DomainSourceReading.operations, DomainSourceReading.receive, mode]
        cases route : routing.message state.frames site sender routing.context.validator with
        | none => trivial
        | some origin =>
          simp only [PIR.Process.bind, Typed.ChargedCostBound, NominalDomain.interface]
          intro payload value decoded
          have payloadEq : payload = .field field value := by
            rw [NominalDomain.received_message] at decoded
            exact (Domain.Payload.ofValue_value decoded).symm |> Option.some.inj
          subst payload
          simp only [Domain.Payload.ofValue]
          exact ih value (supported value) _ _ _
            (holds (.field field value) value (by simp [Context.receivedValue, Payload.value]))
      | @send ty site receiver value =>
        cases ty <;> try exact False.elim allowed
        rename_i field
        simp only [scalar, PIR.Process.interpret, Occurrence.erase, CommonAdapter.project,
          PIR.Process.bind, Typed.ChargedCostBound, Context.interface, Payload.ofValue] at holds
        simp only [DomainSourceReading.presentation, PIR.Process.interpretState,
          DomainSourceReading.operations, DomainSourceReading.send, mode, Domain.Payload.ofValue]
        cases route : routing.message state.frames site routing.context.validator receiver with
        | none => trivial
        | some origin =>
          simp only [DomainSourceReading.record, PIR.Process.bind, Typed.ChargedCostBound,
            NominalDomain.interface]
          exact ih () (supported ()) _ _ _ holds
      | query site field arguments =>
        cases arguments with
        | cons handle rest =>
          cases rest
          simp only [scalar, PIR.Process.interpret, Occurrence.erase, CommonAdapter.project,
            PIR.Process.bind, Typed.ChargedCostBound, Context.interface] at holds
          change Typed.ChargedCostBound NominalDomain.interface (fun _ _ => price)
            ((DomainSourceReading.query routing state site field handle).bind fun result =>
              DomainSourceReading.presentation routing (next result.1) result.2) state.history budget
          simp only [DomainSourceReading.query, mode]
          cases route : routing.draw state.frames site field handle with
          | none => trivial
          | some origin =>
            have request := Original.Routing.draw_request route
            rcases origin with ⟨entry, events, asked⟩
            change asked = some (.draw field) at request
            subst asked
            simp only [DomainSourceReading.queryField, ↓reduceDIte, PIR.Process.bind,
              Typed.ChargedCostBound, NominalDomain.interface]
            obtain ⟨remaining, le, after⟩ := holds
            exact ⟨remaining, le, fun value => ih value (supported value) _ _ _ (after value)⟩

end ZkcSecurity.FiatShamir.FieldSourceProperties
