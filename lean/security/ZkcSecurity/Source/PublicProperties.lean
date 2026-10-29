module

public import ZkcSecurity.FiatShamir.DomainSourceReading
public import ZkcSecurity.Obligations.Derivation
public import ZkcSecurity.FiatShamir.CostComposition

@[expose] public section

/-! Property transport for an occurrence validator's public interpretation.
Static proof events retain source boundaries and are never transcript identities.
Dynamic origins and the actual accumulated history come only from routing.
A missing route is an actual refusal, not a failed proof counted as an attack.
-/
set_option autoImplicit false
namespace ZkcSecurity.Source.PublicProperties
open Zkc.Source Zkc.Source.Structured Zkc.Construction Zkc.Transcript Zkc.Obligations
open ZkcSecurity.FiatShamir
open OracleComp OracleSpec

variable {carriers : Carriers}

inductive Event (carriers : Carriers) where
  | enter (frame : Occurrence.Frame)
  | leave (frame : Occurrence.Frame)
  | message (site : String) (peer : Nat) (payload : Domain.Payload carriers)
  | challenge (site field : String) (handle : Nat)

def Raw : Event carriers → Type
  | .challenge _ field _ => carriers.Field field
  | _ => Unit

def recovered (ty : Ty) : Event carriers → Option (carriers.Value ty)
  | .message _ _ payload => payload.value ty
  | _ => none

def interface : Interface (Occurrence.signature carriers) (Event carriers) (Domain.Payload carriers) Raw
  | .enter frame => .send (.enter frame) ()
  | .leave frame => .send (.leave frame) ()
  | .action (.receive ty site sender) => .receive (.message site sender) (recovered ty)
  | .action (@Participant.Action.send _ _ _ _ ty site receiver value) =>
    match Domain.Payload.ofValue ty value with
    | none => .refuse
    | some payload => .send (.message site receiver payload) ()
  | .action (.query site field (.cons handle .nil)) => .query (.challenge site field handle) some

variable [samples : ∀ event : Domain.Event carriers, SampleableType (Domain.Raw event)]

/-- The source query obligation quantifies over every actual routed origin.
This retains the selected nominal raw distribution and refusing request check;
no static source address is substituted for an oracle key. -/
def escape (price : ENNReal) : EscapeJudgment (Event carriers) Raw :=
  fun _ event bad => match event with
  | .challenge _ field _ => ∀ (origin : Origin) (request : origin.request = some (.draw field)),
      Pr{let raw ← $ᵗ (Domain.Raw (.challenge origin : Domain.Event carriers))}[bad (Original.fieldReply origin field request raw)] ≤ price
  | _ => True

variable (routing : Original.Routing) (mode : routing.mode = .validator) (price : ENNReal)
include mode

/-- Source derivations install at arbitrary complete interpreter states and
arbitrary incoming histories. Only local query escape laws are consumed. -/
noncomputable def install {A : Type} (post : A → Prop)
    (source : PIR.Process (Occurrence.signature carriers) A) (history : List (Event carriers))
    (proof : Derivation interface (escape price) (fun _ => post) history source)
    (state : Original.State carriers) :
    Derivation NominalDomain.interface (ZkcSecurity.Obligations.boundedEscape (fun _ _ => price))
      (fun _ result => post result.1) state.history
      (DomainSourceReading.presentation routing source state) := by
  induction source generalizing history state with
  | done value =>
    cases proof with
    | done holds => exact .done holds
  | halt reason => exact .halt reason
  | call operation next ih =>
    cases operation with
    | enter frame =>
      cases proof with
      | receive absorbed _ => cases absorbed
      | send absorbed suffix =>
        cases absorbed
        exact ih () _ suffix { state with frames := state.frames ++ [frame] }
      | query absorbed _ _ _ => cases absorbed
      | refuse absorbed => cases absorbed
    | leave frame =>
      cases proof with
      | receive absorbed _ => cases absorbed
      | send absorbed suffix =>
        cases absorbed
        simp only [DomainSourceReading.presentation, PIR.Process.interpretState, DomainSourceReading.operations]
        by_cases last : state.frames.getLast? = some frame
        · simp only [last, ↓reduceIte, PIR.Process.bind]
          exact ih () _ suffix { state with frames := state.frames.dropLast }
        · simp only [last, ↓reduceIte, PIR.Process.bind]
          exact .halt .refused
      | query absorbed _ _ _ => cases absorbed
      | refuse absorbed => cases absorbed
    | action action =>
      cases action with
      | receive ty site sender =>
        cases proof with
        | receive absorbed continuations =>
          cases absorbed
          change Derivation _ _ _ _ ((DomainSourceReading.receive routing state ty site sender).bind _)
          simp only [DomainSourceReading.receive, mode]
          cases route : routing.message state.frames site sender routing.context.validator with
          | none => exact .halt .refused
          | some origin =>
            refine .receive rfl fun payload value decoded => ?_
            have recovered : payload.value ty = some value := by
              simpa only [NominalDomain.received_message] using decoded
            simp only [Domain.Payload.ofValue_value recovered, PIR.Process.bind]
            exact ih value _ (continuations payload value recovered)
              { state with history := state.history ++ [.message origin payload] }
        | send absorbed _ => cases absorbed
        | query absorbed _ _ _ => cases absorbed
        | refuse absorbed => cases absorbed
      | @send ty site receiver value =>
        change Derivation _ _ _ _ ((DomainSourceReading.send routing state ty site receiver value).bind _)
        simp only [DomainSourceReading.send, mode]
        cases payloadEq : Domain.Payload.ofValue ty value with
        | none =>
          cases routing.message state.frames site routing.context.validator receiver <;> exact .halt .refused
        | some payload =>
          cases proof with
          | receive absorbed _ => simp only [interface, payloadEq] at absorbed; cases absorbed
          | send absorbed suffix =>
            simp only [interface, payloadEq] at absorbed
            cases absorbed
            cases route : routing.message state.frames site routing.context.validator receiver with
            | none => exact .halt .refused
            | some origin =>
              exact .send rfl (ih () _ suffix
                { state with history := state.history ++ [.message origin payload] })
          | query absorbed _ _ _ => simp only [interface, payloadEq] at absorbed; cases absorbed
          | refuse absorbed => simp only [interface, payloadEq] at absorbed; cases absorbed
      | query site field arguments =>
        cases arguments with
        | cons handle tail =>
          cases tail
          cases proof with
          | receive absorbed _ => cases absorbed
          | send absorbed _ => cases absorbed
          | query absorbed bad bounded continuations =>
            cases absorbed
            change Derivation _ _ _ _ ((DomainSourceReading.query routing state site field handle).bind _)
            simp only [DomainSourceReading.query, mode]
            cases route : routing.draw state.frames site field handle with
            | none => exact .halt .refused
            | some origin =>
              unfold DomainSourceReading.queryField
              by_cases request : origin.request = some (.draw field)
              · simp only [request, ↓reduceDIte, PIR.Process.bind]
                refine .query rfl (fun raw => bad (Original.fieldReply origin field request raw))
                  (bounded origin request) ?_
                intro raw reply decoded outside
                cases decoded
                exact ih (Original.fieldReply origin field request raw) _
                  (continuations _ _ rfl outside)
                  { state with history := state.history ++ [.challenge origin] }
              · simp only [request, ↓reduceDIte, PIR.Process.bind]
                exact .halt .refused
          | refuse absorbed => cases absorbed

omit samples in
/-- Erasing static source boundaries never increases the charged query cost.
Every dynamic query retains the same price and the entire interpreter state. -/
theorem install_cost {A : Type} (source : PIR.Process (Occurrence.signature carriers) A)
    (history : List (Event carriers)) (budget : ENNReal)
    (bounded : Typed.ChargedCostBound interface (fun _ _ => price) source history budget)
    (state : Original.State carriers) :
    Typed.ChargedCostBound NominalDomain.interface (fun _ _ => price)
      (DomainSourceReading.presentation routing source state) state.history budget := by
  induction source generalizing history state budget with
  | done => trivial
  | halt => trivial
  | call operation next ih =>
    cases operation with
    | enter frame =>
      exact ih () _ _ bounded { state with frames := state.frames ++ [frame] }
    | leave frame =>
      simp only [DomainSourceReading.presentation, PIR.Process.interpretState, DomainSourceReading.operations]
      by_cases last : state.frames.getLast? = some frame
      · simp only [last, ↓reduceIte, PIR.Process.bind]
        exact ih () _ _ bounded { state with frames := state.frames.dropLast }
      · simp only [last, ↓reduceIte, PIR.Process.bind]
        trivial
    | action action =>
      cases action with
      | receive ty site sender =>
        change Typed.ChargedCostBound _ _ ((DomainSourceReading.receive routing state ty site sender).bind _) _ _
        simp only [DomainSourceReading.receive, mode]
        cases route : routing.message state.frames site sender routing.context.validator with
        | none => trivial
        | some origin =>
          intro payload value decoded
          have recovered : payload.value ty = some value := by
            simpa only [NominalDomain.received_message] using decoded
          simp only [Domain.Payload.ofValue_value recovered, PIR.Process.bind]
          exact ih value _ _ (bounded payload value recovered)
            { state with history := state.history ++ [.message origin payload] }
      | @send ty site receiver value =>
        change Typed.ChargedCostBound _ _ ((DomainSourceReading.send routing state ty site receiver value).bind _) _ _
        simp only [DomainSourceReading.send, mode]
        cases payloadEq : Domain.Payload.ofValue ty value with
        | none =>
          cases routing.message state.frames site routing.context.validator receiver <;> trivial
        | some payload =>
          simp only [Typed.ChargedCostBound, interface, payloadEq] at bounded
          cases route : routing.message state.frames site routing.context.validator receiver with
          | none => trivial
          | some origin =>
            exact ih () _ _ bounded { state with history := state.history ++ [.message origin payload] }
      | query site field arguments =>
        cases arguments with
        | cons handle tail =>
          cases tail
          obtain ⟨remaining, le, bounded⟩ := bounded
          change Typed.ChargedCostBound _ _ ((DomainSourceReading.query routing state site field handle).bind _) _ _
          simp only [DomainSourceReading.query, mode]
          cases route : routing.draw state.frames site field handle with
          | none => trivial
          | some origin =>
            unfold DomainSourceReading.queryField
            by_cases request : origin.request = some (.draw field)
            · simp only [request, ↓reduceDIte, PIR.Process.bind]
              exact ⟨remaining, le, fun raw => ih (Original.fieldReply origin field request raw) _ _
                (bounded _) { state with history := state.history ++ [.challenge origin] }⟩
            · simp only [request, ↓reduceDIte, PIR.Process.bind]
              trivial

#print axioms install
#print axioms install_cost
end ZkcSecurity.Source.PublicProperties
