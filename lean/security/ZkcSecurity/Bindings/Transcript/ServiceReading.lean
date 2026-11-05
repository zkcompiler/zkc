module

public import ZkcSecurity.Bindings.Transcript.DomainReduction
public import Zkc.Construction.ServiceConnection

@[expose] public section

/-! Exact typed service seams into the existing transcript reading and
coherence relations. There is one request kernel for field, scalar and block
queries; these rules introduce neither an interpreter nor a randomness law. -/
set_option autoImplicit false
namespace ZkcSecurity.FiatShamir.DomainReduction.Service
open Zkc.Source Zkc.Construction
variable {carriers : Structured.Carriers}

def interface : Typed.Interface (Domain.effects carriers)
    (Domain.Event carriers) (Domain.Payload carriers) Domain.Raw
  | .query _ origin => .query (.challenge origin) some
  | _ => .refuse

theorem supported (origin : Origin) (request : Request)
    (valid : request.valid = true) (same : origin.request = some request) :
    Domain.drawRequest origin = true := by
  cases origin
  simp_all [Domain.drawRequest]

/-- One actual query, one exact history extension, and every raw continuation.
This rule also covers malformed decoding by retaining its refusal. -/
theorem request (history : Domain.History carriers) (origin : Origin) (request : Request)
    (valid : request.valid = true) (same : origin.request = some request) :
    Bridge interface (fun reached _ => reached = history ++ [.challenge origin]) history
      (Domain.requestValue origin request (.query history origin))
      (Domain.requestValue origin request (.query history origin)) := by
  rw [Domain.requestValue_query origin request history valid same]
  constructor
  · apply ReadingTo.query (I := Domain.effects carriers) history origin _ (.query history origin) _ id
      (supported origin request valid same) rfl
    intro raw
    dsimp only [id]
    cases decoded : request.decode (by simpa only [Domain.Raw, same] using raw) with
    | none => exact .halt _ .refused
    | some value => exact .done _ _ rfl
  · apply CoherentTo.query history origin _ (supported origin request valid same)
    intro raw
    dsimp only
    split
    · exact .done _ _ rfl
    · exact .halt _ .refused

/-- The actual constructed instruction reads at the accumulated prefix and
advances it once. All returned data, encode refusal and unread proof remain
available to the generic Bridge continuation/handler/computation laws. -/
theorem challenge (context : Context) (suite : String) (request : Request)
    (template : Template) (state coordinates : Nat) (references : List Nat)
    (env : Domain.Environment carriers) (history : Domain.History carriers)
    (path : List Nat) (origin : Origin)
    (transcript : env[state]? = some (.transcript suite history))
    (indices : env[coordinates]? = some (.indices path))
    (checks : suite = context.suite ∧ context.service.isSome ∧ request.valid ∧
      (request.operation context.contract).isSome ∧
      (if request.method = "index" then Domain.requestOperands env references request else references.isEmpty) ∧
      request.nativeSupported)
    (found : Domain.templateOrigin (context.mapReplacement fun replacement =>
      { replacement with request := some request }) template path = some origin)
    (same : origin.request = some request) :
    Bridge interface (fun reached _ => reached = history ++ [.challenge origin]) history
      (Domain.challengeRequest context suite request template state coordinates references
        [.data request.sort, .transcript suite] env)
      (Domain.challengeRequest context suite request template state coordinates references
        [.data request.sort, .transcript suite] env) := by
  rw [Domain.challengeRequest_of_checks context suite request template state coordinates references
    env history path origin transcript indices checks found]
  apply (Service.request history origin request checks.2.2.1 same).bind
  intro reached value advanced
  split
  · exact .done _ _ advanced
  · exact .halt _ .refused

/-- The original fold has exactly the same transcript reading, carrying its
source frames and reached history as returned state. -/
theorem original (state : Original.State carriers) (origin : Origin) (request : Request)
    (valid : request.valid = true) (same : origin.request = some request) :
    Bridge interface (fun reached result => reached = result.2.history ∧
        result.2.frames = state.frames) state.history
      (Original.queryRequest state origin request) (Original.queryRequest state origin request) := by
  unfold Original.queryRequest
  apply (Service.request state.history origin request valid same).bind
  intro reached value advanced
  exact .done _ _ ⟨advanced, rfl⟩

/-- Combine a checked typed source reading with the request kernel's independent
history coherence. Existing exact computation, query-log and reduction laws
then apply to that source presentation without a new oracle experiment. -/
theorem source_bridge {I : PIR.Signature}
    (absorb : Typed.Interface I (Domain.Event carriers) (Domain.Payload carriers) Domain.Raw)
    (history : Domain.History carriers) (origin : Origin) (request : Request)
    (valid : request.valid = true) (same : origin.request = some request)
    (presented : PIR.Process I (carriers.Value request.sort))
    (reading : Reading absorb history
      (Domain.requestValue origin request (.query history origin)) presented) :
    Bridge absorb (fun _ _ => True) history
      (Domain.requestValue origin request (.query history origin)) presented :=
  ⟨reading, (Service.request history origin request valid same).coherent.weaken (fun _ _ _ => trivial)⟩

/-- Read the actual checked scalar source action through its typed transcript
interface. Formation, nominal contract, and every finite reply are explicit;
the source reply check is discharged by the finite decoder's range law. -/
theorem source_index (context : Context) (replacement : Replacement)
    (profile : context.profile = .fiatShamir replacement) (site contract : String)
    (nominal : contract = context.contract) (handle bound : Nat)
    (valid : (Request.sampleIndex bound).valid = true) (positive : 0 < bound)
    (history : Domain.History carriers) :
    Reading (Domain.interface context) history
      (Domain.requestValue (context.query site (.sampleIndex bound)) (.sampleIndex bound)
        (.query history (context.query site (.sampleIndex bound))))
      (Structured.serviceAction (.query site (.sampleIndex contract)
        (.cons handle (.cons bound .nil)))) := by
  have formed : (Structured.ServiceOp.sampleIndex contract).validInputs
      (carriers := carriers) (.cons handle (.cons bound .nil)) = true := valid
  rw [Domain.requestValue_query _ _ history valid rfl]
  simp only [Structured.serviceAction, formed, ite_true]
  apply ReadingTo.query (I := Domain.Actions carriers) history (context.query site (.sampleIndex bound)) _
    (.query site (.sampleIndex contract) (.cons handle (.cons bound .nil))) _
    (fun raw : Fin (Request.replyBound bound) => raw.val) (supported _ _ valid rfl)
  · change (show Zkc.Transcript.Absorption (Domain.Event carriers) (Domain.Payload carriers)
      Domain.Raw Nat from match context.profile with
      | .plain => .refuse
      | .fiatShamir _ =>
        if (Request.sampleIndex bound).valid && contract == context.contract then
          .query (.challenge (context.query site (.sampleIndex bound))) (fun raw => some raw.val)
        else .refuse) = _
    rw [profile]
    simp only [valid, nominal, BEq.rfl, Bool.and_self, ite_true]
    rfl
  · intro raw
    have bounded := Request.index_reply_valid (carriers := carriers) contract handle bound positive raw
    simp only [bounded, ite_true]
    exact .done _ _ trivial

/-- A checked block source action reads one vector-valued oracle answer and
extends history once. Exact count and entry range discharge the source check. -/
theorem source_block (context : Context) (replacement : Replacement)
    (profile : context.profile = .fiatShamir replacement) (site contract : String)
    (nominal : contract = context.contract) (handle bound count : Nat)
    (valid : (Request.sampleIndices bound count).valid = true) (positive : 0 < bound)
    (history : Domain.History carriers) :
    Reading (Domain.interface context) history
      (Domain.requestValue (context.query site (.sampleIndices bound count)) (.sampleIndices bound count)
        (.query history (context.query site (.sampleIndices bound count))))
      (Structured.serviceAction (.query site (.sampleIndices contract)
        (.cons handle (.cons bound (.cons count .nil))))) := by
  have formed : (Structured.ServiceOp.sampleIndices contract).validInputs
      (carriers := carriers) (.cons handle (.cons bound (.cons count .nil))) = true := valid
  rw [Domain.requestValue_query _ _ history valid rfl]
  simp only [Structured.serviceAction, formed, ite_true]
  apply ReadingTo.query (I := Domain.Actions carriers) history (context.query site (.sampleIndices bound count)) _
    (.query site (.sampleIndices contract) (.cons handle (.cons bound (.cons count .nil)))) _
    (fun raw : Fin count → Fin (Request.replyBound bound) => List.ofFn fun i => (raw i).val)
    (supported _ _ valid rfl)
  · change (show Zkc.Transcript.Absorption (Domain.Event carriers) (Domain.Payload carriers)
      Domain.Raw (List Nat) from match context.profile with
      | .plain => .refuse
      | .fiatShamir _ =>
        if (Request.sampleIndices bound count).valid && contract == context.contract then
          .query (.challenge (context.query site (.sampleIndices bound count)))
            (fun raw => some (List.ofFn fun i => (raw i).val))
        else .refuse) = _
    rw [profile]
    simp only [valid, nominal, BEq.rfl, Bool.and_self, ite_true]
    rfl
  · intro raw
    have bounded := Request.block_reply_valid (carriers := carriers) contract handle bound count positive raw
    simp only [bounded, ite_true]
    exact .done _ _ trivial

end ZkcSecurity.FiatShamir.DomainReduction.Service
