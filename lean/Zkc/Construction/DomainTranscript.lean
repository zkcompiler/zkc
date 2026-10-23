module

public import Zkc.Construction.FiatShamir
public import Zkc.Source.Structured.DomainParticipant

@[expose] public section

/-! Transcript data with the carriers of the admitted nominal domains.

The generic transcript transform already supports event-dependent replies.
This module supplies its structured participant interface without identifying
different fields or groups. Service handles are capabilities, not proof data.
-/

set_option autoImplicit false

namespace Zkc.Construction.Domain
open Zkc.Source

/-- Data transported in a proof or absorbed into a transcript. -/
inductive Payload (carriers : Structured.Carriers) where
  | boolean (value : Bool)
  | index (value : Nat)
  | field (domain : String) (value : carriers.Field domain)
  | vector (domain : String) (value : List (carriers.Field domain))
  | group (domain : String) (value : carriers.Group domain)

namespace Payload
variable {carriers : Structured.Carriers}

def ty : Payload carriers → Structured.Ty
  | .boolean _ => .boolean
  | .index _ => .index
  | .field domain _ => .field domain
  | .vector domain _ => .vector domain
  | .group domain _ => .group domain

def ofValue : (ty : Structured.Ty) → carriers.Value ty → Option (Payload carriers)
  | .boolean, value => some (.boolean value)
  | .index, value => some (.index value)
  | .field domain, value => some (.field domain value)
  | .vector domain, value => some (.vector domain value)
  | .group domain, value => some (.group domain value)
  | .service _, _ => none

/-- Decode only at the exact nominal sort. The equality transports the value's
type; an equality of host carrier types alone cannot authorize decoding. -/
def value : (ty : Structured.Ty) → Payload carriers → Option (carriers.Value ty)
  | .boolean, .boolean value => some value
  | .index, .index value => some value
  | .field domain, .field other value =>
      if h : other = domain then some (h ▸ value) else none
  | .vector domain, .vector other value =>
      if h : other = domain then some (h ▸ value) else none
  | .group domain, .group other value =>
      if h : other = domain then some (h ▸ value) else none
  | _, _ => none

theorem value_ofValue {ty : Structured.Ty} {input : carriers.Value ty}
    {payload : Payload carriers} (encoded : ofValue ty input = some payload) :
    payload.value ty = some input := by
  cases ty <;> simp only [ofValue] at encoded <;> cases encoded <;> simp [value]

theorem ofValue_value {ty : Structured.Ty} {payload : Payload carriers}
    {output : carriers.Value ty} (decoded : payload.value ty = some output) :
    ofValue ty output = some payload := by
  cases ty <;> cases payload <;> simp_all [value, ofValue]
  all_goals
    rcases decoded with ⟨rfl, rfl⟩
    exact ⟨rfl, HEq.rfl⟩

theorem value_isSome {ty : Structured.Ty} {payload : Payload carriers} :
    (payload.value ty).isSome = decide (payload.ty = ty) := by
  cases ty <;> cases payload <;> simp [value, Payload.ty]
  all_goals split <;> simp_all

end Payload

/-- The history retains actual typed data and the full request occurrence. -/
inductive Event (carriers : Structured.Carriers) where
  | message (origin : Origin) (value : Payload carriers)
  | challenge (origin : Origin)
  | publicBinding (binding : PublicBinding (Payload carriers))

abbrev History (carriers : Structured.Carriers) := List (Event carriers)
abbrev Proof (carriers : Structured.Carriers) := List (Payload carriers)
abbrev Actions (carriers : Structured.Carriers) := Structured.participantInterfaceOn carriers

/-- A challenge's result type is fixed by its recorded request. Other events
use the singleton carrier: arbitrary oracle queries at those keys reveal no
information, and the participant interface never decodes them as challenges. -/
abbrev Raw {carriers : Structured.Carriers} : Event carriers → Type
  | .challenge origin =>
      match origin.request with
      | some request =>
          match request.sort with
          | .field domain => carriers.Field domain
          | _ => Unit
      | none => Unit
  | _ => Unit

def receivedValue {carriers : Structured.Carriers} (context : Context)
    (ty : Structured.Ty) (site : String) (sender : Nat) :
    Event carriers → Option (carriers.Value ty)
  | .message origin payload =>
      if origin = context.message site sender context.validator then payload.value ty else none
  | _ => none

/-- The same generic transform interface, now with nominally typed payloads and
the requested field at each query. -/
def interface {carriers : Structured.Carriers} (context : Context) :
    Transcript.Interface (Actions carriers) (Event carriers) (Payload carriers) Raw
  | .receive ty site sender =>
      .receive (fun payload => .message (context.message site sender context.validator) payload)
        (receivedValue context ty site sender)
  | .send (ty := ty) site receiver sent =>
      match Payload.ofValue ty sent with
      | some payload =>
          .send (.message (context.message site context.validator receiver) payload) ()
      | none => .refuse
  | .query site field _ =>
      .query (.challenge (context.query site (.draw field))) some

def transform {carriers : Structured.Carriers} {m : Type → Type} [Monad m]
    {A : Type} (context : Context)
    (oracle : History carriers → (event : Event carriers) → m (Raw event)) :
    PIR.Process (Actions carriers) A → History carriers → Proof carriers →
      m (PIR.Outcome A × Proof carriers) :=
  Transcript.transform (interface context) oracle

end Zkc.Construction.Domain
