module

public import Zkc.Construction.Context
public import Zkc.Construction.Binding
public import Zkc.Transcript.Interface
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

/-- Data transported in a proof or bound in a public statement. The nominal
sort determines the existing recursive value interpretation. Eligibility excludes
services and logical oracle handles recursively; it does not assume relation validity or finite size. -/
structure Payload (carriers : Structured.Carriers) where
  ty : Structured.Ty
  admissible : ty.isHandle = false
  contents : carriers.Value ty

namespace Payload
variable {carriers : Structured.Carriers}

/-- Smart constructors retain concise scalar patterns without a second data
universe. General products and sequences use the same dependent constructor. -/
@[match_pattern] abbrev boolean (value : Bool) : Payload carriers := ⟨.boolean, rfl, value⟩
@[match_pattern] abbrev index (value : Nat) : Payload carriers := ⟨.index, rfl, value⟩
@[match_pattern] abbrev field (domain : String) (value : carriers.Field domain) : Payload carriers :=
  ⟨.field domain, rfl, value⟩
@[match_pattern] abbrev vector (domain : String) (value : List (carriers.Field domain)) : Payload carriers :=
  ⟨.vector domain, rfl, value⟩
@[match_pattern] abbrev group (domain : String) (value : carriers.Group domain) : Payload carriers :=
  ⟨.group domain, rfl, value⟩

def ofValue (ty : Structured.Ty) (contents : carriers.Value ty) : Option (Payload carriers) :=
  if admissible : ty.isHandle = false then some ⟨ty, admissible, contents⟩ else none

/-- Only exact nominal equality authorizes transport. Equal host carrier types
cannot identify different fields, products, constructors or ordered fields. -/
def value (ty : Structured.Ty) (payload : Payload carriers) : Option (carriers.Value ty) :=
  if same : payload.ty = ty then some (same ▸ payload.contents) else none

theorem value_ofValue {ty : Structured.Ty} {input : carriers.Value ty}
    {payload : Payload carriers} (encoded : ofValue ty input = some payload) :
    payload.value ty = some input := by
  unfold ofValue at encoded
  split at encoded
  · cases Option.some.inj encoded
    simp [value]
  · cases encoded

theorem ofValue_value {ty : Structured.Ty} {payload : Payload carriers}
    {output : carriers.Value ty} (decoded : payload.value ty = some output) :
    ofValue ty output = some payload := by
  rcases payload with ⟨actual, admissible, contents⟩
  unfold value at decoded
  simp only at decoded
  split at decoded
  · rename_i same
    subst actual
    simp only [Option.some.injEq] at decoded
    subst output
    simp [ofValue, admissible]
  · cases decoded

theorem value_isSome {ty : Structured.Ty} {payload : Payload carriers} :
    (payload.value ty).isSome = decide (payload.ty = ty) := by
  unfold value
  split <;> simp_all

theorem value_wrong_type {ty : Structured.Ty} {payload : Payload carriers}
    (different : payload.ty ≠ ty) : payload.value ty = none := by
  simp [value, different]

/-- A logical handle cannot occur even inside an otherwise ordinary aggregate. -/
theorem value_handle_refused {ty : Structured.Ty} (handle : ty.isHandle = true)
    (payload : Payload carriers) : payload.value ty = none := by
  apply value_wrong_type
  intro same
  have admissible := payload.admissible
  rw [same, handle] at admissible
  cases admissible

/-- Fixed-sort packaging is injective; eligibility proof witnesses carry no identity. -/
@[simp] theorem mk_inj {ty : Structured.Ty} {firstProof secondProof : ty.isHandle = false}
    {first second : carriers.Value ty} :
    (Payload.mk ty firstProof first : Payload carriers) = ⟨ty, secondProof, second⟩ ↔
      first = second := by
  constructor
  · intro same
    have decoded := congrArg (value ty) same
    simpa [value] using decoded
  · rintro rfl
    rfl

theorem ofValue_injective {ty : Structured.Ty} (admissible : ty.isHandle = false) :
    Function.Injective (ofValue (carriers := carriers) ty) := by
  intro first second same
  have decoded := congrArg (fun encoded => encoded >>= value ty) same
  simpa [ofValue, admissible, value] using decoded

end Payload

/-- One public row uses the same nominal data as proof messages. Coordinates
are original source positions; the request fixes their order and the schema. -/
structure PublicBinding (carriers : Structured.Carriers) where
  application : String
  row : List (Nat × Payload carriers)

/-- The history retains actual typed data and the full request occurrence. -/
inductive Event (carriers : Structured.Carriers) where
  | message (origin : Origin) (value : Payload carriers)
  | challenge (origin : Origin)
  | publicBinding (binding : PublicBinding carriers)

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
      match context.profile with
      | .plain => .refuse
      | .fiatShamir _ => .query (.challenge (context.query site (.draw field))) some

def transform {carriers : Structured.Carriers} {m : Type → Type} [Monad m]
    {A : Type} (context : Context)
    (oracle : History carriers → (event : Event carriers) → m (Raw event)) :
    PIR.Process (Actions carriers) A → History carriers → Proof carriers →
      m (PIR.Outcome A × Proof carriers) :=
  Transcript.transform (interface context) oracle

end Zkc.Construction.Domain

-- Own the shared decoding equations before independent readers request them.
run_cmd Lean.Elab.Command.liftTermElabM do
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Construction.Domain.receivedValue
