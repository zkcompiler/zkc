module

public import Zkc.Construction.Participant
public import Zkc.Construction.Binding
public import Zkc.Source.Participant
public import Zkc.Source.Common.Scalar
public import Zkc.Transcript.Interface

@[expose] public section

/-! The Fiat–Shamir transform of validator processes.

`transform` is the Fiat–Shamir transform of any validator process over the
common participant actions: received messages come from a proof list and are
absorbed, each `query` is answered by the transcript challenge function on the
absorbed history followed by its own occurrence, and each challenge delivery to
the producer is absorbed instead of sent. It is the generic transform of
`Zkc.Transcript` at the transcript interface of the common participant actions
(`Context.interface`): raw answers are field elements decoded by the identity,
and the oracle at a history before an occurrence and the occurrence is the
challenge function at their concatenation. The transform is independent of any
compiled program; `Zkc.Construction.Semantics` gives exported programs their
ideal and interactive meanings and `Zkc.Construction.Rule` checks that the first
is the transform of the second. Treating the native suite's challenge function
as a random oracle is a named assumption of a security consumer, not of the
transform.
-/

set_option autoImplicit false

namespace Zkc.Construction
open Zkc.Source Zkc.Source.Common.Native

variable {F G : Type}

/-- Data absorbed by observations and carried by proof messages. -/
inductive Payload (F G : Type) where
  | boolean (value : Bool)
  | field (domain : String) (value : F)
  | group (domain : String) (value : G)
  deriving DecidableEq, Repr

namespace Payload

def ty : Payload F G → Ty
  | .boolean _ => .boolean
  | .field domain _ => .field domain
  | .group domain _ => .group domain

def ofValue : (ty : Ty) → ScalarValue F G ty → Option (Payload F G)
  | .boolean, value => some (.boolean value)
  | .field domain, value => some (.field domain value)
  | .group domain, value => some (.group domain value)
  | .service _, _ => none

/-- Decoding at an expected type requires the same kind and nominal domain. -/
def value : (ty : Ty) → Payload F G → Option (ScalarValue F G ty)
  | .boolean, .boolean value => some value
  | .field domain, .field other value => if domain = other then some value else none
  | .group domain, .group other value => if domain = other then some value else none
  | _, _ => none

theorem value_some {ty : Ty} {payload : Payload F G} {decoded : ScalarValue F G ty}
    (decodes : payload.value ty = some decoded) : ofValue ty decoded = some payload := by
  cases ty <;> cases payload <;> simp_all [value, ofValue]

theorem value_isSome {ty : Ty} {payload : Payload F G} :
    (payload.value ty).isSome = decide (payload.ty = ty) := by
  cases ty <;> cases payload <;> simp [value, Payload.ty]
  all_goals (split <;> simp_all [eq_comm])

end Payload

/-- Absorbed transcript events. `binding` is the host's initialization with the
authorized public context and scalar public values, and `publicBinding` the
initialization with a typed public-value binding event, whose vectors, indices
and counts are bound as typed values; neither is an operation of the
participant program. -/
inductive Event (F G : Type) where
  | binding (context : String) (values : List (Payload F G))
  | message (origin : Origin) (value : Payload F G)
  | challenge (origin : Origin)
  | publicBinding (binding : PublicBinding (Payload F G))
  deriving DecidableEq, Repr

abbrev History (F G : Type) := List (Event F G)

/-- Proof messages, in their delivered order and at their typed values. -/
abbrev Proof (F G : Type) := List (Payload F G)

/-- The common participant actions of a validator. -/
abbrev Actions (F G : Type) := Participant.interface Nat Ty services (ScalarValue F G)

/-- Deployment facts that fix occurrence identities: original entry, role
roster, producer and validator positions, the replaced service's original input
index, contract and the typed request its challenges carry, and the ordered
query/delivery sites. -/
structure Context where
  entry : String
  roles : List String
  producer : Nat
  validator : Nat
  service : Nat
  contract : String
  request : Option Request
  suite : String
  draws : List (String × String)
  deriving DecidableEq, Repr

/-- One decimal digit; larger arguments spell `9`. -/
def decimalDigit : Nat → String
  | 0 => "0" | 1 => "1" | 2 => "2" | 3 => "3" | 4 => "4"
  | 5 => "5" | 6 => "6" | 7 => "7" | 8 => "8" | _ => "9"

/-- The canonical decimal spelling of an index below `10000`, as used in native
service port names. It is built from literals so that kernel evaluation reduces
it. -/
def decimal (index : Nat) : String :=
  if index < 10 then decimalDigit index
  else if index < 100 then decimalDigit (index / 10) ++ decimalDigit (index % 10)
  else if index < 1000 then
    decimalDigit (index / 100) ++ decimalDigit (index / 10 % 10) ++ decimalDigit (index % 10)
  else
    decimalDigit (index / 1000 % 10) ++ decimalDigit (index / 100 % 10) ++
      decimalDigit (index / 10 % 10) ++ decimalDigit (index % 10)

namespace Context

def role (context : Context) (index : Nat) : String := context.roles.getD index ""

def message (context : Context) (site : String) (sender receiver : Nat) : Origin :=
  .message context.entry site (context.role sender) (context.role receiver)

/-- The selected query's occurrence names the replaced service's original port
and contract, which the original export fixes, and carries the query's typed
request. -/
def query (context : Context) (site : String) (request : Request) : Origin :=
  .query context.entry site ("input_" ++ decimal context.service) context.contract
    (context.role context.validator) request

end Context

/-- The reply a received message event carries: the payload at the expected
message occurrence, decoded at the expected type. -/
def Context.receivedValue (context : Context) (ty : Ty) (site : String) (sender : Nat) :
    Event F G → Option (ScalarValue F G ty)
  | .message origin payload =>
      if origin = context.message site sender context.validator then payload.value ty else none
  | _ => none

/-- The transcript interface of the common participant actions: a receive
absorbs its message occurrence with the payload and recovers the payload's value
at the expected type, a send absorbs its message occurrence with the sent value
(refusing a value without a payload), and every query absorbs its challenge
occurrence, whose typed request is the draw of its field, and reads the raw
field answer as the challenge. -/
def Context.interface (context : Context) :
    Transcript.Interface (Actions F G) (Event F G) (Payload F G) (fun _ => F)
  | .receive ty site sender =>
      .receive (fun payload => .message (context.message site sender context.validator) payload)
        (context.receivedValue ty site sender)
  | .send (ty := ty) site receiver sent =>
      match Payload.ofValue ty sent with
      | some payload =>
          .send (.message (context.message site context.validator receiver) payload) ()
      | none => .refuse
  | .query site field _ =>
      .query (.challenge (context.query site (.draw field))) some

section Transform
variable {m : Type → Type} [Monad m]

/-- The Fiat–Shamir transform of a validator process whose every query is a
selected challenge. Receives read the proof in order and absorb the decoded
message; a decoding failure refuses without consuming. Every query is answered
by `challenge` on the history ending with its occurrence, which is absorbed;
the occurrence carries the query's typed request, the draw of its field. A
send is absorbed with its message occurrence and produces no proof data. Returns
the outcome and the unread proof suffix. It is the generic transform at the
context's transcript interface. -/
def transform {A : Type} (context : Context) (challenge : History F G → m F) :
    PIR.Process (Actions F G) A → History F G → Proof F G → m (PIR.Outcome A × Proof F G) :=
  Transcript.transform context.interface fun preceding event => challenge (preceding ++ [event])

/-- The transform is the generic transform at the context's interface. -/
theorem transform_eq_transcript {A : Type} (context : Context) (challenge : History F G → m F) :
    transform (A := A) context challenge =
      Transcript.transform context.interface fun preceding event => challenge (preceding ++ [event]) :=
  rfl

theorem transform_eq_done {A : Type} (context : Context) (challenge : History F G → m F) (value : A)
    (history : History F G) (proof : Proof F G) :
    transform context challenge (.done value) history proof = pure (.returned value, proof) :=
  rfl

theorem transform_eq_halt {A : Type} (context : Context) (challenge : History F G → m F)
    (stop : PIR.Stop) (history : History F G) (proof : Proof F G) :
    transform (A := A) context challenge (.halt stop) history proof = pure (.stopped stop, proof) :=
  rfl

theorem transform_eq_receive {A : Type} (context : Context) (challenge : History F G → m F) (ty : Ty)
    (site : String) (sender : Nat)
    (next : (Actions F G).Reply (.receive ty site sender) → PIR.Process (Actions F G) A)
    (history : History F G) (proof : Proof F G) :
    transform context challenge (.call (.receive ty site sender) next) history proof =
      match proof with
      | [] => pure (.stopped .refused, [])
      | payload :: rest =>
          match payload.value ty with
          | some value => transform context challenge (next value)
              (history ++ [.message (context.message site sender context.validator) payload]) rest
          | none => pure (.stopped .refused, payload :: rest) := by
  cases proof with
  | nil => rfl
  | cons payload rest =>
      rw [transform_eq_transcript, Transcript.transform_receive _ _
        (show context.interface (.receive ty site sender) = _ from rfl)]
      simp only [Context.receivedValue, ite_true]
      cases Payload.value ty payload <;> rfl

theorem transform_eq_query {A : Type} (context : Context) (challenge : History F G → m F)
    (site : String) (field : services.Op) (arguments : Values (ScalarValue F G) (services.arguments field))
    (next : (Actions F G).Reply (.query site field arguments) → PIR.Process (Actions F G) A)
    (history : History F G) (proof : Proof F G) :
    transform context challenge (.call (.query site field arguments) next) history proof =
      (do
        let event := Event.challenge (context.query site (.draw field))
        let answer ← challenge (history ++ [event])
        transform context challenge (next answer) (history ++ [event]) proof) :=
  rfl

theorem transform_eq_send {A : Type} (context : Context) (challenge : History F G → m F) {ty : Ty}
    (site : String) (receiver : Nat) (sent : ScalarValue F G ty)
    (next : (Actions F G).Reply (.send site receiver sent) → PIR.Process (Actions F G) A)
    (history : History F G) (proof : Proof F G) :
    transform context challenge (.call (.send site receiver sent) next) history proof =
      match Payload.ofValue ty sent with
      | some payload => transform context challenge (next ())
          (history ++ [.message (context.message site context.validator receiver) payload]) proof
      | none => pure (.stopped .refused, proof) := by
  change Transcript.transform context.interface _ (.call (.send site receiver sent) next) history
    proof = _
  cases encoded : Payload.ofValue ty sent with
  | none =>
      rw [Transcript.transform_refuse _ _ (by simp [Context.interface, encoded])]
  | some payload =>
      rw [Transcript.transform_send _ _ (event := .message (context.message site context.validator
        receiver) payload) (value := ()) (by simp [Context.interface, encoded])]
      rfl

end Transform

end Zkc.Construction
