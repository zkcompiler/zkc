import Tools.Interactive.ReferenceValue
import Tools.Interactive.Explicit
import Tools.Interactive.Control

/-! Explicit reference service state and exact mathematical request boundary.

The state is outside ExceptT so a failed attempt preserves its completed prefix.
Resource state is interpreter-owned; provider replies cannot install successors.
These development fixtures and service requests are not adversary observations.
-/

set_option autoImplicit false

namespace Tools.Interactive.Reference
open Lean (Json)

structure Location where
  session : String
  entry : Name
  scope : Control.Scope
  definition : Option Explicit.Origin := none
  interactionPath : Array Json := #[]

/-- A location with no frames, no explicit definition and no interaction path.

That is what a consumer names when the test is about something else, and nine
of the suite's fixtures wrote it out positionally -- where a changed field
order would have been a silent re-interpretation rather than an error, because
every field it fixes has a default and the four that vary are all strings. -/
def Location.plain (session binding site role : String) (entry : Name := "main") :
    Location :=
  { session := session, entry := entry, scope := ⟨binding, [], site, role⟩ }

private def frameJson : Control.Frame → Json
  | .call site => .arr #[.str "call", .str site]
  | .iteration site i => .arr #[.str "iteration", .str site, .str (toString i)]
  | .localMatch site alternative => .arr #[.str "match", .str site, .str alternative]
  | .localBranch site selected => .arr #[.str "if", .str site, .str (if selected then "then" else "else")]
  | .localIteration site i => .arr #[.str "for", .str site, .str (toString i)]
  | .localCall site function => .arr #[.str "local", .str site, .str function]

def Location.json (location : Location) : Json :=
  .arr #[.str "source-origin/2", .str location.session, .str location.entry,
    .str location.scope.binding, .arr (location.scope.path.map frameJson).toArray,
    .str location.scope.site, .str location.scope.role,
    match location.definition with
    | none => .arr #[]
    | some definition => .arr #[.str definition.definition,
        .arr (definition.arguments.map fun (name, value) => .arr #[.str name, .str value]).toArray]]

structure Fault where
  reason : String
  detail : String
  location : Location

inductive NonceState (F : Type := Math.Fr) where
  | issued (secret : F)
  | committed (secret : F)
  | spent

inductive ResourcePayload where
  | resourceUnit (domain : String)
  | brng (tape : List (ScalarReference.Scalar .bn254))
  | erng (tape : List ExtensionReference.Data)
  | rrng (tape : List (ScalarReference.Scalar .ristretto))
  | rnonce (stage : NonceState (ScalarReference.Scalar .ristretto))
  | rng (tape : List Math.Fr)
  | nonce (stage : NonceState)
  | transcript (suite : String) (root : ByteArray) (history : Array Json)

def ResourcePayload.kind : ResourcePayload → String
  | .resourceUnit _ => "resource_unit"
  | .rng _ | .rrng _ | .erng _ | .brng _ => "rng"
  | .nonce _ | .rnonce _ => "nonce"
  | .transcript .. => "transcript"

def ResourcePayload.stage : ResourcePayload → String
  | .resourceUnit _ => "resource_unit"
  | .rng _ | .rrng _ | .erng _ | .brng _ => "rng"
  | .nonce (.issued _) | .rnonce (.issued _) => "issued"
  | .nonce (.committed _) | .rnonce (.committed _) => "committed"
  | .nonce .spent | .rnonce .spent => "spent"
  | .transcript .. => "transcript"

def ResourcePayload.domain : ResourcePayload → String
  | .resourceUnit domain => domain
  | .brng _ => Bindings.bn254Fr
  | .erng _ => Bindings.koalaBearExt8
  | .rrng _ | .rnonce _ => Bindings.ristrettoScalar
  | .rng _ | .nonce _ => Bindings.fr
  | .transcript suite .. => suite

structure Resource where
  identity : Name
  owner : Name
  boundInstance : Option Name
  budget : Nat
  payload : ResourcePayload
  generation : Nat := 0
  draws : Nat := 0

structure State where
  setupKeys : List (Name × List CommitmentIdentity) := []
  receivingKeys : List (Json × CommitmentIdentity) := []
  resources : List Resource := []
  nextResourceUnit : Nat := 0
  answers : Std.HashMap String Json := {}
  usedAnswers : Std.HashSet String := {}
  replies : List (Json × Value) := []
  events : Array Json := #[]
  spent : Nat := 0
  iterations : Nat := 0
  fault : Option Fault := none
  pendingFaults : List (Name × Fault) := []

abbrev RunM := ExceptT Fault (StateM State)

def failAt {α : Type} (location : Location) (reason detail : String) : RunM α :=
  throw ⟨reason, detail, location⟩

def checked {α : Type} (location : Location) : Result α → RunM α
  | .ok value => pure value
  | .error code => failAt location "refused" code

def require (location : Location) (condition : Bool) (detail : String) : RunM Unit :=
  checked location (ensure condition detail)

def charge (location : Location) (weight : Nat := 1) : RunM Unit := do
  let state ← get
  if state.spent + weight > limits.steps then failAt location "exhausted" "reference-work-limit"
  set { state with spent := state.spent + weight }

def event (location : Location) (record : Json) (weight : Nat := 1) : RunM Unit := do
  charge location weight
  modify fun state => { state with events := state.events.push record }

def requestJson (location : Location) (contract : String) (arguments attributes : List String)
    (inputs : List Value) : Json :=
  .arr #[.str "zkc.reference-primitive/2", location.json, .str contract,
    .arr (arguments.map Json.str).toArray, .arr (attributes.map Json.str).toArray, valuesJson inputs]

/-- Replies are an explicit service assumption. A missing exact request stops
with its request in the event prefix; a reply for another site cannot fill it. -/
def oracle (location : Location) (request : Json) (weight : Nat := 1) : RunM Json := do
  event location (.arr #[.str "external", request]) weight
  let state ← get
  let key := request.compress
  let some reply := state.answers[key]?
    | failAt location "pending-primitive" "exact-request-missing"
  modify fun state => { state with usedAnswers := state.usedAnswers.insert key }
  return reply

def successfulReply (location : Location) (reply : Json) : RunM Json := do
  match ← checked location (Decode.array reply) with
  | [.str "ok", value] => return value
  | [.str "error", .str reason, .str detail] =>
      require location (["refused", "reject", "exhausted"].contains reason) "primitive-error-reason"
      failAt location reason detail
  | _ => failAt location "refused" "primitive-response"

def external (location : Location) (contract : String) (arguments attributes : List String)
    (inputs : List Value) : RunM (List Value) := do
  let reply ← successfulReply location (← oracle location (requestJson location contract arguments attributes inputs))
  checked location ((← checked location (Decode.array reply)).mapM decodeValue)

def authorized (state : State) (role : Name) (value : Value) : Result Unit := do
  for leaf in value.leaves do
   if let some identity ← leaf.commitmentIdentity then
    let keys := (state.setupKeys.find? (fun row => row.1 == role)).map Prod.snd |>.getD []
    ensure (keys.any (· == identity)) "unauthorized-setup"

def validatePublic (location : Location) (value : Value) : RunM Unit := do
  require location value.public "nonserializable-message"
  checked location (authorized (← get) location.scope.role value)
  match value with
  | .bnGroup .. | .rgroup _ | .rgroups _ | .group _ | .groups _ | .commitment _ | .proof _ =>
      let result ← external location "validate" [value.ty.identity] [] [value]
      require location result.isEmpty "validation-response"
  | _ => pure ()

def State.resourcesJson (state : State) : Json :=
  .arr (state.resources.map fun r => .arr #[.str r.identity, .str r.owner,
    r.boundInstance.map Json.str |>.getD (.arr #[]), .str (toString r.generation),
    .str (toString r.draws), .str (toString r.budget), .str r.payload.stage]).toArray

end Tools.Interactive.Reference
