import Tools.Interactive.ReferenceState
import Tools.Interactive.ServiceDomain
import Tools.Interactive.Sampling

/-! Logical resource transitions, independent of native handles and frame views.

Only the interpreter updates generation, budget and nonce stage. A finite tape
or nonce secret is selected at issuance. Nonce group calculations use the exact
mathematical service; scalar response arithmetic is computed here independently.
-/

set_option autoImplicit false

namespace Tools.Interactive.Reference

def updateResource (identity : Name) (change : Resource → Resource) : RunM Unit :=
  modify fun state => { state with resources := state.resources.map fun r =>
    if r.identity == identity then change r else r }

def consumeResource (location : Location) (kind : String)
    (identity : Name) (generation : Nat) (domain : String := Bindings.fr)
    (draw : Bool := true) : RunM ResourcePayload := do
  let state ← get
  let some resource := state.resources.find? (fun r => r.identity == identity)
    | failAt location "refused" "capability-unissued"
  require location (resource.generation == generation) "capability-stale"
  require location (resource.payload.kind == kind) "capability-kind"
  require location (resource.payload.domain == domain) "capability-identity"
  require location (resource.owner == location.scope.role &&
    resource.boundInstance.all (· == location.scope.binding)) "capability-domain"
  -- Issued counters start at zero and bounded reference work cannot wrap u64.
  -- The consuming attempt survives budget refusal; payload transitions occur
  -- only once budget succeeds, exactly as in the selected native contract.
  updateResource identity fun r => { r with generation := generation + 1, draws := r.draws + (if draw then 1 else 0) }
  if !draw then return resource.payload
  if resource.budget == 0 then failAt location "exhausted" "resource-budget"
  updateResource identity fun r => { r with budget := r.budget - 1 }
  return resource.payload

/-- A fresh logical identity, with no payload, randomness, or provider call. -/
def createResourceUnit (location : Location) (domain : String) : RunM Value := do
  let state ← get
  let identity := "$resource_unit." ++ toString state.nextResourceUnit
  let resource : Resource := ⟨identity, location.scope.role, none, 0, .resourceUnit domain, 0, 0⟩
  set { state with resources := resource :: state.resources, nextResourceUnit := state.nextResourceUnit + 1 }
  return .resourceUnit domain identity 0

def rngValue (domain : RandomDomain) (identity : Name) (generation : Nat) : Value :=
  match domain with
  | .bls => .rng identity generation | .ristretto => .rrng identity generation
  | .bn254 => .brng identity generation

def nonceValue (domain : ServiceDomain) (identity : Name) (generation : Nat) : Value :=
  match domain with | .bls => .nonce identity generation | .ristretto => .rnonce identity generation

private def rngPayload : (domain : RandomDomain) → List (ScalarReference.Scalar domain.scalar) → ResourcePayload
  | .bls, tape => .rng tape | .ristretto, tape => .rrng tape | .bn254, tape => .brng tape

private def rngTape : (domain : RandomDomain) → ResourcePayload → Result (List (ScalarReference.Scalar domain.scalar))
  | .bls, .rng tape => .ok tape | .ristretto, .rrng tape => .ok tape
  | .bn254, .brng tape => .ok tape
  | _, _ => .error "capability-kind"

def randomDraw (location : Location) (identity : Name) (generation : Nat)
    (domain : RandomDomain := .bls) : RunM (List Value) := do
  let payload ← consumeResource location "rng" identity generation domain.identity
  let tape ← checked location (rngTape domain payload)
  let value :: tape := tape | failAt location "exhausted" "test-tape"
  updateResource identity fun r => { r with payload := rngPayload domain tape }
  return [Value.fromArithmetic domain.scalar (.field value), rngValue domain identity (generation + 1)]

/-- One atomic vector transition: all capability and total-budget checks precede
the generation advance and length-sized debit. Entropy failure keeps that full
transition and any consumed tape prefix. Logical storage is bounded here; native
allocation reservation is outside this reference's accounting scope. -/
def randomVector (location : Location) (domain : RandomDomain)
    (identity : Name) (generation count : Nat) : RunM (List Value) := do
  require location (count ≤ Zkc.Algebra.FiniteVectors.limit) "vector-limit"
  let some resource := (← get).resources.find? (fun r => r.identity == identity)
    | failAt location "refused" "capability-unissued"
  require location (resource.generation == generation) "capability-stale"
  require location (resource.payload.kind == "rng") "capability-kind"
  require location (resource.payload.domain == domain.identity) "capability-identity"
  require location (resource.owner == location.scope.role &&
    resource.boundInstance.all (· == location.scope.binding)) "capability-domain"
  if resource.budget < count then failAt location "exhausted" "resource-budget"
  let mut tape ← checked location (rngTape domain resource.payload)
  updateResource identity fun r => { r with
    generation := generation + 1
    draws := r.draws + count
    budget := r.budget - count }
  let mut values := []
  for _ in [:count] do
    let value :: rest := tape | failAt location "exhausted" "test-tape"
    tape := rest
    updateResource identity fun r => { r with payload := rngPayload domain tape }
    values := value :: values
  return [Value.fromArithmetic domain.scalar (.vector values.reverse), rngValue domain identity (generation + 1)]

def extensionDraw (location : Location) (identity : Name) (generation : Nat)
    (bound : Option Nat) : RunM (List Value) := do
  if let some n := bound then require location (Sampling.validBound n) "query-bound"
  let .erng tape ← consumeResource location "rng" identity generation Bindings.koalaBearExt8
    | failAt location "refused" "capability-kind"
  let value :: rest := tape | failAt location "exhausted" "test-tape"
  updateResource identity fun r => { r with payload := .erng rest }
  let value ← match bound, value with
    | none, .field x => pure (Value.extension (.field x))
    | some bound, .index n =>
        pure (Value.fromArithmetic .bls (.index (n % bound)))
    | _, _ => failAt location "refused" "extension-rng-tape"
  return [value, .erng identity (generation + 1)]

def extensionVector (location : Location) (identity : Name) (generation count : Nat) : RunM (List Value) := do
  require location (count ≤ 1048576) "vector-limit"
  let some resource := (← get).resources.find? (fun r => r.identity == identity)
    | failAt location "refused" "capability-unissued"
  require location (resource.generation == generation) "capability-stale"
  require location (resource.payload.kind == "rng") "capability-kind"
  require location (resource.payload.domain == Bindings.koalaBearExt8) "capability-identity"
  require location (resource.owner == location.scope.role && resource.boundInstance.all (· == location.scope.binding)) "capability-domain"
  if resource.budget < count then failAt location "exhausted" "resource-budget"
  let .erng tape := resource.payload | failAt location "refused" "capability-kind"
  updateResource identity fun r => { r with generation := generation + 1, draws := r.draws + count, budget := r.budget - count }
  let mut values := []
  let mut tape := tape
  for _ in [0:count] do
    let value :: rest := tape | failAt location "exhausted" "test-tape"
    tape := rest
    updateResource identity fun r => { r with payload := .erng tape }
    let .field x := value | failAt location "refused" "extension-rng-tape"
    values := x :: values
  return [Value.extension (.vector values.reverse), .erng identity (generation + 1)]

private def noncePayload : (domain : ServiceDomain) → NonceState (ScalarReference.Scalar domain.scalar) → ResourcePayload
  | .bls, stage => .nonce stage | .ristretto, stage => .rnonce stage

private def nonceStage : (domain : ServiceDomain) → ResourcePayload → Result (NonceState (ScalarReference.Scalar domain.scalar))
  | .bls, .nonce stage => .ok stage | .ristretto, .rnonce stage => .ok stage
  | _, _ => .error "capability-kind"

private def takeNonce (location : Location) (domain : ServiceDomain)
    (identity : Name) (generation : Nat) : RunM (NonceState (ScalarReference.Scalar domain.scalar)) := do
  let payload ← consumeResource location "nonce" identity generation domain.identity
  let previous ← checked location (nonceStage domain payload)
  updateResource identity fun r => { r with payload := noncePayload domain .spent }
  return previous

def nonceCommitFor (location : Location) (domain : ServiceDomain) (bases : Value)
    (identity : Name) (generation : Nat) : RunM (List Value) := do
  let .issued secret ← takeNonce location domain identity generation
    | failAt location "refused" "nonce-stage"
  updateResource identity fun r => { r with payload := noncePayload domain (.committed secret) }
  let [points] ← external location "curve.scale_many" [bases.ty.identity] []
      [bases, Value.fromArithmetic domain.scalar (.field secret)]
    | failAt location "refused" "primitive-response"
  require location (points.ty == bases.ty && points.size == bases.size) "group-count"
  return [points, nonceValue domain identity (generation + 1)]

def nonceCommit (location : Location) (bases : ByteArray) (identity : Name)
    (generation : Nat) : RunM (List Value) :=
  nonceCommitFor location .bls (.groups bases) identity generation

def nonceResponseFor (location : Location) (domain : ServiceDomain)
    (secret challenge : ScalarReference.Scalar domain.scalar) (identity : Name) (generation : Nat) : RunM (List Value) := do
  let .committed nonce ← takeNonce location domain identity generation
    | failAt location "refused" "nonce-stage"
  return [Value.fromArithmetic domain.scalar (.field (nonce + challenge * secret))]

def nonceResponse (location : Location) (secret challenge : Math.Fr)
    (identity : Name) (generation : Nat) : RunM (List Value) :=
  nonceResponseFor location .bls secret challenge identity generation

end Tools.Interactive.Reference
