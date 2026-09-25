import Tools.Artifact.Configuration
import Tools.Artifact.Transcript
import Tools.Artifact.Oracle
import Tools.Interactive.MatrixIdentity

/-! A public-primitive boundary for the independent source validator. Replies
are keyed by complete requests. State is outside ExceptT: failures keep reached
requests, transcript actions, cursor consumption and resource transitions. -/

set_option autoImplicit false

namespace Tools.Artifact
open Lean (Json)
open Tools.Interactive

structure Failure where
  reason : String
  detail : String
  request : Json := .null

structure OracleReply where
  request : Json
  response : Json

structure State where
  cursor : Cursor
  root : ByteArray
  configuration : Json
  answers : Array OracleReply
  setups : SetupConfiguration := { keys := [] }
  transcriptBudget : Nat := 100000
  usedAnswers : List Nat := []
  history : Array Json := #[]
  events : Array Json := #[]
  requests : Array Json := #[]
  draws : Nat := 0
  transcriptActions : Nat := 0
  spent : Nat := 0
  iterations : Nat := 0

abbrev RunM := ExceptT Failure (StateM State)

def fail {α : Type} (reason detail : String) (request : Json := .null) : RunM α :=
  throw ⟨reason, detail, request⟩

def checked {α : Type} (result : Result α) : RunM α :=
  match result with
  | .ok value => pure value
  | .error e =>
      -- These codes denote the selected finite execution policy, not malformed
      -- representation. Preserve the distinction in failure observations.
      fail (if e == "arity-limit" || e == "group-limit" then "exhausted" else "refused") e

def require (condition : Bool) (detail : String) : RunM Unit :=
  checked (ensure condition detail)

def charge : RunM Unit := do
  let state ← get
  if state.spent ≥ limits.steps then fail "exhausted" "reference-work-limit"
  set { state with spent := state.spent + 1 }

def event (e : Json) : RunM Unit := do
  charge
  modify fun s => { s with events := s.events.push e }

/-- A missing exact public request is observable, never inferred from the next
reply or an ordinal tape. A host can evaluate that request and rerun with a
larger authenticated primitive cache. This tool is an executable reference,
not a proof checker for arbitrary cache providers. -/
def oracle (request : Json) : RunM Json := do
  charge
  modify fun s => { s with requests := s.requests.push request }
  let state ← get
  let some index := state.answers.findIdx? (fun r => r.request == request)
    | fail "pending-primitive" "exact-request-missing" request
  let some reply := state.answers[index]? | fail "refused" "primitive-index"
  modify fun s => { s with usedAnswers := index :: s.usedAnswers }
  return reply.response

def primitive (_source : Source) (name : String) (arguments attrs : List String)
    (inputs : List Value) (selected : Option Name := none) : RunM (List Json) := do
  let values ← checked (inputs.mapM (Value.jsonFor))
  let state ← get
  let request ← do
      let keys ← match selected with
        | none => pure state.setups.keys
        | some name => do pure [(name, ← checked (lookup name state.setups.keys))]
      let records ← checked (keys.mapM fun (name, value) => do
        let [.str ty, wire] ← Decode.array (← value.jsonFor) | throw "primitive-key-record"
        return Json.arr #[.str name, .str ty, wire])
      pure (Json.arr #[.str "zkc.public-primitive/1", .arr records.toArray,
        .str name, .arr (arguments.map Json.str).toArray,
        .arr (attrs.map Json.str).toArray, .arr values.toArray])
  match ← checked (Decode.array (← oracle request)) with
  | .str "ok" :: outputs => return outputs
  | [.str "error", .str detail] => fail "refused" detail
  | _ => fail "refused" "primitive-response"

def validatePublic (source : Source) (v : Value) (selected : Option Name := none) : RunM Unit := do
  match v with
  | .nominalBytes .. | .publicBytes .. | .verifierKey .. =>
      if requiresSetup (← checked (v.typeFor)) then
        let some key := selected | fail "refused" "artifact-setup-required"
        checked (checkSetup (← get).setups key v)
      let [] ← primitive source "validate" [] [] [v] selected | fail "refused" "validation-response"
      pure ()
  | .selectedRng _ | .ristrettoRng _ | .extensionRng _ => fail "refused" "nonserializable"
  | _ => pure ()

def decodeReplyValue (j : Json)  : Result Value := do
  let [.str ty, .str bytes] ← Decode.array j | throw "primitive-value"
  decodeValue ty (← unhex bytes)

def transcriptMessage (origin : Json) (value : Value) : RunM Unit := do
  let state ← get
  if state.transcriptActions ≥ state.transcriptBudget then fail "exhausted" "transcript-budget"
  let origin ← checked (treeBytes origin)
  let bytes ← checked value.wire
  let action := Json.arr #[.str "message", .str (hex origin), .str (hex bytes)]
  modify fun s => { s with
    history := s.history.push action
    transcriptActions := s.transcriptActions + 1 }
  event (.arr #[.str "message", .str (hex origin), .str (← checked (value.typeFor)), .str (hex bytes)])

/-- Complete one logical draw before recording its challenge event. The helper
owns the bounded rejection loop so an early successful sample cannot bypass
its caller's observation and type checks. -/
private def sampleChallenge (suite : String) (bound : Option Nat) : RunM Value := do
  let mut coordinates := []
  for attempt in [0:16] do
    if attempt > 0 then modify fun s => { s with history := s.history.push (.arr #[.str "challenge-continuation"]) }
    let state ← get
    let response ← oracle (← checked (transcriptRequest state.root state.history suite))
    let [.str "ok", .str encoded] ← checked (Decode.array response) | fail "refused" "transcript-response"
    let bytes ← checked (unhex encoded)
    require (bytes.size == 64) "transcript-challenge-width"
    if let some n := bound then return Value.fromArithmetic .bls (.index (← checked (Sampling.index bytes n)))
    if suite == Bindings.extensionTranscript then
      coordinates := coordinates ++ Sampling.coordinates bytes
      if let some x := Sampling.extension coordinates then return Value.extension (.field x)
    else
      let domain ← checked (ScalarReference.Domain.parse (← checked (Bindings.associatedIdentity suite "ChallengeField")))
      let integer := if domain == .ristretto then valueLE bytes else bytes.toList.foldl (fun n b => 256*n + b.toNat) 0
      return Value.fromArithmetic domain (.field (integer : ScalarReference.Scalar domain))
  fail "exhausted" "challenge-rejection-limit"

def challenge (_source : Source) (descriptor : Descriptor) (location : Location)
    (generation : Nat) (bound : Option Nat := none) : RunM Value := do
  if let some n := bound then
    require (descriptor.suite == Bindings.extensionTranscript && Sampling.validBound n) "query-bound"
  -- Ristretto is available only through the explicit suite-bearing primitive.
  -- Keep this guard at execution as well as descriptor ingress.
  require (Bindings.transcriptDomain descriptor.suite) "construction-transcript-suite"
  require (descriptor.draws.contains (location.function, location.operation)) "unselected-draw"
  require (location.role == descriptor.validator) "challenge-owner"
  require (generation == (← get).draws) "challenge-generation"
  let state ← get
  if state.transcriptActions ≥ state.transcriptBudget then fail "exhausted" "transcript-budget"
  -- Rejection retries extend primitive history inside one logical transition.
  modify fun s => { s with
    draws := s.draws + 1
    transcriptActions := s.transcriptActions + 1 }
  let origin ← checked (treeBytes location.challenge)
  modify fun s => { s with history := s.history.push (match bound with
    | none => .arr #[.str "challenge", .str (hex origin)]
    | some n => .arr #[.str "index", .str (hex origin), .str (toString n)]) }
  let value ← sampleChallenge descriptor.suite bound
  require (value.ty == (if bound.isSome then "index" else "field")) "challenge-type"
  event (.arr #[.str "challenge", .str (hex origin), ← checked (value.jsonFor)])
  return value

def observedValue (value : Value)  : Result Json :=
  match value with
  | .selectedRng _ | .ristrettoRng _ | .extensionRng _ => .ok (.arr #[.str "selected_rng"])
  | _ => value.jsonFor

private def groupCount (value : Value) : Result Nat := do
  ensure (value.ty == "groups") "group-kind"
  let bytes ← value.wire
  if let .nominalBytes identity _ _ := value then
    if identity == Bindings.ristrettoGroup then checkRistrettoWire "groups" bytes
    else checkBn254Wire identity "groups" bytes
  else
    let _ ← decodeWire "groups" bytes
  return valueLE (bytes.extract 6 10)

/-- Exact shape guards around public group primitives. This validator retains
materialized meanings; no diagonal allocator accounting is attributed to it. -/
private def groupShapes (name : String) (inputs : List Value) (attrs : List String) : Result (Option (List Nat)) := do
  match name, inputs with
  | "pairing.check", [xs, ys] =>
      ensure ((← groupCount xs) == (← groupCount ys)) "pairing-length"
      return none
  | "curve.msm", [scalars, bases] | "curve.scale_each", [scalars, bases] =>
      let .arithmetic _ (.vector xs) := scalars | throw "kernel-input-types"
      let n ← groupCount bases
      ensure (xs.length == n) "vector-shape"
      return if name == "curve.scale_each" then some [n] else none
  | "curve.vector_add", [xs, ys] =>
      let n ← groupCount xs
      ensure (n == (← groupCount ys)) "vector-shape"
      return some [n]
  | "curve.vector_scale", [xs, _] => return some [← groupCount xs]
  | "curve.empty", [] => return some [0]
  | "curve.append", [xs, _] =>
      let n ← groupCount xs
      ensure (n < 4096) "group-limit"
      return some [n + 1]
  | "curve.concat", [xs, ys] =>
      let n := (← groupCount xs) + (← groupCount ys)
      ensure (n ≤ 4096) "group-limit"
      return some [n]
  | "curve.split", [xs] =>
      let n ← groupCount xs
      ensure (n > 0 && n % 2 == 0) "group-split-shape"
      return some [n / 2, n / 2]
  | "curve.at", [xs] =>
      let [index] := attrs | throw "kernel-attributes"
      ensure ((← Decode.natural (.str index)) < (← groupCount xs)) "group-index"
      return none
  | _, _ => return none

def evaluate (source : Source) (descriptor : Descriptor) (location : Location)
    (name : String) (attrs : List String) (inputs : List Value) : RunM (List Value) := do
  let selected ← checked (selectOperation source name attrs)
  let signature := selected.signature
  require ((← checked (inputs.mapM (Value.typeFor))) == signature.inputs) "kernel-input-types"
  let name := selected.contract
  let request := location.request name attrs selected.arguments
  event (.arr #[.str "request", request, .arr (← checked (inputs.mapM (fun v => observedValue v))).toArray])
  let outputs ← if name == "matrix.identity_check" then do
      let [value] := inputs | fail "refused" "kernel-input-types"
      let hashRequest ← checked (match value with
        | .arithmetic domain data => MatrixIdentity.prime domain data
        | .extension data => MatrixIdentity.extension data
        | _ => .error "matrix-identity-type")
      pure [.boolean (← checked (MatrixIdentity.acceptsDigest attrs (← oracle hashRequest)))]
    else if Bindings.oracleContract name then
      checked (oracleCompute name (selected.arguments.headD "") inputs)
    else if name == "vector.embed" then do
      let [input] := inputs | fail "refused" "kernel-input-types"
      let .vector xs ← checked (input.toArithmetic .koalaBear) | fail "refused" "kernel-input-types"
      require (selected.arguments == [Bindings.koalaBearExt8] && attrs.isEmpty) "binding-static-arguments"
      pure [Value.fromExtension (.vector (xs.map ExtensionReference.embed))]
    else if name == "field.embed" then do
      let [input] := inputs | fail "refused" "kernel-input-types"
      let .field x ← checked (input.toArithmetic .koalaBear) | fail "refused" "kernel-input-types"
      require (selected.arguments == [Bindings.koalaBearExt8] && attrs.isEmpty) "binding-static-arguments"
      pure [Value.fromExtension (.field (ExtensionReference.embed x))]
    else if selected.arguments.head? == some Bindings.koalaBearExt8 && !name.startsWith "random." then do
      let values ← checked (inputs.mapM Value.toExtension)
      pure ((← checked (ExtensionReference.compute name attrs values)).map Value.fromExtension)
    else if ScalarReference.supported name then do
      let domain ← checked (ScalarReference.Domain.parse (selected.arguments.headD Bindings.fr))
      let values ← checked (inputs.mapM (Value.toArithmetic domain))
      pure ((← checked (ScalarReference.compute domain name attrs values)).map (Value.fromArithmetic domain))
    else match name, inputs with
    | "curve.length", [xs] =>
        pure [Value.fromArithmetic .bls (.index (← checked (groupCount xs)))]
    | "curve.get", [xs, index] => do
        let .index i ← checked (index.toArithmetic .bls) | fail "refused" "kernel-input-types"
        require (i < (← checked (groupCount xs))) "group-index"
        let wire ← checked xs.wire
        let ristretto := selected.arguments == [Bindings.ristrettoGroup]
        let identity := selected.arguments.headD ""
        let bn := identity == Bindings.bn254G1 || identity == Bindings.bn254G2
        let width := if bn then (if identity == Bindings.bn254G1 then 32 else 64)
          else if ristretto then 32 else 48
        let tag ← if bn then checked (bn254GroupTag identity "group") else pure (if ristretto then 16 else 9)
        let result := magic.push tag ++
          wire.extract (10 + i * width) (10 + (i + 1) * width)
        pure [← checked (decodeValue (signature.outputs.headD "group") result)]
    | "bool.and", [.boolean a, .boolean b] => pure [.boolean (a && b)]
    | "bool.not", [.boolean a] => pure [.boolean (!a)]
    | "bool.or", [.boolean a, .boolean b] => pure [.boolean (a || b)]
    | "control.require", [.boolean value] => do
        if !value then fail "reject" "require-false"
        pure []
    | "poly.product_sum", [.table a, .table b] => pure [.field (← checked (Math.productSum a b))]
    | "poly.product_round", [.table a, .table b] => pure [.round (← checked (Math.productRound a b))]
    | "poly.fold", [.table t, .field r] => pure [.table (← checked (t.fold r))]
    | "poly.evaluate", [.table t, .point p] => pure [.field (← checked (t.evaluate p))]
    | "poly.empty_point", [] => pure [.point []]
    | "poly.append_point", [.point p, .field r] => do
        require (p.length < limits.rank) "point-limit"
        pure [.point (p ++ [r])]
    | "vector.from_point", [.point p] => pure [Value.fromArithmetic .bls (.vector p)]
    | "vector.from_table", [.table t] => pure [Value.fromArithmetic .bls (.vector t.cells)]
    | "vector.to_point", [v] => do
        let .vector xs ← checked (v.toArithmetic .bls) | fail "refused" "kernel-input-types"
        require (xs.length ≤ limits.rank) "point-limit"
        pure [.point xs]
    | "vector.to_table", [v] => do
        let .vector xs ← checked (v.toArithmetic .bls) | fail "refused" "kernel-input-types"
        pure [.table (← checked (Math.Table.admit xs.length.log2 xs))]
    | "poly.equality_weights", [.point p] => do
        require (p.length ≤ limits.rank) "point-limit"
        pure [Value.fromArithmetic .bls (.vector (Zkc.Algebra.FiniteVectors.equalityWeights p))]
    | "random.draw", [.extensionRng n] => do
        let value ← challenge source descriptor location n
        pure [value, .extensionRng (n+1)]
    | "random.index", [.extensionRng n, bound] => do
        let .index bound ← checked (bound.toArithmetic .bls) | fail "refused" "kernel-input-types"
        let value ← challenge source descriptor location n (some bound)
        pure [value, .extensionRng (n+1)]
    | "random.draw", [.ristrettoRng n] => do
        let value ← challenge source descriptor location n
        pure [value, .ristrettoRng (n + 1)]
    | "random.draw", [.selectedRng n] => do
        let value ← challenge source descriptor location n
        pure [value, .selectedRng (n+1)]
    | "pcs.equal", [a,b] => do
        pure [.boolean ((← checked a.wire) == (← checked b.wire))]
    | "pairing.check", _ | "pcs.check", _ | "curve.neg", _ | "curve.nonidentity", _ | "curve.msm", _ |
      "curve.scale_each", _ | "curve.vector_add", _ | "curve.vector_scale", _ | "curve.split", _ | "curve.concat", _ | "curve.generator", _ | "curve.add", _ | "curve.scale", _ |
      "curve.equal", _ | "curve.empty", _ | "curve.append", _ | "curve.at", _ => do
        let expected ← checked (groupShapes name inputs attrs)
        let outputs ← primitive source name selected.arguments attrs inputs
        let values ← checked (outputs.mapM (fun v => decodeReplyValue v))
        if let some counts := expected then
          require (values.length == counts.length) "kernel-result-types"
          for (value, count) in values.zip counts do
            require ((← checked (groupCount value)) == count) "group-count"
        pure values
    | _, _ => fail "refused" "unimplemented-validator-kernel"
  require ((← checked (outputs.mapM (Value.typeFor))) == signature.outputs) "kernel-result-types"
  event (.arr #[.str "response", request, .arr (← checked (outputs.mapM (fun v => observedValue v))).toArray])
  return outputs

end Tools.Artifact
