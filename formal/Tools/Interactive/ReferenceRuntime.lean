import Tools.Interactive.ReferenceAdmission
import Tools.Interactive.ExternalReference
import Zkc.Source.FiniteControl
import Tools.Interactive.ReferenceTranscript
import Tools.Interactive.ReferenceGroups
import Tools.Interactive.ReferenceCommitment
import Tools.Interactive.ReferenceOracle
import Tools.Interactive.TypedLocal
import Tools.Interactive.MatrixIdentity

/-! Execute independently typed source locals under mathematical and explicit
stateful services. Physical allocation and frame views have separate scope. -/

set_option autoImplicit false

namespace Tools.Interactive.Reference
open Lean (Json)
open Zkc.Source

/-- Contract computation and authoritative state transitions, without observation
wrapping. Physical interpretations may check output retention before publishing
a successful response; consuming failures still retain the reached state. -/
def compute (location : Location) (request : TypedLocal.Request)
    (inputs : List Value) : RunM (List Value) := do
  require location (inputs.map Value.ty == request.signature.inputs) "runtime-kernel-types"
  if request.contract.startsWith "transcript." then
    require location (Bindings.validTranscriptAttributes request.attributes) "kernel-attributes"
  let outputs ← if Bindings.resourceUnitContract request.contract then do
      require location request.attributes.isEmpty "kernel-attributes"
      -- Resolution admits a unit contract only with one valid domain argument,
      -- and the type check above fixes each operand's domain and arity, so the
      -- fallbacks name the checks that already refused those shapes.
      let [domain] := request.arguments | failAt location "refused" "binding-resource-unit-domain"
      match request.contract, inputs with
      | "resource_unit.create", [] => do pure [← createResourceUnit location domain]
      | "resource_unit.pass", [.resourceUnit actual identity generation] => do
          let _ ← consumeResource location "resource_unit" identity generation domain false
          pure [.resourceUnit actual identity (generation + 1)]
      | "resource_unit.consume", [.resourceUnit _ identity generation] => do
          let _ ← consumeResource location "resource_unit" identity generation domain false
          modify fun state => { state with resources := state.resources.filter (·.identity != identity) }
          pure []
      | _, _ => failAt location "refused" "runtime-kernel-types"
    else if request.contract.startsWith "external." then do
      require location (request.arguments.isEmpty && request.attributes.isEmpty) "external-attributes"
      External.compute location request.contract inputs
    else if request.contract == "matrix.identity_check" then do
      let [value] := inputs | failAt location "refused" "runtime-kernel-types"
      let hashRequest ← checked location (match value with
        | .arithmetic domain data => MatrixIdentity.prime domain data
        | .extension data => MatrixIdentity.extension data
        | _ => .error "matrix-identity-type")
      let response ← successfulReply location (← oracle location hashRequest)
      pure [.boolean (← checked location (MatrixIdentity.acceptsDigest request.attributes response))]
    else if Bindings.oracleContract request.contract then
      checked location (oracleCompute request.contract (request.arguments.headD "") inputs)
    else if request.contract == "vector.embed" then do
      let [input] := inputs | failAt location "refused" "runtime-kernel-types"
      let .vector xs ← checked location (input.toArithmetic .koalaBear) | failAt location "refused" "runtime-kernel-types"
      require location (request.arguments == [Bindings.koalaBearExt8] && request.attributes.isEmpty) "binding-static-arguments"
      pure [Value.fromExtension (.vector (xs.map ExtensionReference.embed))]
    else if request.contract == "field.embed" then do
      let [input] := inputs | failAt location "refused" "runtime-kernel-types"
      let .field x ← checked location (input.toArithmetic .koalaBear) | failAt location "refused" "runtime-kernel-types"
      require location (request.arguments == [Bindings.koalaBearExt8] && request.attributes.isEmpty) "binding-static-arguments"
      pure [Value.fromExtension (.field (ExtensionReference.embed x))]
    else if request.arguments.head? == some Bindings.koalaBearExt8 && !request.contract.startsWith "random." then do
      let values ← checked location (inputs.mapM Value.toExtension)
      let outputs ← checked location (ExtensionReference.compute request.contract request.attributes values)
      pure (outputs.map Value.fromExtension)
    else if ScalarReference.supported request.contract then do
      let domain ← checked location (ScalarReference.Domain.parse (request.arguments.headD Bindings.fr))
      let values ← checked location (inputs.mapM (Value.toArithmetic domain))
      let outputs ← checked location (ScalarReference.compute domain request.contract request.attributes values)
      pure (outputs.map (Value.fromArithmetic domain))
    else match request.contract, inputs with
    | "pairing.check", [xs, ys] => do
        require location ((← checked location (groupCount xs)) ==
          (← checked location (groupCount ys))) "pairing-length"
        external location request.contract request.arguments request.attributes inputs
    | "pcs.commit", [.proverKey key, .table table] => commit location key table
    | "pcs.open", [.opening state, .point point] => openCommitment location state point
    | "pcs.check", [.verifierKey key, .commitment commitment, .point point, .field value, .proof proof] =>
        checkCommitment location key commitment point value proof
    | "pcs.equal", [.commitment a, .commitment b] => pure [.boolean (a == b)]
    | "bool.and", [.boolean a, .boolean b] => pure [.boolean (a && b)]
    | "bool.not", [.boolean a] => pure [.boolean (!a)]
    | "bool.or", [.boolean a, .boolean b] => pure [.boolean (a || b)]
    | "control.require", [.boolean allowed] => do
        if !allowed then failAt location "reject" "require"
        pure []
    | "poly.product_sum", [.table a, .table b] => do
        require location (a.rank == b.rank) "arity-mismatch"
        pure [.field (← checked location (Math.productSum a b))]
    | "poly.product_round", [.table a, .table b] => do
        -- The /2 contract checks equal arities before positive arity. Keep the
        -- shared mathematical helpers' older /1 diagnostics unchanged.
        require location (a.rank == b.rank) "arity-mismatch"
        require location (a.rank > 0) "positive-arity-required"
        pure [.round (← checked location (Math.productRound a b))]
    | "poly.fold", [.table t, .field r] => do
        require location (t.rank > 0) "positive-arity-required"
        pure [.table (← checked location (t.fold r))]
    | "poly.evaluate", [.table t, .point p] => do
        require location (t.rank == p.length) "arity-mismatch"
        pure [.field (← checked location (t.evaluate p))]
    | "poly.empty_point", [] => pure [.point []]
    | "poly.append_point", [.point p, .field r] => do
        require location (p.length < limits.rank) "point-limit"
        pure [.point (p ++ [r])]
    | "vector.from_point", [.point p] => pure [Value.fromArithmetic .bls (.vector p)]
    | "vector.from_table", [.table t] => pure [Value.fromArithmetic .bls (.vector t.cells)]
    | "vector.to_point", [v] => do
        let .vector xs ← checked location (v.toArithmetic .bls) | failAt location "refused" "runtime-kernel-types"
        require location (xs.length ≤ limits.rank) "point-limit"
        pure [.point xs]
    | "vector.to_table", [v] => do
        let .vector xs ← checked location (v.toArithmetic .bls) | failAt location "refused" "runtime-kernel-types"
        let rank := xs.length.log2
        pure [.table (← checked location (Math.Table.admit rank xs))]
    | "poly.equality_weights", [.point p] => do
        require location (p.length ≤ limits.rank) "point-limit"
        pure [Value.fromArithmetic .bls (.vector (Zkc.Algebra.FiniteVectors.equalityWeights p))]
    | "random.draw", [.erng identity generation] => extensionDraw location identity generation none
    | "random.index", [.erng identity generation, bound] => do
        let .index n ← checked location (bound.toArithmetic .bls) | failAt location "refused" "runtime-kernel-types"
        extensionDraw location identity generation (some n)
    | "random.vector", [.erng identity generation] => do
        let [length] := request.attributes | failAt location "refused" "kernel-attributes"
        extensionVector location identity generation (← checked location (Decode.natural (.str length)))
    | "random.draw", [.brng identity generation] => randomDraw location identity generation .bn254
    | "random.draw", [.rrng identity generation] => randomDraw location identity generation .ristretto
    | "random.vector", [value] => do
        let some ("rng", identity, generation) := value.capability
          | failAt location "refused" "capability-kind"
        let domain ← checked location (RandomDomain.parse value.ty.identity)
        let [length] := request.attributes | failAt location "refused" "kernel-attributes"
        randomVector location domain identity generation (← checked location (Decode.natural (.str length)))
    | "curve.commit", [.rgroups bases, .rnonce identity generation] =>
        nonceCommitFor location .ristretto (.rgroups bases) identity generation
    | "curve.response", [secret, challenge, .rnonce identity generation] => do
        let .field secret ← checked location (secret.toArithmetic .ristretto) | failAt location "refused" "runtime-kernel-types"
        let .field challenge ← checked location (challenge.toArithmetic .ristretto) | failAt location "refused" "runtime-kernel-types"
        nonceResponseFor location .ristretto secret challenge identity generation
    | "random.draw", [.rng identity generation] => randomDraw location identity generation
    | "curve.commit", [.groups bases, .nonce identity generation] =>
        nonceCommit location bases identity generation
    | "curve.response", [.field secret, .field challenge, .nonce identity generation] =>
        nonceResponse location secret challenge identity generation
    | "transcript.draw_index", [.transcript suite identity generation, bound] => do
        let .index n ← checked location (bound.toArithmetic .bls) | failAt location "refused" "runtime-kernel-types"
        transcriptChallenge location request.attributes identity generation suite (some n)
    | "transcript.challenge", [.transcript suite identity generation] =>
        transcriptChallenge location request.attributes identity generation suite
    | name, [.transcript suite identity generation, value] =>
        if name.startsWith "transcript.observe." then
          transcriptObserve location request.attributes identity generation value suite
        else failAt location "refused" "reference-kernel-not-supported"
    | name, _ =>
        if name.startsWith "curve." then
          groupCompute location name (request.arguments.headD Bindings.fr) request.attributes inputs
        else failAt location "refused" "reference-kernel-not-supported"
  require location (outputs.map Value.ty == request.signature.outputs) "runtime-kernel-results"
  return outputs

/-- Shared observation and work charging for logical and physical interpreters.
The physical interpreter may fail between the request and response. -/
def observeRequest (location : Location) (semantic : Json) (inputs : List Value) : RunM Unit :=
  event location (.arr #[.str "request", semantic]) (1 + (inputs.map Value.size).sum)

def observeResponse (location : Location) (semantic : Json) (outputs : List Value) : RunM Unit :=
  event location (.arr #[.str "response", semantic, valuesJson outputs]) (1 + (outputs.map Value.size).sum)

def evaluate (location : Location) (request : TypedLocal.Request)
    (inputs : List Value) : RunM (List Value) := do
  require location (inputs.map Value.ty == request.signature.inputs) "runtime-kernel-types"
  let semantic := requestJson location request.contract request.arguments request.attributes inputs
  observeRequest location semantic inputs
  let outputs ← compute location request inputs
  observeResponse location semantic outputs
  return outputs

private abbrev Operation := (request : TypedLocal.Request) × Values TypedValue request.signature.inputs
private abbrev interface : PIR.Signature where
  Op := Operation
  Reply op := Values TypedValue op.1.signature.outputs

private def meaning : ResultBundle.Meaning TypedLocal.signature interface where
  Value := TypedValue
  condition value := match value.val with
    | .boolean b => b
    | _ => false
  operation request arguments := .call ⟨request, arguments⟩ .done

private def stopReason : String → PIR.Stop
  | "reject" => .reject
  | "abort" => .abort
  | "exhausted" => .exhausted
  | "incomplete" | "pending-primitive" | "pending" => .incomplete
  | _ => .refused

private def handler (location : Location) : PIR.Handler interface State Empty := fun op state =>
  let location := { location with scope := { location.scope with site := op.1.site } }
  let action : RunM _ := do
    let values ← evaluate location op.1 (untypedValues op.2)
    checked location (typedValues op.1.signature.outputs values)
  let (result, state) := action.run state
  match result with
  | .ok values => ⟨.returned values, state, []⟩
  | .error fault => ⟨.stopped (stopReason fault.reason), { state with fault := some fault }, []⟩

private def localIndex (location : Location) (value : Value) : RunM Nat := do
  let .index n ← checked location (value.toArithmetic .bls) | failAt location "refused" "local-bound-type"
  if n > limits.iterations then failAt location "exhausted" "local-bound-limit"
  return n

private def unitIdentities (values : List Value) : List Name :=
  (values.flatMap Value.leaves).filterMap fun value => match value with
    | .resourceUnit _ identity _ => some identity
    | _ => none

/-- Close a local frame without rolling back consumed resources. Only active
returned leaves retain resource-unit authority; unrelated outer units survive. -/
def closeLocalFrame (before after : State) (inputs : List Value)
    (result : Except Fault (List Value)) : State :=
  let retained := match result with | .ok values => unitIdentities values | .error _ => []
  let incoming := unitIdentities inputs
  let previous := before.resources.map (·.identity)
  { after with resources := after.resources.filter fun resource =>
    resource.payload.kind != "resource_unit" || retained.contains resource.identity ||
      (previous.contains resource.identity && !incoming.contains resource.identity) }

/-- Finalize only this participant; later failures cannot revoke its return. -/
def closeParticipantFrame (state : State) (role : Name)
    (result : Except Fault (List Value)) : State :=
  let retained := match result with | .ok values => unitIdentities values | .error _ => []
  { state with resources := state.resources.filter fun resource =>
    resource.owner != role || resource.payload.kind != "resource_unit" ||
      retained.contains resource.identity }

/-- Finalize the selected open role. Joint execution instead closes each root
with `closeParticipantFrame` and cancels only participants still running. -/
def closeRootFrame (state : State) (result : Except Fault (List Value)) : State :=
  let retained := match result with | .ok values => unitIdentities values | .error _ => []
  { state with resources := state.resources.filter fun resource =>
    resource.payload.kind != "resource_unit" || retained.contains resource.identity }

def withLocalFrame (location : Location) (inputs : List Value)
    (action : RunM (List Value)) : RunM (List Value) := do
  recordBoundary location inputs
  activateRole location.scope.role
  let before ← get
  let (result, after) := action.run before
  set (closeLocalFrame before after inputs result)
  match result with
  | .ok values =>
      recordBoundary location values
      activateRole location.scope.role
      return values
  | .error fault => throw fault

/-- The selected arm extends the local origin and the interaction path together,
exactly as a branch or an iteration does, so a local observation and its domain
separation name the arm they happened in:
docs/spec/profiles/compiler/local-variants.md. -/
def enterMatch (location : Location) (site alternative : Name) : Location :=
  { location with
    scope := { location.scope with path := location.scope.path ++ [.localMatch site alternative] },
    interactionPath := location.interactionPath.push
      (.arr #[.str "match", .str site, .str alternative]) }

private def structuredBody (bindings : List OperationBinding) : Nat → Location → List (Name × Value) →
    List Instruction → RunM (List Value)
  | 0, location, _, _ => failAt location "exhausted" "local-stack-limit"
  | depth + 1, location, initial, code => do
      let mut env := initial
      for instruction in code do
        match instruction with
        | .op site name attrs inputs outputs =>
          let current := { location with scope := { location.scope with site } }
          let request ← checked current (TypedLocal.resolveRequest bindings site name attrs)
          let values ← evaluate current request (← checked current (Control.readValues env inputs))
          env ← checked current (Control.bindValues env outputs values)
        | .variant site ty alternative payload output =>
          let current := { location with scope := { location.scope with site } }
          charge current
          let values ← checked current (Control.readValues env payload)
          let value ← checked current (Value.pack ty alternative values)
          env ← checked current (Control.bindValues env [output] [value])
        | .localMatch site input captures arms outputs =>
          let current := { location with scope := { location.scope with site } }
          charge current
          let value ← checked current (lookup input env)
          checked current value.validate
          let .variant _ alternative payload := value | failAt current "refused" "variant-type"
          let (names, nested) ← checked current (lookup alternative arms)
          let captured ← checked current (Control.readValues env captures)
          -- The tag is local origin metadata, never a protocol scheduling event.
          let nestedLocation := enterMatch current site alternative
          let values ← withLocalFrame nestedLocation (payload ++ captured)
            (structuredBody bindings depth nestedLocation (names.zip payload ++ captures.zip captured) nested)
          env ← checked current (Control.bindValues env outputs values)
        | .stop site _ reason =>
          let current := { location with scope := { location.scope with site } }
          charge current
          failAt current reason "explicit-stop"
        | .conditional site condition captures yes no outputs =>
          let current := { location with scope := { location.scope with site } }
          charge current
          let .boolean selected ← checked current (lookup condition env) | failAt current "refused" "local-condition-type"
          let inputs ← checked current (Control.readValues env captures)
          let nested := { current with
            scope := { current.scope with path := current.scope.path ++ [.localBranch site selected] }
            interactionPath := current.interactionPath.push (.arr #[.str "if", .str site, .str (if selected then "then" else "else")]) }
          let values ← Zkc.Source.FiniteControl.branchM (fun _ => failAt nested "refused" "local-control-stop") selected
            (fun _ => structuredBody bindings depth nested (captures.zip inputs) yes)
            (fun _ => structuredBody bindings depth nested (captures.zip inputs) no)
          env ← checked current (Control.bindValues env outputs values)
        | .forLoop site induction lower upper carried captures nested outputs =>
          let current := { location with scope := { location.scope with site } }
          charge current
          let lower ← localIndex current (← checked current (lookup lower env))
          let upper ← localIndex current (← checked current (lookup upper env))
          let some bounds := Zkc.Source.FiniteControl.Bounds.admit lower upper limits.iterations
            | failAt current "exhausted" "local-bound-limit"
          let initial ← checked current (Control.readValues env (carried.map Prod.snd))
          let captured ← checked current (Control.readValues env captures)
          let (_, values) ← Zkc.Source.FiniteControl.iterateM (fun _ => failAt current "refused" "local-control-stop")
            bounds.count (bounds.lower, initial) fun (index, values) => do
              let current := { current with
                scope := { current.scope with path := current.scope.path ++ [.localIteration site index] }
                interactionPath := current.interactionPath.push (.arr #[.str "for", .str site, .str (toString index)]) }
              if (← get).iterations ≥ 100000 then failAt current "exhausted" "local-iteration-limit"
              modify fun state => { state with iterations := state.iterations + 1 }
              let inputs := [(induction, Value.fromArithmetic .bls (.index index))] ++
                (carried.map Prod.fst).zip values ++ captures.zip captured
              let values ← structuredBody bindings depth current inputs nested
              return (index + 1, values)
          env ← checked current (Control.bindValues env outputs values)
        | .yield values | .ret values =>
          charge location
          return ← checked location (Control.readValues env values)
        | _ => failAt location "refused" "local-control-instruction"
      failAt location "refused" "local-control-terminal"

/-- Execute the retained typed source region. Instrumentation is in `State`, so
the core handler's event type is empty; stopped state still retains every log
entry and detailed fault. No candidate operation list is executed here. -/
private def executeFunctionBody (location : Location) (function : TypedLocal.Function)
    (inputs : List Value) : RunM (List Value) := do
  let location := { location with definition := function.origin }
  let some code := function.code | do
    let _ ← checked location (typedValues (function.arguments.map Prod.snd) inputs)
    let values ← structuredBody function.bindings (limits.callDepth - location.scope.path.length) location
      ((function.arguments.map Prod.fst).zip inputs) function.structured
    let _ ← checked location (typedValues function.results values)
    return values
  let inputs ← checked location (typedValues (function.arguments.map Prod.snd) inputs)
  let program := code.denote meaning.interpretation (ResultBundle.singletons inputs).get
  let result := program.run (handler location) (← get)
  set result.state
  match result.outcome with
  | .returned values => return untypedValues values
  | .stopped _ =>
      match result.state.fault with
      | some fault => throw fault
      | none => failAt location "refused" "unlocated-region-stop"

/-- Local cleanup is shared with isolated active-payload regions. -/
def executeFunction (location : Location) (function : TypedLocal.Function)
    (inputs : List Value) : RunM (List Value) :=
  withLocalFrame location inputs (executeFunctionBody location function inputs)

end Tools.Interactive.Reference
