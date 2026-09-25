import Tools.Interactive.GenericReference
import Tools.Interactive.GenericValidation

/-! A bounded physical interpretation of a source-checked local plan.

Scope: one root participant, one local call, returned results; nested local
branches/finite loops, supported numerical and group-sequence operations.
Input table storage capacity is explicit. Fresh table
allocations are assumed successful with exact capacity, checked by native tests.
This is executable correspondence evidence, not a native adequacy theorem.
-/

set_option autoImplicit false

namespace Tools.Interactive.PhysicalLocal
open Lean (Json)
open Reference

structure Stored where
  value : Value
  representation : String
  capacity : Nat := 0
  leafCapacities : List Nat := []

private def arithmeticBytes {F : Type} (width : Nat) : ScalarReference.Data F → Nat
  | .index _ => 512
  | .indices xs => 256 + 8 * xs.length
  | .vector xs | .polynomial xs => 256 + width * xs.length
  | .matrix m => 256 + (8 + width) * m.entries.length
  | _ => 512

private def valueBytes (value : Value) (capacity : Nat) : Nat :=
  match value with
  | .table _ => 256 + 32 * capacity
  | .point values => 256 + 32 * values.length
  | .arithmetic domain value => arithmeticBytes (if domain == .koalaBear then 4 else 32) value
  | .extension value => arithmeticBytes 32 value
  | .groups wire => 256 + 128 * Tools.Artifact.valueLE (wire.extract 6 10)
  | .rgroups wire => 256 + 160 * Tools.Artifact.valueLE (wire.extract 6 10)
  | .bnGroup g2 true wire => 256 + (if g2 then 128 else 64) * Tools.Artifact.valueLE (wire.extract 6 10)
  | _ => 512

/-- The native local-variant profile uses a stable conservative charge instead
of allocator-specific capacities. Every nested descriptor is counted in full. -/
private def descriptorBytes : Nat → Variant.Descriptor → Nat
  | 0, _ => 0
  | fuel + 1, descriptor =>
      512 + 4 * descriptor.spelling.utf8ByteSize +
      256 * descriptor.alternatives.length +
      (descriptor.alternatives.map fun (_, payload) =>
        256 * payload.length + (payload.map fun spelling =>
          match Variant.parse spelling with
          | .ok nested => descriptorBytes fuel nested
          | .error _ => 0).sum).sum

/-- Active table capacities survive packing and selection; no inactive storage
is charged or invented. Descriptor and tag bytes remain private local storage. -/
private def variantBytes : Value → Nat
  | .variant descriptor _ payload =>
      256 + descriptorBytes 8 descriptor + 512 * payload.length + (payload.map variantBytes).sum
  | _ => 0

def Stored.bytes (stored : Stored) : Nat :=
  match stored.value with
  | .variant .. => variantBytes stored.value +
      (stored.value.leaves.zipIdx.map fun (value, i) => valueBytes value
        (stored.leafCapacities[i]?.getD (match value with | .table t => t.cells.length | _ => 0))).sum
  | value => valueBytes value stored.capacity

private def Stored.capacities (stored : Stored) : List Nat :=
  match stored.value with
  | .variant .. => stored.leafCapacities
  | _ => [stored.capacity]

private def fresh (value : Value) (ty : Bindings.ValueType) : Stored :=
  ⟨value, ty.representation, match value with | .table t => t.cells.length | _ => 0, []⟩

structure Accounting where
  instructions : Nat := 0
  liveValues : Nat := 0
  liveBytes : Nat := 0
  totalBytes : Nat := 0
  views : Nat := 0
  deriving BEq, Repr

def Accounting.json (a : Accounting) : Json :=
  .arr ([a.instructions, a.liveValues, a.liveBytes, a.totalBytes, a.views].map
    (fun n => Json.str (toString n))).toArray

private structure State where
  logical : Reference.State
  accounting : Accounting := {}
  steps : Array Json := #[]
  rootValues : List Stored := []
  localValues : List Stored := []
  iterations : Nat := 0

private abbrev Run := ExceptT Fault (StateM State)
private def liveLimit := 64 * 1024 * 1024
private def totalLimit := 256 * 1024 * 1024

private def fail {α : Type} (location : Location) (reason detail : String) : Run α :=
  throw ⟨reason, detail, location⟩

private def liftResult {α : Type} (location : Location) : Result α → Run α
  | .ok value => pure value
  | .error detail => fail location "refused" detail

private def logical {α : Type} (action : RunM α) : Run α := do
  let (result, next) := action.run (← get).logical
  modify fun state => { state with logical := next }
  match result with
  | .ok value => return value
  | .error fault => throw fault

private def tick (location : Location) : Run Unit := do
  if (← get).accounting.instructions ≥ 1000000 then fail location "limit" "instructions"
  modify fun s => { s with accounting.instructions := s.accounting.instructions + 1 }

private def canRetain (location : Location) (values : List Stored) : Run Nat := do
  let bytes := (values.map Stored.bytes).sum
  let a := (← get).accounting
  if a.liveValues + values.length > 16384 || a.liveBytes + bytes > liveLimit ||
      a.totalBytes + bytes > totalLimit then fail location "limit" "retained-values"
  return bytes

private def retain (location : Location) (values : List Stored) : Run Unit := do
  let bytes ← canRetain location values
  let a := (← get).accounting
  modify fun s => { s with accounting := { a with
    liveValues := a.liveValues + values.length
    liveBytes := a.liveBytes + bytes
    totalBytes := a.totalBytes + bytes } }

private def release (values : List Stored) : Run Unit :=
  modify fun s => { s with accounting := { s.accounting with
    liveValues := s.accounting.liveValues - values.length,
    liveBytes := s.accounting.liveBytes - (values.map Stored.bytes).sum } }

private def output (location : Location) (ceiling available bytes : Nat) : Run Unit :=
  if bytes > ceiling || bytes > available then fail location "exhausted" "output-bytes"
  else pure ()

def supported (binding : OperationBinding) : Bool :=
  (Bindings.resourceUnitContract binding.contract || ScalarReference.supported binding.contract ||
    ["field.constant", "field.add", "field.mul", "field.equal", "poly.product_sum", "poly.product_round",
      "poly.boundary", "poly.round_evaluate", "poly.fold", "poly.evaluate", "poly.empty_point",
      "poly.append_point", "table.relayout", "random.draw", "random.vector", "bool.and", "bool.not", "bool.or",
      "curve.empty", "curve.append", "curve.at", "curve.get", "curve.length", "control.require"].contains binding.contract) &&
    !binding.implementation.startsWith "arkworks-diagonal/" &&
    !binding.implementation.startsWith "dalek-diagonal/" && (Bindings.resolve true binding).isOk

private def preflight (location : Location) (ceiling available : Nat) (contract : String)
    (inputs : List Stored) : Run Unit := do
  match contract, inputs.map Stored.value with
  | "table.relayout", [.table t] => output location ceiling available (256 + 32 * t.cells.length)
  | "poly.fold", [.table t, _] => output location ceiling available (256 + 32 * (t.cells.length / 2))
  | "poly.append_point", [.point p, _] =>
      if p.length ≥ limits.rank then fail location "exhausted" "arity-limit"
      output location ceiling available (256 + 32 * (p.length + 1))
  | _, _ => pure ()

private def operation (location : Location) (ceiling : Nat) (bindings : List OperationBinding)
    (binding : OperationBinding) (attrs : List String) (inputs : List Stored) : Run (List Stored) := do
  let signature ← liftResult location (Bindings.resolve true binding)
  for (input, ty) in inputs.zip signature.inputs do
    if input.value.ty != { ty with representation := "" } || input.representation != ty.representation then
      fail location "refused" "physical-input-type"
    output location ceiling liveLimit input.bytes
  if inputs.length != signature.inputs.length then fail location "refused" "physical-input-arity"
  let a := (← get).accounting
  let available := min (liveLimit - a.liveBytes) (totalLimit - a.totalBytes)
  let record := .arr #[.str location.scope.site, .str binding.contract, .str (toString available)]
  modify fun s => { s with steps := s.steps.push (.arr #[.str "attempt", record, .str (toString a.views)]) }
  let semantic := requestJson location binding.contract binding.arguments attrs (inputs.map Stored.value)
  if binding.contract != "table.relayout" then
    logical (observeRequest location semantic (inputs.map Stored.value))
  preflight location ceiling available binding.contract inputs
  let values ← if binding.contract == "table.relayout" then do
      let [input] := inputs | fail location "refused" "physical-conversion-arity"
      pure [input.value]
    else do
      let request ← liftResult location (TypedLocal.resolveRequest bindings location.scope.site binding.name attrs)
      logical (Reference.compute location request (inputs.map Stored.value))
  let outputs := (values.zip signature.outputs).map fun (value, ty) => fresh value ty
  if values.length != signature.outputs.length then fail location "refused" "physical-output-arity"
  output location ceiling available (outputs.map Stored.bytes |>.sum)
  if binding.contract != "table.relayout" then
    logical (observeResponse location semantic values)
  -- Backend completion precedes the runner's retention, which can still fail.
  let completed := .arr #[.str "completed", record, .str (toString (← get).accounting.views)]
  modify fun s => { s with steps := s.steps.push completed }
  retain location outputs
  modify fun s => { s with localValues := s.localValues ++ outputs }
  return outputs

private def index (location : Location) (value : Stored) : Run Nat := do
  let .index n ← liftResult location (value.value.toArithmetic .bls) | fail location "refused" "local-bound-type"
  if n > limits.iterations then fail location "exhausted" "local-bound-limit"
  return n

private def region (location : Location) (inputs : List Stored)
    (action : Run (List Stored)) : Run (List Stored) := do
  if (← get).accounting.views ≥ limits.callDepth then fail location "limit" "stack-depth"
  logical (recordBoundary location (inputs.map Stored.value) *> activateRole location.scope.role)
  let before := (← get).logical
  let outer := (← get).localValues
  retain location inputs
  modify fun s => { s with localValues := inputs, accounting.views := s.accounting.views + 1 }
  let result : Except Fault (List Stored) ← try pure (.ok (← action)) catch fault => pure (.error fault)
  modify fun s => { s with logical := (closeLocalFrame before s.logical (inputs.map Stored.value)
      (result.map (List.map Stored.value))) }
  release (← get).localValues
  modify fun s => { s with localValues := outer, accounting.views := s.accounting.views - 1 }
  match result with
  | .ok values =>
      logical (recordBoundary location (values.map Stored.value) *> activateRole location.scope.role)
      return values
  | .error fault => throw fault

private def bindResults (location : Location) (outputs : List Stored) : Run Unit := do
  retain location outputs
  modify fun s => { s with localValues := s.localValues ++ outputs }

private def bodyCode (ceiling : Nat) (bindings : List OperationBinding) :
    Nat → Location → List (Name × Stored) → List Instruction → Run (List Stored)
  | 0, location, _, _ => fail location "limit" "stack-depth"
  | depth + 1, location, initial, instructions => do
      let mut env := initial
      for instruction in instructions do
        if let .release names := instruction then
          env := env.filter fun pair => !(names.contains pair.1)
          continue
        tick location
        match instruction with
        | .op site name attrs arguments results =>
            let current := { location with scope := { location.scope with site } }
            let binding ← liftResult current (lookup name (bindings.map fun b => (b.name, b)))
            let inputs ← liftResult current (arguments.mapM fun n => lookup n env)
            let values ← operation current ceiling bindings binding attrs inputs
            env := env ++ results.zip values
        | .variant site ty alternative payload output =>
            let current := { location with scope := { location.scope with site } }
            let parsed ← liftResult current (Bindings.valueType true ty)
            let inputs ← liftResult current (payload.mapM fun n => lookup n env)
            let value ← liftResult current (Value.pack {parsed with representation := ""}.spelling alternative (inputs.map Stored.value))
            let stored : Stored := ⟨value, parsed.representation, 0, inputs.flatMap Stored.capacities⟩
            bindResults current [stored]
            env := env ++ [(output, stored)]
        | .localMatch site input captures arms outputs =>
            let current := { location with scope := { location.scope with site } }
            let stored ← liftResult current (lookup input env)
            liftResult current stored.value.validate
            let .variant _ alternative payload := stored.value | fail current "refused" "variant-type"
            let (names, nested) ← liftResult current (lookup alternative arms)
            let captured ← liftResult current (captures.mapM fun n => lookup n env)
            let mut capacities := stored.leafCapacities
            let mut inputs := []
            for value in payload do
              let count := value.leaves.length
              let currentCaps := capacities.take count
              capacities := capacities.drop count
              let input : Stored := ⟨value, Bindings.defaultRepresentation value.ty.kind value.ty.identity,
                currentCaps.headD 0, currentCaps⟩
              inputs := inputs ++ [input]
            let nestedLocation := { current with scope := { current.scope with
              path := current.scope.path ++ [.localMatch site alternative] } }
            let values ← region nestedLocation (inputs ++ captured)
              (bodyCode ceiling bindings depth nestedLocation (names.zip inputs ++ captures.zip captured) nested)
            bindResults current values
            env := env ++ outputs.zip values
        | .stop site _ reason =>
            fail { location with scope := { location.scope with site } } reason "explicit-stop"
        | .conditional site condition captures yes no outputs =>
            let current := { location with scope := { location.scope with site } }
            let condition ← liftResult current (lookup condition env)
            let .boolean selected := condition.value | fail current "refused" "local-condition-type"
            let inputs ← liftResult current (captures.mapM fun n => lookup n env)
            let nested := { current with scope := { current.scope with path := current.scope.path ++ [.localBranch site selected] } }
            let values ← region nested inputs (Zkc.Source.FiniteControl.branchM
              (fun _ => fail nested "refused" "local-control-stop") selected
              (fun _ => bodyCode ceiling bindings depth nested (captures.zip inputs) yes)
              (fun _ => bodyCode ceiling bindings depth nested (captures.zip inputs) no))
            bindResults current values
            env := env ++ outputs.zip values
        | .forLoop site induction lower upper carried captures nested outputs =>
            let current := { location with scope := { location.scope with site } }
            let lower ← index current (← liftResult current (lookup lower env))
            let upper ← index current (← liftResult current (lookup upper env))
            let some bounds := Zkc.Source.FiniteControl.Bounds.admit lower upper limits.iterations
              | fail current "exhausted" "local-bound-limit"
            let initial ← liftResult current ((carried.map Prod.snd).mapM fun n => lookup n env)
            let captured ← liftResult current (captures.mapM fun n => lookup n env)
            let (_, values) ← Zkc.Source.FiniteControl.iterateM (fun _ => fail current "refused" "local-control-stop")
              bounds.count (bounds.lower, initial) fun (i, values) => do
                let current := { current with scope := { current.scope with path := current.scope.path ++ [.localIteration site i] } }
                if (← get).iterations ≥ 100000 then fail current "limit" "iterations"
                modify fun s => { s with iterations := s.iterations + 1 }
                let value := Value.fromArithmetic .bls (.index i)
                let input := fresh value { value.ty with representation := Bindings.defaultRepresentation "index" "" }
                let inputs := [(induction, input)] ++ (carried.map Prod.fst).zip values ++ captures.zip captured
                let values ← region current (inputs.map Prod.snd) (bodyCode ceiling bindings depth current inputs nested)
                return (i + 1, values)
            bindResults current values
            env := env ++ outputs.zip values
        | .ret names | .yield names => return ← liftResult location (names.mapM fun n => lookup n env)
        | _ => fail location "refused" "physical-local-instruction"
      fail location "refused" "physical-local-terminal"

private def body (location : Location) (ceiling : Nat) (bindings : List OperationBinding)
    (function : Tools.Interactive.Function) (inputs : List Stored) : Run (List Stored) := do
  retain location inputs
  modify fun s => { s with localValues := inputs }
  bodyCode ceiling bindings limits.callDepth location ((function.arguments.map Prod.fst).zip inputs) (function.body.getD [])

private def executeBody (root location : Location) (ceiling : Nat) (bindings : List OperationBinding)
    (function : Tools.Interactive.Function) (inputs : List Stored) : Run (List Stored) := do
  -- Root ingress precedes view admission. Local entry duplicates retained args.
  for value in inputs do output root ceiling liveLimit value.bytes
  retain root inputs
  modify fun s => { s with rootValues := inputs, accounting.views := s.accounting.views + 1 }
  logical (recordBoundary root (inputs.map Stored.value) *> activateRole root.scope.role)
  tick location
  let _ ← canRetain location inputs
  modify fun s => { s with accounting.views := s.accounting.views + 1 }
  let before := (← get).logical
  let result : Except Fault (List Stored) ← try pure (.ok (← body location ceiling bindings function inputs))
    catch fault => pure (.error fault)
  modify fun s => { s with logical := (closeLocalFrame before s.logical (inputs.map Stored.value)
      (result.map (List.map Stored.value))) }
  release (← get).localValues
  modify fun s => { s with accounting.views := s.accounting.views - 1, localValues := [] }
  match result with
  | .error fault => throw fault
  | .ok values =>
      logical (recordBoundary location (values.map Stored.value) *> activateRole location.scope.role)
      retain location values
      modify fun s => { s with rootValues := s.rootValues ++ values }
      tick root
      release (← get).rootValues
      modify fun s => { s with rootValues := [] }
      retain root values
      modify fun s => { s with accounting.views := s.accounting.views - 1 }
      return values

private def execute (root location : Location) (ceiling : Nat) (bindings : List OperationBinding)
    (function : Tools.Interactive.Function) (inputs : List Stored) : Run (List Stored) := do
  try executeBody root location ceiling bindings function inputs
  catch fault =>
    -- The local bracket has already released its own retained values. Unwind
    -- the root's actual environment, including results bound before a halt.
    release (← get).rootValues
    modify fun s => { s with rootValues := [], accounting.views := s.accounting.views - 1 }
    throw fault

private def checkSupported (bindings : List OperationBinding) : Nat → List Instruction → Result Unit
  | 0, _ => .error "body-depth-limit"
  | depth + 1, instructions => do
      for instruction in instructions do
        match instruction with
        | .op _ name _ _ _ => ensure (supported (← lookup name (bindings.map fun b => (b.name, b)))) "physical-contract-not-supported"
        | .localMatch _ _ _ arms _ => for arm in arms do checkSupported bindings depth arm.2.2
        | .conditional _ _ _ yes no _ => checkSupported bindings depth yes; checkSupported bindings depth no
        | .forLoop _ _ _ _ _ _ body _ => checkSupported bindings depth body
        | _ => pure ()

/-- Formation and whole-source correspondence precede selection. The root
wrapper is one local call and return; local regions have actual child lifetimes. -/
def reference (source candidateJson inputJson storageJson : Json) : Result Json := do
  let correspondence ← Generic.validate source candidateJson
  let candidate ← Explicit.candidateLocals candidateJson
  ensure candidate.physical "physical-stage-required"
  let invocation ← Reference.invocation correspondence.prepared none inputJson
  ensure (invocation.state.answers.isEmpty && invocation.state.replies.isEmpty)
    "physical-external-inputs-not-supported"
  let [(_, role)] := invocation.binding.roles | throw "physical-single-role"
  let store := ((invocation.environments.find? (·.1 == role)).map Prod.snd).getD []
  let some [.localCall site owner configuration args outputs, .ret returns] := invocation.definition.body
    | throw "physical-single-local"
  ensure ((← invocation.binding.role owner) == role && args == invocation.context.map Port.name &&
    returns == outputs) "physical-local-wrapper"
  let occurrences := correspondence.calls.filter fun (binding, r, c) =>
    binding == invocation.binding.name && r == role && c.site == site && c.configuration == configuration
  let [(_, _, occurrence)] := occurrences | throw "physical-local-selection"
  let function ← lookup occurrence.function (candidate.functions.map fun f => (f.code.name, f))
  checkSupported candidate.bindings limits.depth (function.code.body.getD [])
  let [.str "zkc.local-resources/1", ceiling, capacities] ← Decode.array storageJson
    | throw "physical-storage-input"
  let ceiling ← Decode.natural ceiling
  ensure (ceiling ≤ liveLimit) "physical-output-ceiling"
  let capacities ← Decode.pairs Decode.name Decode.natural capacities
  let tables := store.filter fun (_, value) => value.ty.kind == "table"
  ensure (exactKeys capacities (tables.map fun (n, _) => (n, ()))) "physical-table-capacities"
  let values ← args.mapM fun name => do
    let value ← lookup name store
    let capacity ← match value with
      | .table t => do
          let capacity ← lookup name capacities
          ensure (capacity ≥ t.cells.length && capacity ≤ (liveLimit - 256) / 32) "physical-table-capacity"
          pure capacity
      | .field _ | .point _ | .round _ | .boolean _ | .rng .. => pure 0
      | _ => pure 0
    return Stored.mk value (Bindings.defaultRepresentation value.ty.kind value.ty.identity) capacity []
  let location := { invocation.location with
    definition := function.origin
    scope := { invocation.location.scope with
      role
      site
      path := [.localCall site configuration] } }
  let root := { invocation.location with scope := { invocation.location.scope with role } }
  let (outcome, state) := (execute root location ceiling candidate.bindings function.code values).run
    { logical := invocation.state }
  let outcome : Json := match outcome with
    | .ok values => .arr #[.str "returned", valuesJson (values.map Stored.value)]
    | .error fault => .arr #[.str fault.reason, .str fault.detail, fault.location.json]
  return .arr #[.str "zkc.physical-reference/1", outcome, .arr state.logical.events,
    state.logical.resourcesJson, state.accounting.json, .arr state.steps,
    .arr #[.str "source-checked-local-plan", .str "single-root-local-return",
      .str "exact-capacity-successful-allocation-premise", .str "conservative-payload-accounting",
      .str "no-native-adequacy-proof"]]

end Tools.Interactive.PhysicalLocal
