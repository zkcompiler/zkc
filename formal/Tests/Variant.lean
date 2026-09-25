import Tools.Interactive.ReferenceRuntime
import Tools.Interactive.ReferenceAdmission
import Tools.Interactive.LocalValidation
import Tools.Interactive.PhysicalLocal
import Tests.Checks

/-! Executable carrier, ownership and stop discriminators. These are finite
reference checks, not a theorem about the native parser or cryptography. -/
set_option autoImplicit false
namespace Tests.Variant
open Tools.Interactive Tools.Interactive.Reference
open Lean (Json)

private def choice : Variant.Descriptor := ⟨.str "pkg/type{T=index}", [("Some", ["index"]), ("None", [])]⟩
private def affineChoice : Variant.Descriptor :=
  ⟨.str "pkg/permission", [("Empty", []), ("Token", ["resource_unit:Slot.A"])]⟩
private def rngChoice : Variant.Descriptor :=
  ⟨.str "pkg/random", [("Empty", []), ("Coins", ["rng:" ++ Bindings.fr])]⟩
private def index (n : Nat) : Value := .fromArithmetic .bls (.index n)
private def bindings : List OperationBinding :=
  [⟨"add", "index.add", [], ""⟩, ⟨"guard", "control.require", [], ""⟩,
   ⟨"create", "resource_unit.create", ["Slot.A"], ""⟩,
   ⟨"draw", "random.draw", [Bindings.fr], ""⟩]
private def location : Location := Location.plain "test" "root" "invoke" "P"

private def function (arms : List (Name × List Name × List Instruction)) : Explicit.Function :=
  ⟨⟨"Select", [("v", choice.spelling), ("fallback", "index")], ["index"], some
    [.localMatch "select" "v" ["fallback"] arms ["out"], .ret ["out"]]⟩, none⟩
private def good : Explicit.Function := function
  [("Some", ["x"], [.op "sum" "add" [] ["x", "fallback"] ["sum"], .yield ["sum"]]),
   ("None", [], [.yield ["fallback"]])]
private def stopped : Explicit.Function := function
  [("Some", ["x"], [.stop "stop" "" "reject"]), ("None", [], [.yield ["fallback"]])]
private def admitted (f : Explicit.Function) : Result Unit :=
  admitFunctionWith (environmentSignature (.explicit bindings) "logical") f.code
private def execute (f : Explicit.Function) (inputs : List Value) (state : State := {}) :
    Result (Except Fault (List Value) × State) := do
  let typed ← TypedLocal.elaborate bindings f
  return (executeFunction location typed inputs).run state
private def returns (f : Explicit.Function) (inputs : List Value) (expected : List Value) : Bool :=
  match execute f inputs with
  | .ok (.ok values, _) => valuesJson values == valuesJson expected
  | _ => false

/-- An exception in the selected action preserves its state and bypasses any
continuation. This is the actual ExceptT/StateM order used by the interpreter. -/
theorem stop_bypasses_continuation (fault : Fault) (next : Unit → RunM (List Value)) (state : State) :
    (((throw fault : RunM Unit) >>= next).run state) = (.error fault, state) := rfl

private def errorCode (action : RunM Unit) : String :=
  match (action.run {}).1 with | .error fault => fault.detail | .ok _ => "success"

private def aliasUse : RunM Unit := do
  let token ← createResourceUnit location "Slot.A"
  let packed ← checked location (Value.pack affineChoice.spelling "Token" [token])
  recordBoundary location [packed, token]
  activateRole "P"

private def keepToken : Explicit.Function :=
  ⟨⟨"Keep", [], [affineChoice.spelling], some
    [.op "issue" "create" [] [] ["token"],
     .variant "pack" affineChoice.spelling "Token" ["token"] "v", .ret ["v"]]⟩, none⟩

private def consumeThenStop : Explicit.Function :=
  ⟨⟨"ConsumeStop", [("v", rngChoice.spelling), ("allowed", "bool")], [], some
    [.localMatch "select" "v" ["allowed"]
      [("Empty", [], [.yield []]),
       ("Coins", ["r"], [.op "drawn" "draw" [] ["r"] ["x", "next"],
         .op "checked" "guard" [] ["allowed"] [], .yield []])] [], .ret []]⟩, none⟩

private def tag : Variant.Descriptor := ⟨.str "pkg/tag", [("yes", []), ("no", [])]⟩
private def transcriptTy : Ty := "transcript:" ++ Bindings.transcriptIdentity
private def originAttributes : List String := ["Protocol", "call", "Function", "draw", "V"]

/-- One arm holds the body under test over four data ports; both arms yield an
`indices` value, so only the operation inside the arm is under test. -/
private def armFunction (body : List Instruction) : Explicit.Function :=
  ⟨⟨"Work", [("v", tag.spelling), ("s", "indices"), ("w", "indices"), ("n", "index"), ("m", "index")],
    ["indices"], some
    [.localMatch "select" "v" ["s", "w", "n", "m"]
      [("yes", [], body), ("no", [], [.yield ["s"]])] ["out"],
     .ret ["out"]]⟩, none⟩

private def admitKernel (contract : String) (arguments : List String := [])
    (locals : List Function := []) (f : Explicit.Function) : Result Unit :=
  admitFunctionWith (environmentSignature (.explicit [⟨"kernel", contract, arguments, ""⟩]) "logical")
    f.code true false locals

private def externalShape (contract : String) (inputs outputs : List Name) : Result Unit :=
  admitKernel contract [] [] (armFunction [.op "effect" "kernel" [] inputs outputs, .yield ["s2"]])

/-- Every external contract that carries transcript history. -/
private def historyShapes : List (String × List Name × List Name) :=
  [("external.openvm.observe", ["s", "w"], ["s2"]),
   ("external.openvm.sample", ["s"], ["s2", "i"]),
   ("external.openvm.sample_ext", ["s"], ["s2", "c"]),
   ("external.openvm.sample_bits", ["s", "n"], ["s2", "i"]),
   ("external.openvm.check_witness", ["s", "n", "m"], ["s2", "ok"]),
   ("external.monero.update", ["s", "w"], ["s2", "h"])]

/-- The external contracts that touch no history: construction and a stateless hash. -/
private def pureShapes : List (String × List Name × List Name) :=
  [("external.monero.init", ["s"], ["s2"]),
   ("external.monero.hash", ["s"], ["s2"]),
   ("external.openvm.init", [], ["s2"])]

private def sampleHelper : Function :=
  ⟨"Effect", [("s", "indices")], ["indices"], some
    [.op "effect" "kernel" [] ["s"] ["s2", "i"], .ret ["s2"]]⟩

private def helperEffect : Result Unit :=
  admitKernel "external.openvm.sample" [] [sampleHelper]
    (armFunction [.call "apply" "Effect" ["s"] ["s2"], .yield ["s2"]])

private def nestedEffect : Result Unit :=
  admitKernel "external.openvm.sample" [] []
    (armFunction [.forLoop "repeat" "i" "n" "m" [("carried", "s")] []
        [.op "effect" "kernel" [] ["carried"] ["next", "drawn"], .yield ["next"]] ["sampled"],
      .yield ["sampled"]])

private def transcriptEffect (contract : String) (arguments : List String)
    (inputs outputs : List Name) : Result Unit :=
  admitKernel contract arguments []
    ⟨⟨"Work", [("v", tag.spelling), ("t", transcriptTy), ("n", "index")], [transcriptTy], some
      [.localMatch "select" "v" ["t", "n"]
        [("yes", [], [.op "effect" "kernel" originAttributes inputs outputs, .yield ["t2"]]),
         ("no", [], [.yield ["t"]])] ["out"],
       .ret ["out"]]⟩, none⟩

private def physical (f : Explicit.Function) : Explicit.Function :=
  let lift := fun (ty : Ty) => match Bindings.valueType false ty with
    | .ok t => {t with representation := Bindings.defaultRepresentation t.kind t.identity}.spelling
    | .error _ => ty
  let code := { f.code with
    arguments := f.code.arguments.map (fun (n, t) => (n, lift t))
    results := f.code.results.map lift }
  { f with code }

/-! Refusals that no command-line input reaches, because an earlier check refuses
first. They still guard every direct caller of these functions. -/
private def refusal {α : Type} (result : Result α) : String :=
  match result with | .error code => code | .ok _ => "success"
private def raised {α : Type} (action : RunM α) : String :=
  match (action.run {}).1 with | .error fault => fault.detail | .ok _ => "success"
private def indices (ns : List Nat) : Value := .fromArithmetic .bls (.indices ns)
private def initRequest (attributes : List String) : Result TypedLocal.Request :=
  match h : Bindings.resolve false ⟨"", "external.monero.init", [], ""⟩ with
  | .ok signature => .ok ⟨"k", "external.monero.init", [], attributes, signature, h⟩
  | .error code => .error code
private def variantKernel : String → List String → Result KernelSignature :=
  fun _ _ => .ok ⟨[choice.spelling], ["index"], true⟩
private def usesVariantKernel : Function :=
  ⟨"F", [("v", choice.spelling)], ["index"], some [.op "k" "kernel" [] ["v"] ["out"], .ret ["out"]]⟩
private def aborted : Explicit.Function := function
  [("Some", ["x"], [.stop "stop" "" "abort"]), ("None", [], [.yield ["fallback"]])]
private def packing (alternative : Name) (payload : List Name) : Explicit.Function :=
  ⟨⟨"Pack", [("x", "index")], [choice.spelling], some
    [.variant "pack" choice.spelling alternative payload "v", .ret ["v"]]⟩, none⟩
private def closedAgainst (source candidate : Explicit.Function) (name : Name) : String :=
  refusal (Generic.validateClosed source bindings ⟨false, bindings, [candidate], .arr #[], .arr #[]⟩ name)

def run : IO Unit := do
  let checks ← Tests.Checks.start
  let inventory := include_str "../../tests/fixtures/variants/history-contracts.txt"
  for row in inventory.splitOn "\n" do
    if !row.isEmpty then
      let [contract, expected] := row.splitOn " " | throw (IO.userError "history inventory row")
      checks.holds (expected == "0" || expected == "1") "history inventory value"
      checks.holds (Bindings.historyContract contract == (expected == "1")) s!"history inventory: {contract}"

  let commonStop := Json.arr #[Json.arr #[.str "stop", .str "halt", .str "", .str "reject"]]
  let projectedStop := Json.arr #[Json.arr #[.str "stop", .str "halt", .str "reject"]]
  let decodeStop := fun code sourceLocal =>
    Decode.body limits.depth .localFunction code (Explicit.typeName false) false sourceLocal
  checks.holds ((decodeStop commonStop true).isOk) "common local stop has empty owner slot"
  checks.holds (!(decodeStop projectedStop true).isOk) "common stop rejects projected spelling"
  checks.holds ((decodeStop projectedStop false).isOk) "projected local stop omits owner slot"
  checks.holds (!(decodeStop commonStop false).isOk) "projected stop rejects common spelling"
  checks.holds ((Variant.parse choice.spelling).toOption == some choice) "canonical descriptor roundtrip"
  checks.holds ((Bindings.valueType false choice.spelling).isOk) "logical descriptor"
  checks.holds ((Bindings.valueType true (choice.spelling ++ "@logical.variant/1")).isOk) "physical descriptor"
  checks.holds (!(Bindings.valueType true (choice.spelling ++ "@native.variant/1")).isOk) "fixed representation"
  checks.holds (!(Bindings.valueType false choice.spelling.toUpper).isOk) "uppercase hex refused"
  let spaced := "variant:" ++ Variant.hex (" " ++ choice.json.compress).toUTF8
  checks.holds (!(Bindings.valueType false spaced).isOk) "noncanonical JSON refused"
  let malformed := fun d => !(Bindings.valueType false (Variant.Descriptor.spelling d)).isOk
  checks.holds (malformed ⟨.str "", [("A", [])]⟩) "empty nominal refused"
  checks.holds (malformed ⟨.str "é", [("A", [])]⟩) "nonASCII nominal refused"
  checks.holds (malformed ⟨.str "bad\n", [("A", [])]⟩) "control nominal refused"
  checks.holds (malformed ⟨.str (String.ofList (List.replicate 262145 'x')), [("A", [])]⟩) "nominal bound"
  checks.holds (malformed ⟨.str "N", []⟩) "empty alternatives refused"
  checks.holds (malformed ⟨.str "N", [("A", []), ("A", [])]⟩) "duplicate alternatives refused"
  checks.holds (malformed ⟨.str "N", [("0bad", [])]⟩) "label grammar"
  checks.holds (malformed ⟨.str "N", [("A", ["bool@native.bool/1"])]⟩) "physical payload refused"
  checks.holds (malformed ⟨.str "N", [("A", ["unknown"])]⟩) "unknown payload refused"
  checks.holds (malformed ⟨.str "N", [("A", List.replicate 129 "bool")]⟩) "payload bound"
  checks.holds (malformed ⟨.str "N", (List.range 33).map (fun i => (s!"A{i}", []))⟩) "alternative bound"
  checks.holds (duplicable choice.spelling && discardable choice.spelling && !serializable choice.spelling) "public leaves still private tag"
  checks.holds (!duplicable affineChoice.spelling && affine affineChoice.spelling && discardable affineChoice.spelling) "inactive affine leaf prevents copying"
  checks.holds (!discardable rngChoice.spelling) "inactive RNG prevents release"
  let nested : Variant.Descriptor := ⟨.str "Nested", [("Wrap", [affineChoice.spelling])]⟩
  checks.holds ((Bindings.valueType false nested.spelling).isOk && !duplicable nested.spelling) "nested conservative permissions"
  checks.holds ((Value.pack choice.spelling "Some" [index 5]).isOk) "active pack"
  checks.holds (!(Value.pack choice.spelling "Some" [.boolean true]).isOk) "wrong active type refused"
  checks.holds (!(Value.pack choice.spelling "None" [index 5]).isOk) "inactive extra payload refused"
  checks.holds (!(Value.pack choice.spelling "Other" []).isOk) "unknown active tag refused"
  let someValue := Value.variant choice "Some" [index 5]
  let noneValue := Value.variant choice "None" []
  checks.holds (noneValue.leaves.isEmpty && !noneValue.public && !noneValue.wire.isOk) "zero payload no inactive value or codec"
  checks.holds (returns good [someValue, index 7] [index 12]) "selected payload then capture"
  checks.holds (returns good [noneValue, index 7] [index 7]) "other arm only"
  checks.holds (!(admitted (function [("Some", ["x"], [.yield ["x"]])])).isOk) "missing arm refused"
  checks.holds (!(admitted (function [("None", [], [.yield ["fallback"]]), ("Some", ["x"], [.yield ["x"]])])).isOk) "reordered arms refused"
  checks.holds (!(admitted (function [("Some", ["x"], [.yield ["x"]]), ("None", [], [.yield ["x"]])])).isOk) "inactive payload inaccessible"
  checks.holds (admitted (function [("Some", ["x"], [.yield ["v"]]), ("None", [], [.yield ["fallback"]])]) == .error "unbound:v") "scrutinee not implicitly captured"
  checks.holds ((admitted stopped).isOk && returns stopped [noneValue, index 7] [index 7]) "stopping arm needs no yield"
  let stoppedOnly := match execute stopped [someValue, index 7] with
    | .ok (.error fault, state) => fault.reason == "reject" && state.events.isEmpty &&
        fault.location.scope.path == [.localMatch "select" "Some"]
    | _ => false
  checks.holds stoppedOnly "terminal stop bypasses other arm and return"
  let wrongNominal := Value.variant {choice with nominal := "Other"} "Some" [index 5]
  checks.holds (match execute good [wrongNominal, index 7] with | .ok (.error _, _) => true | _ => false) "equal layout wrong nominal refused"
  checks.holds (errorCode aliasUse == "capability-alias") "nested capability alias refused"
  let retained := match execute keepToken [] with
    | .ok (.ok [value], state) => value.leaves.length == 1 && state.resources.length == 1
    | _ => false
  checks.holds retained "active returned resource retained across frame"
  let state : State := { resources := [⟨"coins", "P", none, 2, .rng [11, 17], 0, 0⟩] }
  let coins := Value.variant rngChoice "Coins" [.rng "coins" 0]
  let eventPrefix := match execute consumeThenStop [coins, .boolean false] state with
    | .ok (.error fault, state) => fault.reason == "reject" && state.events.size == 3 &&
        (state.resources.head?.map Resource.generation) == some 1 &&
        (state.resources.head?.map Resource.draws) == some 1
    | _ => false
  checks.holds eventPrefix "stop preserves consumed state and ordered event prefix"
  let exhausted := match execute consumeThenStop [coins, .boolean true]
      { resources := [⟨"coins", "P", none, 0, .rng [], 0, 0⟩] } with
    | .ok (.error fault, state) => fault.reason == "exhausted" && state.events.size == 1
    | _ => false
  checks.holds exhausted "resource exhaustion not caught by match"
  let candidate : Explicit.CandidateLocals := ⟨false, bindings, [good], .arr #[], .arr #[]⟩
  checks.holds ((Generic.validateClosed good bindings candidate "Select").isOk) "logical correspondence"
  let physicalBindings := bindings.map fun b => {b with implementation :=
    (if b.contract.startsWith "resource_unit." then "logical/" else if b.contract.startsWith "index." then "native/" else "arkworks/") ++ b.contract}
  let candidate : Explicit.CandidateLocals := ⟨true, physicalBindings, [physical good], .arr #[], .arr #[]⟩
  checks.holds ((Generic.validateClosed good bindings candidate "Select").isOk) "physical correspondence"
  -- A private tag must not schedule a protocol transcript effect. The external
  -- duplex states carry the same history as the internal transcript family and
  -- are ordinary checked data, so nothing about them is visible in an attribute.
  checks.holds (historyShapes.all fun (contract, inputs, outputs) =>
      externalShape contract inputs outputs == .error "variant-challenge")
    "external history effects refused in an arm"
  checks.holds (pureShapes.all fun (contract, inputs, outputs) =>
      (externalShape contract inputs outputs).isOk)
    "external construction and stateless hash still admitted in an arm"
  checks.holds (helperEffect == .error "variant-challenge") "history effect through a helper refused"
  checks.holds (nestedEffect == .error "variant-challenge") "history effect under a nested loop refused"
  checks.holds (transcriptEffect "transcript.observe.index"
      [Bindings.transcriptIdentity, "zkcv.index/1"] ["t", "n"] ["t2"] == .error "variant-challenge")
    "internal transcript observation refused in an arm"
  checks.holds (transcriptEffect "transcript.challenge"
      [Bindings.transcriptIdentity] ["t"] ["x", "t2"] == .error "variant-challenge")
    "internal transcript challenge refused in an arm"
  -- One logical type has one spelling, on the type path as well as at a use.
  checks.holds (!Bindings.validLogical 8 "bool:" && Bindings.validLogical 8 "bool")
    "canonical leaf spelling on the type path"
  checks.holds (["bool:", "index:", "indices:"].all fun spelling =>
      !(Bindings.valueType false spelling).isOk && !Bindings.validLogical 8 spelling)
    "noncanonical leaf aliases refused by both paths"
  checks.holds (malformed ⟨.str "N", [("A", ["bool:"])]⟩ && malformed ⟨.str "N", [("A", ["indices:"])]⟩)
    "noncanonical payload leaf refused"
  -- The selected arm names itself in the transcript interaction path, as the
  -- native runtime does, not only in the event origin.
  let entered := Reference.enterMatch location "select" "Some"
  checks.holds (entered.scope.path == [.localMatch "select" "Some"] &&
      entered.interactionPath == #[Json.arr #[.str "match", .str "select", .str "Some"]])
    "selected arm extends the local origin and the interaction path together"
  checks.holds (raised (External.compute location "external.monero.init"
      [indices ([2 ^ 64] ++ List.replicate 31 0)]) == "external-u64") "external index beyond u64"
  checks.holds (raised (External.compute location "external.monero.init" [index 3])
      == "external-operands") "external operand kind"
  checks.holds (raised (External.compute location "external.openvm.sample_bits"
      [indices ([External.magic, 1, 2] ++ List.replicate 18 0), indices [1]]) == "external-operands")
    "external operand arity"
  checks.holds (raised (External.compute location "external.monero.bogus" []) == "external-operands")
    "unknown external operation"
  checks.holds (match initRequest ["prefix"] with
      | .ok request => raised (Reference.compute location request [indices (List.replicate 32 0)])
          == "external-attributes"
      | .error _ => false) "external operation attributes"
  checks.holds (refusal (Variant.parse "variant:zz") == "variant-descriptor") "descriptor decoding"
  checks.holds (refusal (Value.validateAt 0 (Value.variant choice "None" [])) == "variant-depth")
    "value nesting fuel"
  checks.holds (refusal (admitFunctionWith variantKernel usesVariantKernel) == "variant-operation-boundary")
    "variant operation port"
  checks.holds (closedAgainst stopped stopped "Select" == "success") "stop correspondence control"
  checks.holds (closedAgainst stopped aborted "Select" == "local-stop-correspondence")
    "stop reason correspondence"
  checks.holds (closedAgainst (packing "Some" ["x"]) (packing "None" []) "Pack"
      == "local-variant-correspondence") "packed alternative correspondence"
  checks.finish "finite local variant reference"

#eval run
end Tests.Variant
