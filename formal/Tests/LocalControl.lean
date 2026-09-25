import Tools.Interactive.GenericReference
import Tools.Interactive.LocalValidation
import Tools.Artifact.Interpreter
import Zkc.Source.FiniteControl

set_option autoImplicit false
namespace Tests.LocalControl
open Tools.Interactive
open Lean (Json)

private def bindings : List OperationBinding :=
  [⟨"add", "index.add", [], ""⟩, ⟨"guard", "control.require", [], ""⟩,
    ⟨"draw", "random.draw", [Bindings.fr], ""⟩]

private def sum : Explicit.Function := ⟨⟨"Sum", [("lo", "index"), ("hi", "index"), ("initial", "index")],
  ["index"], some [.forLoop "loop" "i" "lo" "hi" [("acc", "initial")] []
    [.op "plus" "add" [] ["acc", "i"] ["next"], .yield ["next"]] ["result"], .ret ["result"]]⟩, none⟩

private def location : Reference.Location :=
  ⟨"test", "main", ⟨"root", [.localCall "invoke" "Sum"], "invoke", "P"⟩, none, #[]⟩

private def index (n : Nat) : Reference.Value := .fromArithmetic .bls (.index n)

private def execute (function : Explicit.Function) (inputs : List Reference.Value)
    (state : Reference.State := {}) : Result (Except Reference.Fault (List Reference.Value) × Reference.State) := do
  let typed ← TypedLocal.elaborate bindings function
  return (Reference.executeFunction location typed inputs).run state

private def outcome (function : Explicit.Function) (inputs : List Reference.Value)
    (state : Reference.State := {}) : Json :=
  match execute function inputs state with
  | .error code => .str code
  | .ok (.error fault, _) => .arr #[.str fault.reason, .str fault.detail]
  | .ok (.ok values, _) => Reference.valuesJson values

example : (outcome sum [index 0, index 4, index 0] == .arr #[.arr #[.str "index", .str "6"]]) = true := by native_decide
example : (outcome sum [index 3, index 3, index 9] == .arr #[.arr #[.str "index", .str "9"]]) = true := by native_decide
example : (outcome sum [index 7, index 2, index 9] == .arr #[.arr #[.str "index", .str "9"]]) = true := by native_decide
example : (outcome sum [index 2, index 5, index 1] == .arr #[.arr #[.str "index", .str "10"]]) = true := by native_decide
example : (outcome sum [index 0, index 1048577, index 0] ==
    .arr #[.str "exhausted", .str "local-bound-limit"]) = true := by native_decide
example : (outcome sum [index 0, index 1, index 0] { iterations := 100000 } ==
    .arr #[.str "exhausted", .str "local-iteration-limit"]) = true := by native_decide
example : (outcome sum [index 0, index 0, index 4] { iterations := 100000 } ==
    .arr #[.arr #[.str "index", .str "4"]]) = true := by native_decide

private def branch : Explicit.Function := ⟨⟨"Branch", [("choose", "bool"), ("allowed", "bool"), ("x", "index")],
  ["index"], some [.conditional "branch" "choose" ["allowed", "x"]
    [.yield ["x"]] [.op "guarded" "guard" [] ["allowed"] [], .yield ["x"]] ["out"], .ret ["out"]]⟩, none⟩

example : (outcome branch [.boolean true, .boolean false, index 7] ==
    .arr #[.arr #[.str "index", .str "7"]]) = true := by native_decide
example : (outcome branch [.boolean false, .boolean false, index 7] ==
    .arr #[.str "reject", .str "require"]) = true := by native_decide

private def observedPath : Bool := Id.run do
  let .ok (.error fault, state) := execute branch [.boolean false, .boolean false, index 7] | return false
  return fault.location.scope.path == [.localCall "invoke" "Sum", .localBranch "branch" false] &&
    state.events.size == 1
example : observedPath = true := by native_decide

private def malformed (yes no : List Instruction) : Explicit.Function :=
  { branch with code := { branch.code with body := some [.conditional "branch" "choose" ["allowed", "x"] yes no ["out"], .ret ["out"]] } }
private def admitted (function : Explicit.Function) : Result Unit :=
  admitFunctionWith (environmentSignature (.explicit bindings) "logical") function.code

example : admitted (malformed [.yield ["x"]] [.yield ["missing"]]) = .error "unbound:missing" := by native_decide
example : admitted (malformed [.yield ["x"]] [.yield ["allowed"]]) = .error "local-if-yield" := by native_decide
example : admitted (malformed [.yield ["x"]] [.ret ["x"]]) = .error "local-terminal-context" := by native_decide
example : admitted (malformed [.yield ["x"]] []) = .error "missing-return" := by native_decide
example : admitted (malformed [.yield ["x"]] [.yield ["x"], .yield ["x"]]) = .error "instruction-after-terminal" := by native_decide
example : admitted (malformed [.op "same" "guard" [] ["allowed"] [], .yield ["x"]]
    [.op "same" "guard" [] ["allowed"] [], .yield ["x"]]) = .error "duplicate-site" := by native_decide
example : admitted { sum with code := { sum.code with body := some [.yield ["initial"]] } } =
    .error "local-terminal-context" := by native_decide

private def rng := "rng:" ++ Bindings.fr
private def field := "field:" ++ Bindings.fr
private def resourceBranch : Explicit.Function := ⟨⟨"Draw", [("choose", "bool"), ("r", rng)], [rng, field], some
  [.conditional "choice" "choose" ["r"]
    [.op "yesDraw" "draw" [] ["r"] ["v", "s"], .yield ["s", "v"]]
    [.op "noDraw" "draw" [] ["r"] ["w", "t"], .yield ["t", "w"]] ["next", "value"],
   .ret ["next", "value"]]⟩, none⟩
private def resourceState : Reference.State := { resources := [⟨"coins", "P", none, 2, .rng [11, 17], 0, 0⟩] }
private def singleDraw : Bool := Id.run do
  let .ok (.ok values, state) := execute resourceBranch [.boolean false, .rng "coins" 0] resourceState | return false
  return Reference.valuesJson values == .arr #[.arr #[.str rng, .arr #[.str "coins", .str "1"]], .arr #[.str field, .str "11"]] &&
    (state.resources.head?.map Reference.Resource.generation) == some 1
example : singleDraw = true := by native_decide

example : admitted { resourceBranch with code := { resourceBranch.code with body := some [.conditional "choice" "choose" ["r"] [.yield ["r"]] [.yield ["r"]] ["next"],
     .op "reuse" "draw" [] ["r"] ["v", "s"], .ret ["s", "v"]] } } = .error "interactive-resource-reuse" := by native_decide
example : admitted ⟨⟨"Bad", [("lo", "index"), ("hi", "index"), ("r", rng)], [], some
    [.forLoop "loop" "i" "lo" "hi" [] ["r"] [.yield []] [], .ret []]⟩, none⟩ =
    .error "affine-capture" := by native_decide
example : admitted ⟨⟨"Bad", [("lo", "index"), ("hi", "index"), ("r", rng)], [rng], some
    [.forLoop "loop" "i" "lo" "hi" [("r", "r")] []
      [.op "draw" "draw" [] ["r"] ["v", "next"], .yield ["r"]] ["out"], .ret ["out"]]⟩, none⟩ =
    .error "interactive-resource-reuse" := by native_decide

private def candidate (function : Explicit.Function) : Explicit.CandidateLocals :=
  ⟨false, bindings, [function], .arr #[], .arr #[]⟩
example : (Generic.validateClosed sum bindings (candidate sum) "Sum").isOk = true := by native_decide
example : (Generic.validateClosed branch bindings (candidate branch) "Branch").isOk = true := by native_decide
-- Type-correct candidate mutations in dormant regions and dynamic bounds must fail correspondence.
example : (Generic.validateClosed branch bindings (candidate (malformed [.yield ["x"]] [.yield ["x"]])) "Branch").isOk = false := by native_decide
private def changedLoop : Explicit.Function := { sum with code := { sum.code with body := some [.forLoop "loop" "i" "hi" "lo" [("acc", "initial")] []
    [.op "plus" "add" [] ["acc", "i"] ["next"], .yield ["next"]] ["result"], .ret ["result"]] } }
example : (Generic.validateClosed sum bindings (candidate changedLoop) "Sum").isOk = false := by native_decide

private def genericLoop : Json := (Json.parse r#"["generic_function","Sum",[],[],
  [["lo","index"],["hi","index"],["x","index"]],["index"],
  [["for","loop","i","lo","hi",[["acc","x"]],[],
    [["op","sum","index.add",[],[],["acc","i"],["next"]],["yield",["next"]]],["out"]],
   ["return",["out"]]]]"#).toOption.getD .null
example : (Generic.formDefinition genericLoop).isOk = true := by native_decide

private def genericDead : Json := (Json.parse r#"["generic_function","Bad",[],[],
  [["b","bool"],["x","index"]],["index"],
  [["if","choice","b",["x"],[["yield",["x"]]],[["yield",["hidden"]]],["out"]],
   ["return",["out"]]]]"#).toOption.getD .null
example : (Generic.formDefinition genericDead).isOk = false := by native_decide

example : admitted { sum with code := { sum.code with arguments := [("lo", "bool"), ("hi", "index"), ("initial", "index")] } } =
    .error "local-bound-type" := by native_decide
example : admitted { branch with code := { branch.code with arguments := [("choose", "index"), ("allowed", "bool"), ("x", "index")] } } =
    .error "local-condition-type" := by native_decide

-- All installed group identities admit logical and selected physical dynamic access.
example : ([Bindings.g1, Bindings.ristrettoGroup, Bindings.bn254G1, Bindings.bn254G2].all fun group =>
    (Bindings.resolve false ⟨"get", "curve.get", [group], ""⟩).isOk &&
    (Bindings.resolve true ⟨"get", "curve.get", [group],
      (if group == Bindings.ristrettoGroup then "dalek/" else "arkworks/") ++ "curve.get"⟩).isOk) = true := by native_decide

private def controlledArtifactResource : Result Unit :=
  Tools.Artifact.admitArtifactProfile ⟨.explicit bindings, [resourceBranch.code], [], [], []⟩
    ⟨"main", "P", "V", [], "coins", [], 0, .null⟩
example : controlledArtifactResource = .error "construction-local-control-resource" := by native_decide

-- Artifact source validator uses the same finite typed control combinators,
-- with its own values/arithmetic and request transcript.
private def artifactSum : Bool := Id.run do
  let source : Source := ⟨.explicit bindings, [sum.code], [], [], []⟩
  let descriptor : Tools.Artifact.Descriptor := ⟨"main", "P", "V", [], "coins", [], 0, .null⟩
  let location : Tools.Artifact.Location := { entry := "main", binding := "root", path := [], protocol := "Main", role := "V" }
  let initial : Tools.Artifact.State := {
    cursor := ⟨ByteArray.empty, 0⟩
    root := ByteArray.empty
    configuration := .null
    answers := #[] }
  let inputs := [0, 4, 0].map fun n => Tools.Artifact.Value.fromArithmetic .bls (.index n)
  let (.ok [value], state) := (Tools.Artifact.executeLocal source descriptor location sum.code inputs).run initial | return false
  return (match value.toArithmetic .bls with | .ok (.index n) => n == 6 | _ => false) && state.iterations == 4
example : artifactSum = true := by native_decide

end Tests.LocalControl
