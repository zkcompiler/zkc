import ZkcTools.StructuredSource.Presentation

/-! Finite, compiled printer controls. Run with `lake env lean --run
checks/RunGenerators.lean presentation-controls OUTPUT_DIRECTORY`. The driver compiles the emitted
Positive.lean and independent negative modules, and requires
their kernel equations to fail. Production imports no example or protocol root.
-/

set_option autoImplicit false
namespace Tests.StructuredPresentation
open Lean Zkc.Source Zkc.Source.Structured Zkc.Source.Structured.NormalForm
open ZkcTools.StructuredSource.Presentation

/- Parameter use is token based and does not count quoted site names. -/
#guard explicitParameters "(b1 : Nat) (b10 : Nat) (ctx : ProtocolContext)"
    ["b1", "b10", "ctx"] "(b10, \"ctx\\\"b1\")" =
    "(_b1 : Nat) (b10 : Nat) (_ctx : ProtocolContext)"

-- A binder used only by a later parameter's type must retain its name.
#guard explicitParameters "(n : Nat) (x : Fin n) (y : Fin (x.val + 1))"
    ["n", "x", "y"] ".halt .abort" =
    "(n : Nat) (x : Fin n) (_y : Fin (x.val + 1))"

def scalar : Ty := .field "bls12-381.fr"
def service : Ty := .service "random.bls12-381.fr/0"

def identity : Function where
  name := "identity"
  kind := .local
  visibility := .privateDef
  inputs := [.index]
  outputs := [.index]
  interface := none
  preconditions := []
  origin := some (.local "identity" [])
  body := .block [] (.ret [0])

def callee : Function where
  name := "child"
  kind := .protocol
  visibility := .publicDef
  inputs := [.index]
  outputs := [.index]
  interface := some ⟨["P", "V"], [["V"]], [["V"]]⟩
  preconditions := []
  origin := some (.protocol ⟨"child", []⟩)
  body := .block [] (.ret [0])

def root : Function where
  name := "main"
  kind := .protocol
  visibility := .publicDef
  inputs := [service, .index, .index]
  outputs := [.index]
  interface := some ⟨["P", "V"], [["V"], ["P", "V"], ["V"]], [["V"]]⟩
  preconditions := []
  origin := some (.protocol ⟨"main", []⟩)
  body := .block [
    .instruction (.exchange "P" "V") [1] [.index] [] "message",
    .instruction .indexEqual [0, 3] [.boolean] [] "",
    .instruction (.guard "V") [0] [] [] "guard",
    .instruction (.draw "V" "bls12-381.fr") [2] [scalar] [] "challenge",
    .instruction (.exchange "V" "P") [0] [scalar] [] "delivery",
    .instruction (.localCall "identity" "V") [3] [.index] [] "owned",
    .instruction (.protocolApply "child" ["P", "V"]) [0] [.index] [] "application",
    .instruction (.protocolRepeat 1 3 ["P", "V"] [["V"]]) [7, 0] [.index]
      [.region [.index, .index] [.index]
        (.block [.instruction (.localCall "identity" "V") [1] [.index] [] "callback_call"] (.yield [0]))] "loop"
  ] (.ret [0])

def snapshot : Snapshot where
  source := "sha256:" ++ String.ofList (List.replicate 64 '0')
  entry := "main"
  domains := []
  relations := []
  bindings := []
  definitions := [.function identity, .function callee, .function root]
  contracts := [⟨"child", []⟩, ⟨"main", []⟩]
  catalogue := blsCatalogue

/-- These tests use actual source admission, including linking and availability. -/
example : (check snapshot).isOk = true := by decide +kernel

def program : Program := (check snapshot).toOption.get (by decide +kernel)

example : check snapshot = .ok program := by kernel_rfl

/-- Transport the admitted selector's indices through a kernel equation, so
the elaborator does not reevaluate complete source admission to infer them. -/
def admittedRootBody : Region protocolDialect [service, .index, .index] [.index] :=
  Eq.mp (show Region protocolDialect (program.payload.protocols.get ⟨1, by decide +kernel⟩).inputs
      (program.payload.protocols.get ⟨1, by decide +kernel⟩).outputs =
      Region protocolDialect [service, .index, .index] [.index] from by kernel_rfl)
    (program.payload.protocols.get ⟨1, by decide +kernel⟩).body

def helper : Helper := ⟨"identity", .local, [.index], [.index]⟩
def child : ProtocolSignature := ⟨"child", ["P", "V"], [.index], [.index], [[1]], [[1]]⟩
def childKey : CalleeKey := ⟨child, 1, .cons .optional .nil, []⟩

def rootRequest (kept : Bool) (role : Nat := 1) : Json := .arr #[
  .str "main", .null, .str (toString role), .str "2",
  .arr #[.str (if role == 1 then "optional" else "absent"), .str "present", .str "optional"],
  .arr #[], .bool true, .arr (if kept then #[.str "identity"] else #[]),
  .arr #[.arr #[.str "child", .str "1", .arr #[.str "optional"], .arr #[]]]]

def callbackRequest : Json := .arr #[
  .str "main", .str "loop", .str "1", .str "2", .arr #[.str "present", .str "optional"],
  .arr #[], .bool true, .arr #[], .arr #[]]

/-- Escaping includes non-ASCII text, NUL, DEL, interpolation-looking text,
newlines, backslashes and quotes; none is treated as Lean source. -/
def unusual : String := "quote\" slash\\\n\t\r 한글 {x} " ++ String.singleton (Char.ofNat 0) ++ String.singleton (Char.ofNat 127)

def escapingForm : Form [] [] [] [.index] :=
  .receive .index unusual 0 <|
  .guard .index (.var .here) (.index 9) <|
  .send .index unusual 0 (.var .here) <|
  .done (.cons (.present (.var .here)) .nil)

def receivedForm : Form [] [] [] [.vector "base", .group "group", .boolean] :=
  .receive (.vector "base") "vector" 0 <|
  .receive (.group "group") "group" 0 <|
  .receive .boolean "boolean" 0 <|
  .done (.cons (.present (.var (.there (.there .here))))
    (.cons (.present (.var (.there .here))) (.cons (.present (.var .here)) .nil)))

def privateForm : Form [] [] [.component (.vector "private"), .component .index] [.vector "private", .index] :=
  .split (.input .here)
    (.halt .incomplete)
    (.done (.cons (.present (.var .here)) (.cons (.input (.there (.there .here))) .nil)))

def privateFinish : Values (fun _ : Ty => Carried) [.vector "private", .index] :=
  .cons .present (.cons .optional .nil)

def embeddingForm : Form [] [] [.value (.field "base")] [.field "extension"] :=
  .done (.cons (.present (.calc (.fieldEmbed "extension" "base") rfl (.cons (.var .here) .nil) .here)) .nil)

def computeForm : Form [] [] [.value (.vector "base"), .value .index] [.field "base"] :=
  .compute (.boundedAt "base") rfl (.cons (.var .here) (.cons (.var (.there .here)) .nil)) <|
  .done (.cons (.present (.result .here .here)) .nil)

def calculationForm : Form [] [] [.value (.field "base"), .value (.field "base")] [.field "base", .boolean] :=
  .done (.cons (.present (.calc (.fieldMultiply "base") rfl
    (.cons (.var .here) (.cons (.var (.there .here)) .nil)) .here))
    (.cons (.present (.calc (.fieldEqual "base") rfl
      (.cons (.var .here) (.cons (.field "base" 2) .nil)) .here)) .nil))

def lawKey : LawKey := ⟨helper, .returns [], []⟩
def lawForm : Form [lawKey] [] [.value .index] [.index] :=
  .byLaw ⟨0, by decide⟩ helper <|
  .done (.cons (.present (.law ⟨0, by decide⟩ (.cons (.var .here) .nil) .here)) .nil)

def identityResults (model : DomainModel) : LawResults model [lawKey] where
  result := fun entry => match entry with
    | ⟨0, _⟩ => fun args => args
    | ⟨n + 1, bound⟩ => False.elim (Nat.not_lt_zero n (Nat.lt_of_succ_lt_succ bound))

def admittedTables (model : DomainModel) : Tables model :=
  program.payload.definitions.foldl
    (Evaluation.ComponentTablesOn.extend model (.silent (Interface model))) ⟨[], []⟩
def changedTables (model : DomainModel) : Tables model :=
  ⟨[⟨helper, fun _ => .halt .abort⟩], []⟩
def helperForm : Form [] [] [.value .index] [.index] :=
  .strict helper (.cons (.var .here) .nil) <|
  .done (.cons (.present (.result .here .here)) .nil)

def badLaw : Form [lawKey] [] [] [] :=
  .byLaw ⟨0, by decide⟩ {helper with name := "different"} (.done .nil)
def badCallee : Form [] [childKey] [] [] := by
  refine Form.apply ⟨0, by decide⟩ {child with outputScopes := [[0]]} [0, 1] "application" ?_ (.done .nil)
  change Values (Argument [] []) [.component .index]
  exact .cons .absent .nil

def refusal {α : Type} : Except String α → String
  | .ok _ => "accepted" | .error error => error
example : refusal (render {} .outputs badLaw) = "presentation-call-identity" := by decide +kernel
example : refusal (render {} .outputs badCallee) = "presentation-call-identity" := by decide +kernel
example : refusal (render {} (.presented (.cons .present .nil))
    (.done (.cons .absent .nil) : Form [] [] [] [.index])) = "presentation-return-shape" := by decide +kernel

-- Numeric IDs keep duplicate, empty, keyword and hostile labels harmless.
example : inputNames (Δ := [.value .index, .value .index, .value .index])
    (.cons (some "match") (.cons (some "match") (.cons (some "x) := by") .nil))) 0 =
    ["b0_match", "b1_match", "b2_xby"] := by decide +kernel

def header : String :=
  "import Tests.StructuredPresentation\n\nset_option autoImplicit false\n" ++
  "open Zkc.Source Zkc.Source.Structured Zkc.Source.Structured.NormalForm\n" ++
  "open Tests.StructuredPresentation\nnamespace GeneratedPresentation\n\n"

def expectOk {α : Type} (result : Except String α) : IO α :=
  match result with | .ok value => pure value | .error error => throw (IO.userError error)

def jsonSource (json : Json) : IO String := expectOk (json.getObjValAs? String "lean_source")

def emit {laws : List LawKey} {callees : List CalleeKey} {Δ : Scope} {out : List Ty}
    (name : String) (form : Form laws callees Δ out) (finish : Finish out := .outputs)
    (naming : Naming laws callees Δ := {})
    (decl : Option ZkcTools.StructuredSource.Presentation.Declaration := none) : IO String := do
  let printed ← expectOk (render naming finish form)
  return declarations naming finish printed (decl.getD (genericDeclaration laws callees name))

def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

def optionalFinish : (out : List Ty) → Values (fun _ => Carried) out
  | [] => .nil | _ :: rest => .cons .optional (optionalFinish rest)

/-- Compile a wrong rendering as a separate module. A generic parser failure
does not count: its diagnostics must identify the kernel's type mismatch. -/
def reject (directory : System.FilePath) (name source : String) : IO Unit := do
  let path := directory / (name ++ ".lean")
  -- An intentionally wrong callee can make its generated type-ascription
  -- tactic redundant. This negative control must reach the kernel equation;
  -- positive generated modules keep all linters enabled.
  IO.FS.writeFile path (header ++ "set_option linter.unusedTactic false\n" ++
    source ++ "\nend GeneratedPresentation\n")
  let result ← IO.Process.output {cmd := "lean", args := #["-DwarningAsError=true", path.toString]}
  IO.FS.writeFile (directory / (name ++ ".log")) (result.stdout ++ result.stderr)
  let errors := result.stdout.splitOn "\n" |>.filter fun line => (line.splitOn ": error").length > 1
  require (result.exitCode != 0 && !errors.isEmpty && errors.all fun line =>
      (line.splitOn "(kernel) declaration type mismatch").length > 1)
    ("negative control did not fail in the kernel: " ++ name ++ "\n" ++ result.stdout ++ result.stderr)

def run (directory : System.FilePath) : IO Unit := do
  IO.FS.createDirAll directory
  let strict ← expectOk (ZkcTools.StructuredSource.Presentation.run program (rootRequest false)
    (declaration := fun selected => genericDeclaration selected.signature.laws selected.signature.callees "strict")
    (bodyExpression := some "admittedRootBody"))
  let kept ← expectOk (ZkcTools.StructuredSource.Presentation.run program (rootRequest true)
    (declaration := fun selected => genericDeclaration selected.signature.laws selected.signature.callees "kept"))
  let strictSource ← jsonSource strict
  let keptSource ← jsonSource kept
  require ((strictSource.splitOn ".receive").length > 1 && (strictSource.splitOn ".query").length > 1 &&
    (strictSource.splitOn ".send").length > 1 && (strictSource.splitOn "@ite").length > 1 &&
    (strictSource.splitOn ".run").length > 1 && (strictSource.splitOn ".enter").length > 1)
    "admitted root did not exercise expected process constructors"
  require ((keptSource.splitOn "Participant.owned").length > 1) "kept call was not rendered"
  let selected ← expectOk (select program callbackRequest)
  let callback ← expectOk (ZkcTools.StructuredSource.Presentation.run program callbackRequest
    (declaration := fun s => genericDeclaration s.signature.laws s.signature.callees "callback")
    (finish := fun s => .presented (optionalFinish s.outputs)))
  let callbackSource ← jsonSource callback
  -- Admission retains a mark before each operation, including the repeat.
  require (selected.path == List.replicate 15 1 ++ [0]) "wrong admitted repeat callback address"
  let emptyBody : Region protocolDialect [] [] := .ret .nil
  let (roster, _, _) ← expectOk (request {} emptyBody 0 2 .nil {} .outputs true)
  require (roster == 1) "normalizer-derived roster minimization failed"
  let (roster, _, _) ← expectOk (request selected.signature selected.body 1 2 selected.pattern {} .outputs true)
  require (roster == 2) "role-one roster changed"
  require ((request selected.signature selected.body 1 1 selected.pattern {}).toOption.isNone)
    "out-of-roster owned call accepted"
  let escaping ← emit "escaping" escapingForm
  let privateState ← emit "privateState" privateForm (.presented privateFinish)
    {inputs := .cons (some "match") (.cons (some "match") .nil)}
  let embedding ← emit "embedding" embeddingForm
  let compute ← emit "compute" computeForm
  let calculation ← emit "calculation" calculationForm
  let law ← emit "law" lawForm
  let readableLaw ← emit "readableLaw" lawForm .outputs {
    results := "(identityResults model)", lawResult := fun _ _ => some "{0}"}
  let received ← emit "received" receivedForm .outputs {label := fun _ => some "match"}
  let bodyNaming : Naming [] [] [.value .index] := {tables := "admittedTables model"}
  let bodyPrinted ← expectOk (render bodyNaming .outputs helperForm)
  let helperBody := declarations (out := [.index]) bodyNaming .outputs bodyPrinted (genericDeclaration [] [] "helperBody")
  let uniformNaming : Naming [] [] [] := {carriers := .uniform "F" "G"}
  let uniformDecl : ZkcTools.StructuredSource.Presentation.Declaration := {
    name := "uniform"
    parameters := "{F G : Type} [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] " ++
      "(tables : Tables (ringModel F G)) (results : LawResults (ringModel F G) []) " ++
      "(ctx : ProtocolContext) (runs : Runs (ringModel F G)) (processes : CalleeProcesses (ringModel F G) [])"
    arguments := ["(F := F)", "(G := G)", "tables", "results", "ctx", "runs", "processes"]}
  let uniform ← emit "uniform" receivedForm .outputs uniformNaming (some uniformDecl)
  let stops ← ([PIR.Stop.reject, .abort, .exhausted, .incomplete, .refused].zipIdx).mapM fun (stop, i) =>
    emit ("stop" ++ toString i) (.halt stop : Form [] [] [] [])
  let dependentDecl := genericDeclaration [] [] "dependent"
  let dependentDecl := { dependentDecl with
    parameters := dependentDecl.parameters ++ " (n : Nat) (x : Fin n)"
    arguments := dependentDecl.arguments ++ ["n", "x"] }
  let dependent ← emit "dependent" (.halt .abort : Form [] [] [] [])
    .outputs {} (some dependentDecl)
  let escapedString := "example : " ++ quoted unusual ++ " = unusual := by kernel_rfl\n"
  let positive := header ++ String.intercalate "\n" ([strictSource, keptSource, callbackSource, escaping,
    privateState, embedding, compute, calculation, law, readableLaw, received, helperBody, uniform, dependent, escapedString] ++ stops) ++
    "\nend GeneratedPresentation\n"
  let positivePath := directory / "Positive.lean"
  IO.FS.writeFile positivePath positive
  let result ← IO.Process.output {cmd := "lean", args := #["-DwarningAsError=true", positivePath.toString]}
  IO.FS.writeFile (directory / "Positive.log") (result.stdout ++ result.stderr)
  require (result.exitCode == 0) ("generated positive module failed:\n" ++ result.stdout ++ result.stderr)
  -- Changing a typed receive binder's use preserves parsing and typing but not
  -- the all-response equation. The old sender value is never substituted.
  let printed ← expectOk (render {} .outputs escapingForm)
  let wrongProcess := printed.process.replace "some (b0)" "some (8)"
  require (wrongProcess != printed.process) "receive mutation did not change generated source"
  let wrongReceive := declarations (laws := []) (callees := []) (Δ := []) (out := [.index])
    {} .outputs {printed with process := wrongProcess}
    (genericDeclaration [] [] "escaping")
  reject directory "WrongReceive" wrongReceive
  let wrongSite := escaping.replace ("qualifyProtocolSite (ctx).applicationPrefix " ++ quoted unusual)
    ("qualifyProtocolSite (ctx).applicationPrefix \"wrong-site\"")
  require (wrongSite != escaping) "site mutation did not change generated source"
  reject directory "WrongSite" wrongSite
  let wrongHelper ← emit "wrongHelper" lawForm .outputs {
    lawResult := fun _ _ => some "999"}
  reject directory "WrongLawBody" wrongHelper
  let wrongKept ← expectOk (ZkcTools.StructuredSource.Presentation.run program (rootRequest true)
    (naming := fun _ => {helpers := [(helper, helperText {helper with name := "changed"})]})
    (declaration := fun s => genericDeclaration s.signature.laws s.signature.callees "wrongKept"))
  reject directory "WrongHelperIdentity" (← jsonSource wrongKept)
  let wrongCallee ← expectOk (ZkcTools.StructuredSource.Presentation.run program (rootRequest false)
    (naming := fun _ => {callee := fun _ => some "(fun _ _ => .halt .abort)"})
    (declaration := fun s => genericDeclaration s.signature.laws s.signature.callees "wrongCallee"))
  reject directory "WrongCalleeBody" (← jsonSource wrongCallee)
  let wrongCallback ← expectOk (ZkcTools.StructuredSource.Presentation.run program (rootRequest false)
    (naming := fun _ => {callback := fun _ _ => some "(fun _ => .halt .abort)"})
    (declaration := fun s => genericDeclaration s.signature.laws s.signature.callees "wrongCallback"))
  reject directory "WrongCallbackBody" (← jsonSource wrongCallback)
  let wrongBody ← expectOk (ZkcTools.StructuredSource.Presentation.run program (rootRequest false)
    (declaration := fun s => genericDeclaration s.signature.laws s.signature.callees "wrongBody")
    (bodyExpression := some "(.ret (.cons (.there .here) .nil))"))
  reject directory "WrongSourceBody" (← jsonSource wrongBody)
  -- The called helper's complete key is unchanged; only its stored body differs.
  let changedProcess := bodyPrinted.process.replace "admittedTables model" "changedTables model"
  require (changedProcess != bodyPrinted.process) "same-name helper body mutation did not change source"
  let wrongHelperBody := declarations (out := [.index]) bodyNaming .outputs
    {bodyPrinted with process := changedProcess} (genericDeclaration [] [] "helperBody")
  reject directory "WrongHelperBody" wrongHelperBody
  IO.println "presentation: generated positive module checked; eight kernel rejection controls passed"

end Tests.StructuredPresentation

def Tests.StructuredPresentation.main (args : List String) : IO Unit := do
  let [directory] := args | throw (IO.userError "expected output directory")
  Tests.StructuredPresentation.run directory
