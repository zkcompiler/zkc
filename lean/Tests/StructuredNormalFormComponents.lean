import ZkcTools.StructuredSource.Presentation

/-! Exact component-call and arbitrary-guard controls. These equations retain
optional inputs, helper stops, and every typed reply of the open Process. -/

set_option autoImplicit false
namespace Tests.StructuredNormalFormComponents
open Zkc.Source Zkc.Source.Structured NormalForm

variable (model : DomainModel)

def noResults : LawResults model [] where
  result := fun entry => entry.elim0

def emptyTables : Tables model := ⟨[], []⟩

def optionalPair : InputPattern [.boolean, .boolean] := .cons .optional (.cons .optional .nil)

def conjunctionBody : Region dialect [.boolean, .boolean] [.boolean] :=
  .letOp .booleanAnd (.cons .here (.cons (.there .here) .nil)) .nil (.ret (.cons .here .nil))

def conjunction : CheckedDefinition where
  name := "combine"
  kind := .math
  inputs := [.boolean, .boolean]
  outputs := [.boolean]
  raw := conjunctionBody.erase
  body := conjunctionBody
  formed := Region.elaborate_erase conjunctionBody

def conjunctionTables : Tables model :=
  Evaluation.ComponentTablesOn.extend model (.silent _) (emptyTables model) conjunction

def mathBody : Region protocolDialect [.boolean, .boolean] [.boolean] :=
  .letOp (.calculate (.invoke conjunction.helper) rfl)
    (.cons .here (.cons (.there .here) .nil)) .nil (.ret (.cons .here .nil))

def mathForm : Form [] [] optionalPair.scope [.boolean] :=
  .math conjunction.helper (.cons (.input .here) (.cons (.input (.there .here)) .nil))
    (.done (.cons (.read .here .here) .nil))

example : normalize {} mathBody 0 1 optionalPair = .ok mathForm := by kernel_rfl
example : mathForm.CallsMatch := by kernel_rfl
example : mathForm.finishes (.cons .optional .nil) = true := by kernel_rfl

/-- The equation quantifies every helper table, optional input and typed reply.
It assumes no helper truth or totality law. -/
theorem math_exact (tables : Tables model) (left right : Option Bool) :
    mathBody.denote (meaningAt model tables [] {} 0) (optionalPair.environment model (.cons left (.cons right .nil))).get =
      mathForm.denote model tables (noResults model) {} (runsAt model tables [] {} 0) (noCallees model)
        (.cons left (.cons right .nil)) :=
  normalize_sound {} mathBody 0 1 optionalPair mathForm (by kernel_rfl) (by kernel_rfl)
    (RosterDistinct.root 0 1) (noResults model) (noCallees model) _
    (fun entry => entry.elim0) (noCallees_hold _ _)

/-- This nonprojection Math helper computes conjunction. -/
example : mathForm.denote model (conjunctionTables model) (noResults model) {}
    (runsAt model (conjunctionTables model) [] {} 0) (noCallees model)
    (.cons (some true) (.cons (some false) .nil)) = .done (.cons (some false) .nil) := by kernel_rfl

example : mathForm.denote model (conjunctionTables model) (noResults model) {}
    (runsAt model (conjunctionTables model) [] {} 0) (noCallees model)
    (.cons (some true) (.cons (some true) .nil)) = .done (.cons (some true) .nil) := by kernel_rfl

/-- Missing operands stay optional; they do not become a fabricated Boolean. -/
example : mathForm.denote model (conjunctionTables model) (noResults model) {}
    (runsAt model (conjunctionTables model) [] {} 0) (noCallees model)
    (.cons none (.cons (some true) .nil)) = .done (.cons none .nil) := by kernel_rfl

example : mathForm.denote model (conjunctionTables model) (noResults model) {}
    (runsAt model (conjunctionTables model) [] {} 0) (noCallees model)
    (.cons (some true) (.cons none .nil)) = .done (.cons none .nil) := by kernel_rfl

/-- The same signature and name, with a body that ignores its first input. -/
def secondBody : Region dialect [.boolean, .boolean] [.boolean] := .ret (.cons (.there .here) .nil)
def secondDefinition : CheckedDefinition :=
  {conjunction with raw := secondBody.erase, body := secondBody, formed := Region.elaborate_erase secondBody}
def secondTables : Tables model :=
  Evaluation.ComponentTablesOn.extend model (.silent _) (emptyTables model) secondDefinition

/-- Strict sequencing of the whole input tuple would incorrectly lose this result. -/
example : mathForm.denote model (secondTables model) (noResults model) {}
    (runsAt model (secondTables model) [] {} 0) (noCallees model)
    (.cons none (.cons (some true) .nil)) = .done (.cons (some true) .nil) := by kernel_rfl

def stoppedBody : Region dialect [.boolean, .boolean] [.boolean] := .stop .abort
def stoppedDefinition : CheckedDefinition :=
  {conjunction with raw := stoppedBody.erase, body := stoppedBody, formed := Region.elaborate_erase stoppedBody}
def stoppedTables : Tables model :=
  Evaluation.ComponentTablesOn.extend model (.silent _) (emptyTables model) stoppedDefinition

/-- A helper stop is preserved even when a call input is absent. -/
example : mathForm.denote model (stoppedTables model) (noResults model) {}
    (runsAt model (stoppedTables model) [] {} 0) (noCallees model)
    (.cons none (.cons (some true) .nil)) = .halt .abort := by kernel_rfl

/-- Exact calls preserve an effectful table's event and every Boolean reply. -/
def effectTables : Tables model :=
  ⟨[], [⟨conjunction.helper, fun _ => .call (.receive .boolean "helper" 0) fun reply =>
    .done (.cons (some reply) .nil)⟩]⟩

example : mathForm.denote model (effectTables model) (noResults model) {}
    (runsAt model (effectTables model) [] {} 0) (noCallees model)
    (.cons none (.cons none .nil)) =
      .call (.receive .boolean "helper" 0) (fun reply => .done (.cons (some reply) .nil)) := by kernel_rfl

/-- A closed returning law cannot replace an optional-component call. -/
def returningSignature : Signature := {laws := [⟨conjunction.helper, .returns [.literal 1], []⟩]}
example : (normalize returningSignature mathBody 0 1 optionalPair).isOk = true := by kernel_rfl
example : (normalize {laws := [⟨conjunction.helper, .stops .reject, []⟩]} mathBody 0 1 optionalPair).isOk = true := by
  kernel_rfl

/-- A malformed projection is still refused, rather than silently assumed. -/
example : normalize {laws := [⟨conjunction.helper, .passes [2], []⟩]} mathBody 0 1 optionalPair =
    .error "law-positions" := by kernel_rfl

/-- A received Boolean can be false. The guard is checked after the receive. -/
def receiveBody : Region protocolDialect [.boolean] [.boolean] :=
  .letOp (.exchange .boolean 0 1 "reply") (.cons .here .nil) .nil
    (.letOp (.guard 1 "check") (.cons .here .nil) .nil (.ret (.cons .here .nil)))
def receivePattern : InputPattern [.boolean] := .cons .absent .nil
def receiveForm : Form [] [] [] [.boolean] :=
  .receive .boolean "reply" 0 <|
  .guard .boolean (.var .here) (.bool true) (.done (.cons (.present (.bool true)) .nil))

example : normalize {} receiveBody 1 2 receivePattern = .ok receiveForm := by kernel_rfl

theorem receive_exact (tables : Tables model) :
    receiveBody.denote (meaningAt model tables [] {} 1) (receivePattern.environment model .nil).get =
      receiveForm.denote model tables (noResults model) {} (runsAt model tables [] {} 1) (noCallees model) .nil :=
  normalize_sound {} receiveBody 1 2 receivePattern receiveForm (by kernel_rfl) (by kernel_rfl)
    (RosterDistinct.root 1 2) (noResults model) (noCallees model) .nil
    (fun entry => entry.elim0) (noCallees_hold _ _)

example : receiveForm.denote model (emptyTables model) (noResults model) {}
    (runsAt model (emptyTables model) [] {} 1) (noCallees model) .nil =
      .call (.receive .boolean "reply" 0) (fun reply =>
        if reply = true then .done (.cons (some true) .nil) else .halt .reject) := by kernel_rfl

/-- The actual-source shape: compare an arbitrary helper result with false. -/
def negativeGuardBody : Region protocolDialect [.boolean] [] :=
  .letOp (.calculate (.booleanConstant false) rfl) .nil .nil <|
  .letOp (.calculate .booleanEqual rfl) (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.guard 0 "negative") (.cons .here .nil) .nil (.ret .nil)
def guardPattern : InputPattern [.boolean] := .cons .optional .nil

def guardForm : Form [] [] guardPattern.scope [] :=
  .split (.input .here) (.halt .incomplete) <|
  .guard .boolean (.calc .booleanEqual rfl (.cons (.var .here) (.cons (.bool false) .nil)) .here)
    (.bool true) (.done .nil)

example : normalize {} negativeGuardBody 0 1 guardPattern = .ok guardForm := by kernel_rfl
example : guardForm.denote model (emptyTables model) (noResults model) {}
    (runsAt model (emptyTables model) [] {} 0) (noCallees model) (.cons (some false) .nil) = .done .nil := by kernel_rfl
example : guardForm.denote model (emptyTables model) (noResults model) {}
    (runsAt model (emptyTables model) [] {} 0) (noCallees model) (.cons (some true) .nil) = .halt .reject := by kernel_rfl
example : guardForm.denote model (emptyTables model) (noResults model) {}
    (runsAt model (emptyTables model) [] {} 0) (noCallees model) (.cons none .nil) = .halt .incomplete := by kernel_rfl

-- A same-name changed Math body does not satisfy the conjunction equation.
/-- error: (kernel) declaration type mismatch -/
#guard_msgs (substring := true) in
example : mathForm.denote model (secondTables model) (noResults model) {}
    (runsAt model (secondTables model) [] {} 0) (noCallees model)
    (.cons (some false) (.cons (some true) .nil)) = .done (.cons (some false) .nil) := by kernel_rfl

-- Erasing an arbitrary guard is rejected by the kernel.
/-- error: (kernel) declaration type mismatch -/
#guard_msgs (substring := true) in
example : guardForm.denote model (emptyTables model) (noResults model) {}
    (runsAt model (emptyTables model) [] {} 0) (noCallees model) (.cons (some true) .nil) = .done .nil := by kernel_rfl

open ZkcTools.StructuredSource.Presentation

def expectOk {α : Type} : Except String α → IO α
  | .ok value => pure value
  | .error refusal => throw (IO.userError refusal)

def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

def printedHeader : String :=
  "import Tests.StructuredNormalFormComponents\n" ++
  "set_option autoImplicit false\n" ++
  "open Zkc.Source Zkc.Source.Structured Zkc.Source.Structured.NormalForm\n" ++
  "open Tests.StructuredNormalFormComponents\nnamespace PrintedComponentControls\n"

def checkPrinted (directory : System.FilePath) (name source : String) (positive : Bool) : IO Unit := do
  let path := directory / (name ++ ".lean")
  IO.FS.writeFile path (printedHeader ++ source ++ "\nend PrintedComponentControls\n")
  let result ← IO.Process.output {cmd := "lean", args := #[path.toString]}
  let log := result.stdout ++ result.stderr
  IO.FS.writeFile (directory / (name ++ ".log")) log
  if positive then
    require (result.exitCode == 0) ("printed component failed: " ++ name ++ "\n" ++ log)
  else
    let errors := log.splitOn "\n" |>.filter fun line => (line.splitOn ": error").length > 1
    require (result.exitCode != 0 && !errors.isEmpty && errors.all fun line =>
      (line.splitOn "(kernel) declaration type mismatch").length > 1)
      ("mutation did not fail in the kernel: " ++ name ++ "\n" ++ log)

/-- The printer emits ordinary Lean. Compile its independent equations, and
require typed changes to the guard and same-name helper body to fail. -/
def run (directory : System.FilePath) : IO Unit := do
  IO.FS.createDirAll directory
  let math ← expectOk (render {} (.presented (.cons .optional .nil)) mathForm)
  let guard ← expectOk (render {} .outputs guardForm)
  let received ← expectOk (render {} .outputs receiveForm)
  let knownNaming : Naming [] [] optionalPair.scope := {tables := "conjunctionTables model"}
  let known ← expectOk (render knownNaming .outputs mathForm)
  let mathSource := declarations (laws := []) (callees := []) (Δ := optionalPair.scope) (out := [.boolean]) {} (.presented (.cons .optional .nil)) math (genericDeclaration [] [] "mathOptional")
  let guardSource := declarations (laws := []) (callees := []) (Δ := guardPattern.scope) (out := []) {} .outputs guard (genericDeclaration [] [] "arbitraryGuard")
  let receiveSource := declarations (laws := []) (callees := []) (Δ := []) (out := [.boolean]) {} .outputs received (genericDeclaration [] [] "receivedGuard")
  let knownSource := declarations (out := [.boolean]) knownNaming .outputs known (genericDeclaration [] [] "knownMath")
  checkPrinted directory "Positive" (mathSource ++ guardSource ++ receiveSource ++ knownSource) true
  let wrongGuard := guard.process.replace "(true)" "(false)"
  require (wrongGuard != guard.process) "guard mutation did not change source"
  checkPrinted directory "WrongGuard"
    (declarations (laws := []) (callees := []) (Δ := guardPattern.scope) (out := []) {} .outputs {guard with process := wrongGuard} (genericDeclaration [] [] "wrongGuard")) false
  let wrongMath := known.process.replace "conjunctionTables model" "secondTables model"
  require (wrongMath != known.process) "helper-body mutation did not change source"
  checkPrinted directory "WrongMathBody"
    (declarations (out := [.boolean]) knownNaming .outputs {known with process := wrongMath} (genericDeclaration [] [] "wrongMath")) false
  IO.println "normalizer components: four printed equations checked; two typed kernel rejection controls passed"

end Tests.StructuredNormalFormComponents

def Tests.StructuredNormalFormComponents.main (args : List String) : IO Unit := do
  let [directory] := args | throw (IO.userError "expected output directory")
  Tests.StructuredNormalFormComponents.run directory
