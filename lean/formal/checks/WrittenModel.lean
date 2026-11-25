import ZkcFormalTests.WrittenSubject

open Zkc.Frontend Zkc.Frontend.Written ZkcFormalTests.WrittenSubject
open Zkc.Tests.Frontend.PrintedPackageSupport

private def statementsFor (input : SourceInput) (goals : List String) : IO Statements := do
  let first :: _ := goals | throw (IO.userError "expected a goal")
  let assembly ← Driver.assembleFiles input ["../../libraries", "../../examples", "../../examples/support"]
  let root ← IO.ofExcept (admitSoundnessGoal assembly first)
  let claims ← IO.ofExcept (goalClaims root goals)
  return ⟨claims, claims.functionsBeforeRoot⟩

private def requireArithmetic (s : Statements) : IO Unit := do
  let chosen ← IO.ofExcept s.chosenModel
  unless chosen.model == scalarFieldModelText.model &&
      chosen.hypotheses == scalarFieldModelText.hypotheses do
    throw (IO.userError "expected arithmetic with the source field-size hypothesis")

/-- The length of a sequence and the index of a variant are not field numerals.
Only the payload of the chosen alternative is read. -/
def checkLiteralData : IO Unit := do
  let bindings : Zkc.Vocabulary.Project.Bindings := {}
  let field : bindings.vocabulary.Ty := .nominal (.inl (.field .bls12381Fr))
  let refined : bindings.vocabulary.Ty := .nominal (.inl (.nonzero .bls12381Fr))
  let variant : bindings.vocabulary.Ty := .variant ⟨0⟩ (.cons field (.cons .bool .nil))
  for (ty, data, expected) in [(field, [0], false), (field, [1], true), (refined, [2], true),
      (.seq field none, [2,0,0], false), (.seq field none, [2,0,1], true),
      (variant, [1,1], false), (variant, [0,1], true)] do
    unless Statements.usesFieldNumeral bindings (.literal ty data) == expected do
      throw (IO.userError s!"unexpected classification of literal data {data}")

/-- Compare the public definition of the first goal with and without a second goal that
charges the same scalar draw. -/
def checkGoalIndependent : IO Unit := do
  let input ← source "fixtures/scalar-goals.zkc"
  let definition (goals : List String) : IO String := do
    let s ← statementsFor input goals
    let issued ← IO.ofExcept (s.module "Sampling" {})
    let some claim := (issued.statements.splitOn "\n\n").find? (·.contains "def freeClaimOf ") |
      throw (IO.userError "missing the definition of freeClaimOf")
    return claim
  unless (← definition ["free"]) == (← definition ["free", "paid"]) do
    throw (IO.userError "the free claim changed when a second goal was issued")

def checkLinkedCeilings (work : System.FilePath) : IO Unit := do
  let file := "../../examples/gkr_example.zkc"
  let scheme ← IO.FS.readFile file
  let subject (bound : Nat) := statementsFor ⟨file, Syntax.parseString file
    (scheme ++ s!"\ngoal bound = soundness(Proof, stage = written, statement = fixed) <= {bound}\n")⟩ ["bound"]
  let high ← subject 1
  unless !high.package.bindings.rows.isEmpty do throw (IO.userError "expected project bindings")
  let issued ← IO.ofExcept (high.ceilingModule "LayerCeiling")
  match (← subject 0).ceilingModule "LayerCeiling" with
  | .error why => unless why.contains "GL4" do throw (IO.userError why)
  | .ok _ => throw (IO.userError "accepted a ceiling below the total")
  let checked ← startLakeLean work "LayerCeiling" issued.text (text := false)
  let (ok, output) ← checked
  acceptedOutput "LayerCeiling" ok output issued.theorems allowed

/-- In a field large enough for the source relation there is a third element. -/
def checkFieldSize (work : System.FilePath) : IO Unit := do
  let s ← statementsFor (← source "fixtures/third-element.zkc") ["sound"]
  let issued ← IO.ofExcept (s.module "ThirdElement" {})
  let proof ← IO.FS.readFile "checks/ThirdElement.lean.in"
  let checked ← startLakeLean work "ThirdElement" (issued.statements ++ proof) (text := false)
  let (ok, output) ← checked
  acceptedOutput "ThirdElement" ok output (issued.stated ++ ["field_judged", "field_claim"]) allowed

/-- Scalar equality itself works on arbitrary data. It is the literal one that requires
arithmetic, even though the verifier never samples. -/
def checkLiteral (work : System.FilePath) : IO Unit := do
  let fixture := "fixtures/scalar-literal.zkc"
  let s ← statementsFor (← source fixture) ["sound"]
  requireArithmetic s
  let issued ← IO.ofExcept (s.module "ScalarLiteral" {})
  let proof ← IO.FS.readFile "checks/ScalarLiteral.lean.in"
  let checked ← startLakeLean work "ScalarLiteral" (issued.statements ++ proof) (text := false)
  let (ok, output) ← checked
  acceptedOutput "ScalarLiteral" ok output (issued.stated ++ ["literal_claim"]) allowed
  let zero ← statementsFor (← source fixture [("x == 1", "x == 0")]) ["sound"]
  let chosen ← IO.ofExcept zero.chosenModel
  unless chosen.model == standardModelText.model do throw (IO.userError "scalar zero required arithmetic")

/-- A field interprets the sum at zero rounds. Constant addition is outside this class. -/
def checkZeroRounds (work : System.FilePath) : IO Unit := do
  let statements ← statementsFor (← source "fixtures/zero-round-sumcheck.zkc") ["sound"]
  requireArithmetic statements
  let issued ← IO.ofExcept (statements.module "ZeroRounds" {text := "", theorems := []})
  let consumer ← IO.FS.readFile "checks/ZeroRounds.lean.in"
  let file := "import ZkcFormal.Written.FiniteModel\n" ++ issued.statements ++ consumer
  let checked ← startLakeLean work "ZeroRoundModel" file (text := false)
  let (ok, output) ← checked
  acceptedOutput "ZeroRounds" ok output (issued.stated ++ ["addition_not_constant"]) allowed

#eval checkLiteralData
#eval checkGoalIndependent
#eval IO.FS.withTempDir checkLiteral
#eval IO.FS.withTempDir checkFieldSize
#eval IO.FS.withTempDir checkLinkedCeilings
#eval IO.FS.withTempDir checkZeroRounds
