import ZkcFormalTests.WrittenSubject

open Zkc.Frontend Zkc.Frontend.Written ZkcFormalTests.WrittenSubject
open Zkc.Tests.Frontend.PrintedPackageSupport

/-- The charge on one draw must not change the hypothesis of an unrelated draw. Both the
position and the scalar instruction are in a callee. -/
def checkScalarCharges : IO Unit := do
  let source (charge : String) :=
    "module sampling\nuse zkc::security::{soundness}\ntype F = primitive(\"bls12-381.fr\")\n" ++
    "relation Holds(b: bool): b\nprotocol Sample roles(P,V)(b: bool @(P,V)):\n" ++
    "    p <- draw index<4> from V to P\n    r <- draw F from V to P\n    guard @V b\n" ++
    (if charge.isEmpty then "" else "spec for Sample:\n    charge " ++ charge ++ "\n") ++
    "protocol Root roles(P,V)(b: bool @(P,V)):\n    Sample(b)\n" ++
    "spec for Root:\n    proves @V Holds(b)\nscheme Checked = Root:\n    prover P\n" ++
    "    construction interactive\ngoal sound = soundness(Checked)\n"
  for (charge, expected) in [("", arithmeticModelText), ("sites.p <= 1 / 4", arithmeticModelText),
      ("sites.r <= 0", arithmeticModelText), ("sites.r <= 1", arithmeticModelText),
      ("sites.r <= 1 / F::Order", scalarFieldModelText)] do
    let root ← IO.ofExcept (goalRoot (source charge) "sound")
    let claims ← IO.ofExcept (goalClaims root ["sound"])
    let statements : Statements := {claims}
    let chosen ← IO.ofExcept statements.chosenModel
    unless chosen.model == expected.model && chosen.hypotheses == expected.hypotheses do
      throw (IO.userError s!"unexpected class or field-size assumption for charge `{charge}`")

/-- A field interprets the sum of a scalar sequence even at zero rounds. There is no charge
and no lower bound on the field order. The Boolean algebra with constant addition that
refutes the statement over arbitrary data is outside this class. -/
def checkZeroRounds (work : System.FilePath) : IO Unit := do
  let entry ← source "fixtures/zero-round-sumcheck.zkc"
  let assembly ← Driver.assembleFiles entry ["../../libraries", "../../examples", "../../examples/support"]
  let root ← IO.ofExcept (admitSoundnessGoal assembly "sound")
  let claims ← IO.ofExcept (goalClaims root ["sound"])
  let statements : Statements := ⟨claims, claims.functionsBeforeRoot⟩
  let chosen ← IO.ofExcept statements.chosenModel
  unless chosen.model == arithmeticModelText.model && chosen.hypotheses.isEmpty do
    throw (IO.userError "a sum without a draw requires arithmetic over an arbitrary finite field")
  let issued ← IO.ofExcept (statements.module "ZeroRounds" {text := "", theorems := []})
  let consumer ← IO.FS.readFile "checks/ZeroRounds.lean.in"
  let file := "import ZkcFormal.Written.FiniteModel\n" ++ issued.statements ++ consumer
  let checked ← startLakeLean work "ZeroRoundModel" file (text := false)
  let (ok, output) ← checked
  acceptedOutput "ZeroRounds" ok output (issued.stated ++ ["addition_not_constant"]) allowed

#eval checkScalarCharges
#eval IO.FS.withTempDir checkZeroRounds
