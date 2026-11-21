import Zkc.Tests.Formal.ExternalRound
import Zkc.Tests.Frontend.PrintedPackageSupport

#eval show IO Unit from do
  let root := (← IO.currentDir) / ".." / ".."
  Zkc.Tests.Formal.ExternalRound.run root
  let text ← Zkc.Tests.Formal.ExternalRound.statement root
  IO.FS.withTempDir fun work => do
    let checks := "\nnamespace CoefficientStatement\n" ++
      "example : soundCaps.counted stored rootKey = true := by decide +kernel\n" ++
      "example : soundCaps.budget = 1 / Zkc.Vocabulary.Field.bls12381Fr.order := by decide +kernel\n" ++
      "#check soundGoal\nend CoefficientStatement\n"
    let task ← Zkc.Tests.Frontend.PrintedPackageSupport.startLakeLean work "CoefficientStatement" (text ++ checks)
    let (ok, output) ← Zkc.Tests.Frontend.PrintedPackageSupport.finishLean task
    unless ok do throw (IO.userError output)

open Zkc.Core Zkc.Frontend.Written Zkc.Tools.Formal Zkc.Formal.Interactive.Sumcheck
open Zkc.Formal.Written Zkc.Formal.FiniteService Zkc.Formal.ProbabilisticProcess OracleComp
open scoped ENNReal

/-- A client of the compiled API states the false-sum experiment and the numerical ceiling. -/
theorem coefficientVerifierBound {c : AdmittedRoot} {n : Nat}
    (g : SingleRoundGoal c n "sound" "challenge" Coefficients.expression)
    (standard : c.emission.bindings.rows = [])
    (unitFee : g.checked.issued.charge.numerator = 1)
    (order : g.checked.issued.charge.denominator = Zkc.Vocabulary.Field.bls12381Fr.order)
    {σ : Type} (advance : Occurrence → Scalar → σ → σ) (other : Slots (RSig scalarModel) σ)
    (path : List Zkc.Core.Frame) (s : σ) (table : Cube Scalar n) (claim : Scalar) (wrong : claim ≠ Cube.sum n table) :
    let verifier := (g.checked.standardVerifier standard).1.root
    let alphabet : Fin (Zkc.Vocabulary.Field.bls12381Fr.order - 1 + 1) → Scalar := ZMod.finEquiv _
    prEvent (observed (fun _ _ => true) <$> run
      (service (RoundService.withChallenge scalarModel ArithmeticModel.events alphabet advance other))
      (roleMeaning scalarModel _ verifier 1 path (TableVerifier.args scalarModel (Cube.flatten n table) claim)) s) ≤
      (n : ℝ≥0∞) / Zkc.Vocabulary.Field.bls12381Fr.order := by
  rw [← g.degreeOneTotal unitFee order]
  exact g.primeBound standard advance other path s table claim wrong

#print axioms coefficientVerifierBound
#print axioms Zkc.Formal.Written.CoefficientPolynomial.installed
#print axioms Zkc.Formal.Written.CoefficientPolynomial.agreements
#print axioms Zkc.Tools.Formal.InstalledRound.probabilityAt
#print axioms Zkc.Tools.Formal.SingleRoundGoal.degreeOneTotal
#print axioms Zkc.Tools.Formal.installRound
#print axioms Zkc.Tools.Formal.SingleRoundGoal.primeBound
#print axioms Zkc.Formal.Interactive.Sumcheck.ReductionRound.MappedReduction.soundFrom
