module

public import ZkcFormal.Written.ReductionModel
public import ZkcFormal.Written.RoundCharge
public import ZkcFormal.Written.PolynomialBounds
public import ZkcFormal.Written.ScalarField

@[expose] public section
namespace ZkcFormal.Written.RoundCharge
open Zkc.Core Interactive Sumcheck FiniteService ProbabilisticProcess OracleComp
open scoped ArithmeticModel ENNReal

scoped instance : Fact (Nat.Prime Zkc.Vocabulary.Field.bls12381Fr.order) := ⟨scalarOrder_prime⟩

/-- In the standard prime-field interpretation, the charge denominator is the field order
and VCVio samples every element. The source theorem needs only primality, the false public
claim and the checked binding. All arithmetic and table-evaluation laws are discharged. -/
theorem primeSumcheck {width n : Nat} [Fact (Nat.Prime (width+1))]
    {p : Zkc.Core.Typed Standard} {root red eval : Key}
    (cert : TableVerifier.Certified ArithmeticModel.scalarRows ArithmeticModel.vectors p root red eval n ArithmeticModel.events)
    {σ : Type} (advance : Occurrence → ZMod (width+1) → σ → σ)
    (other : Slots (RSig (ArithmeticModel.model (ZMod (width+1)) (ZMod (width+1)))) σ)
    (charge : Zkc.Frontend.Written.DrawCharge) (binding : Matches charge cert.linked 1 (width+1))
    (path : List Frame) (s : σ) (x : Cube (ZMod (width+1)) n) (claim : ZMod (width+1))
    (wrong : claim ≠ Cube.sum n x) :
    let M := ArithmeticModel.model (ZMod (width+1)) (ZMod (width+1))
    prEvent (observed (fun _ _ => true) <$> run
      (service (RoundService.withChallenge M ArithmeticModel.events (ZMod.finEquiv (width+1)) advance other))
      (roleMeaning M p cert.root 1 path (TableVerifier.args M (Cube.flatten n x) claim)) s) ≤ total charge := by
  let F := ZMod (width+1)
  let math := ArithmeticModel.reductionArithmetic F F
  exact sumcheck cert (ArithmeticModel.model F F) ((math 1).scalar (by decide))
    (math n).vector (math n).equal _ (List.nodup_ofFn.mpr (ZMod.finEquiv _).injective) advance other
    charge binding path s x claim wrong (PolynomialBounds.pairs (F := F))

end ZkcFormal.Written.RoundCharge
