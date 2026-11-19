module

public import Zkc.Formal.Written.ReductionModel
public import Zkc.Formal.Written.RoundCharge
public import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.Primality

@[expose] public section
namespace Zkc.Formal.Written.RoundCharge
open Core Interactive Sumcheck FiniteService ProbabilisticProcess OracleComp
open scoped ArithmeticModel ENNReal

set_option maxHeartbeats 2000000 in
/-- Primality of the scalar order used by the source vocabulary. Mathlib verifies the
Lucas witnesses and the full factorization recursively in the kernel. -/
theorem scalarOrder_prime : Nat.Prime Zkc.Vocabulary.Field.bls12381Fr.order := by
  change Nat.Prime 52435875175126190479447740508185965837690552500527637822603658699938581184513
  primality (cert := .witnesses [
    .lucas { root := 7, primeFactors := [2, 3, 11, 19, 10177, 125527, 859267, 906349, 2508409, 2529403, 52437899, 254760293] },
    .lucas { root := 7, primeFactors := [2, 3, 53] },
    .lucas { root := 5, primeFactors := [2, 3, 20921] },
    .lucas { root := 3, primeFactors := [2, 5, 523] },
    .lucas { root := 2, primeFactors := [2, 3, 47737] },
    .lucas { root := 5, primeFactors := [2, 3, 13, 17] },
    .lucas { root := 2, primeFactors := [2, 3, 47, 1607] },
    .lucas { root := 5, primeFactors := [2, 11, 73] },
    .lucas { root := 11, primeFactors := [2, 3, 7, 79] },
    .lucas { root := 2, primeFactors := [2, 3, 23, 18329] },
    .lucas { root := 3, primeFactors := [2, 29, 79] },
    .lucas { root := 2, primeFactors := [2, 43, 609743] },
    .lucas { root := 5, primeFactors := [2, 7, 97, 449] },
    .lucas { root := 2, primeFactors := [2, 63690073] },
    .lucas { root := 7, primeFactors := [2, 3, 2653753] },
    .lucas { root := 5, primeFactors := [2, 3, 110573] },
    .lucas { root := 3, primeFactors := [2, 7, 11, 359] }])

scoped instance : Fact (Nat.Prime Zkc.Vocabulary.Field.bls12381Fr.order) := ⟨scalarOrder_prime⟩

/-- In the standard prime-field interpretation, the charge denominator is the field order
and VCVio samples every element. The source theorem needs only primality, the false public
claim and the checked binding. All arithmetic and table-evaluation laws are discharged. -/
theorem primeSumcheck {width n : Nat} [Fact (Nat.Prime (width+1))]
    {p : Core.Typed Standard} {root red eval : Key}
    (cert : TableVerifier.Certified ArithmeticModel.scalarRows ArithmeticModel.vectors p root red eval n ArithmeticModel.events)
    {σ : Type} (advance : Occurrence → ZMod (width+1) → σ → σ)
    (other : Slots (RSig (ArithmeticModel.model (ZMod (width+1)) (ZMod (width+1)))) σ)
    (charge : Frontend.Written.DrawCharge) (binding : Matches charge cert.linked 1 (width+1))
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
    charge binding path s x claim wrong

end Zkc.Formal.Written.RoundCharge
