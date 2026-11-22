module

public import Mathlib.Algebra.Field.ZMod
public import VCVio.OracleComp.Constructions.SampleableType.Basic
public import Zkc.Vocabulary.Keys
import Mathlib.Tactic.Primality

@[expose] public section

/-!
The scalar field of the source vocabulary.

The order that the vocabulary gives its scalar field is a prime, so the integers modulo it are
a field with that many elements, which can be sampled uniformly. A statement over every field
with at least that many elements has this field as a witness of its hypotheses, and a charge
that a source writes with the order is what a uniform scalar of this field pays for.
-/

namespace ZkcFormal.Written

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

/-- The scalar field of the source vocabulary: the integers modulo its order. -/
abbrev ScalarField : Type := ZMod Zkc.Vocabulary.Field.bls12381Fr.order

namespace ScalarField

scoped instance : Fact (Nat.Prime Zkc.Vocabulary.Field.bls12381Fr.order) := ⟨scalarOrder_prime⟩

/-- The scalar field is sampled uniformly. -/
noncomputable scoped instance : SampleableType ScalarField := SampleableType.ofFintype ScalarField

/-- The scalar field has as many elements as its order. -/
theorem card : Fintype.card ScalarField = Zkc.Vocabulary.Field.bls12381Fr.order := ZMod.card _

end ScalarField

end ZkcFormal.Written
