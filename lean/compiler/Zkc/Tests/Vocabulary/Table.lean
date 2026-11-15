import Zkc.Vocabulary

/-!
The table of the standard vocabulary against what the reference says of it.

Every expected signature is written out here, from the types of the reference: never read from
the table. For each family, each row at a field or a group of each kind (a prime field, the
extension of degree four, a group with a generator, the target group), at all elements and at
those that are not zero where the row has both; the rows of collections of a size and of any
length where they have both, and at an element that is a sized collection; the hashes and the
pairing. Then each place where the reference gives a row no instance; the literals of each
nominal type; and the types at which the uniform law is a law and at which it is not (TY15).
-/

namespace Zkc.Vocabulary.TableTests

open Zkc.Core (RowSignature LawSignature)

/-! ## The types of the reference, written out -/

/-- `koala-bear`, the prime field of order `2^31 - 2^24 + 1`. -/
abbrev koalaBear : Ty := .nominal (.field .koalaBear)
/-- `nonzero<koala-bear>`. -/
abbrev koalaBearUnits : Ty := .nominal (.nonzero .koalaBear)
/-- `koala-bear.ext4`, its extension of degree four. -/
abbrev koalaBear4 : Ty := .nominal (.field .koalaBear4)
/-- `nonzero<koala-bear.ext4>`. -/
abbrev koalaBear4Units : Ty := .nominal (.nonzero .koalaBear4)
/-- `bls12-381.fr`, the scalar field of BLS12-381. -/
abbrev fr : Ty := .nominal (.field .bls12381Fr)
/-- `nonzero<bls12-381.fr>`. -/
abbrev frUnits : Ty := .nominal (.nonzero .bls12381Fr)
/-- `bls12-381.g1`, `bls12-381.g2`, `bls12-381.gt`. -/
abbrev g1 : Ty := .nominal (.group .g1)
abbrev g2 : Ty := .nominal (.group .g2)
abbrev gt : Ty := .nominal (.group .gt)
/-- `[byte]` and `[byte; n]`. -/
abbrev bytes : Ty := .seq (.fin 256) none
abbrev sizedBytes (n : Nat) : Ty := .seq (.fin 256) (some n)

/-- A pure signature. -/
def pureSignature (ins outs : List Ty) : Option (RowSignature TypeKey RowKey) :=
  some ⟨ins, outs, .pure⟩

/-! ## The field family, at a prime field and at the extension -/

-- `field.add`, `field.sub`: `F, F → F`
example : row (.field .add .koalaBear .all) =
    pureSignature [koalaBear, koalaBear] [koalaBear] := rfl
example : row (.field .add .koalaBear4 .all) =
    pureSignature [koalaBear4, koalaBear4] [koalaBear4] := rfl
example : row (.field .sub .koalaBear .all) =
    pureSignature [koalaBear, koalaBear] [koalaBear] := rfl
example : row (.field .sub .koalaBear4 .all) =
    pureSignature [koalaBear4, koalaBear4] [koalaBear4] := rfl
-- `field.mul`: `F, F → F`; `nonzero<F>, nonzero<F> → nonzero<F>`
example : row (.field .mul .koalaBear .all) =
    pureSignature [koalaBear, koalaBear] [koalaBear] := rfl
example : row (.field .mul .koalaBear .nonzero) =
    pureSignature [koalaBearUnits, koalaBearUnits] [koalaBearUnits] := rfl
example : row (.field .mul .koalaBear4 .all) =
    pureSignature [koalaBear4, koalaBear4] [koalaBear4] := rfl
example : row (.field .mul .koalaBear4 .nonzero) =
    pureSignature [koalaBear4Units, koalaBear4Units] [koalaBear4Units] := rfl
-- `field.neg`: `F → F`; `nonzero<F> → nonzero<F>`
example : row (.field .neg .koalaBear .all) = pureSignature [koalaBear] [koalaBear] := rfl
example : row (.field .neg .koalaBear .nonzero) =
    pureSignature [koalaBearUnits] [koalaBearUnits] := rfl
example : row (.field .neg .koalaBear4 .all) = pureSignature [koalaBear4] [koalaBear4] := rfl
example : row (.field .neg .koalaBear4 .nonzero) =
    pureSignature [koalaBear4Units] [koalaBear4Units] := rfl
-- `field.inverse`: `nonzero<F> → nonzero<F>`
example : row (.field .inverse .koalaBear .nonzero) =
    pureSignature [koalaBearUnits] [koalaBearUnits] := rfl
example : row (.field .inverse .koalaBear4 .nonzero) =
    pureSignature [koalaBear4Units] [koalaBear4Units] := rfl
-- `field.pow`: `F, nat → F`; `nonzero<F>, nat → nonzero<F>`
example : row (.field .pow .koalaBear .all) =
    pureSignature [koalaBear, .nat] [koalaBear] := rfl
example : row (.field .pow .koalaBear .nonzero) =
    pureSignature [koalaBearUnits, .nat] [koalaBearUnits] := rfl
example : row (.field .pow .koalaBear4 .all) =
    pureSignature [koalaBear4, .nat] [koalaBear4] := rfl
example : row (.field .pow .koalaBear4 .nonzero) =
    pureSignature [koalaBear4Units, .nat] [koalaBear4Units] := rfl
-- `field.equal`: `F, F → bool`
example : row (.field .equal .koalaBear .all) =
    pureSignature [koalaBear, koalaBear] [.bool] := rfl
example : row (.field .equal .koalaBear4 .all) =
    pureSignature [koalaBear4, koalaBear4] [.bool] := rfl
-- `field.is_nonzero`: `F → bool`, the domain row of `field.nonzero`
example : row (.field .isNonzero .koalaBear .all) = pureSignature [koalaBear] [.bool] := rfl
example : row (.field .isNonzero .koalaBear4 .all) = pureSignature [koalaBear4] [.bool] := rfl
-- `field.nonzero`: `F → nonzero<F>`, restricted by `field.is_nonzero`
example : row (.field .nonzero .koalaBear .all) =
    some ⟨[koalaBear], [koalaBearUnits], .restricted (.field .isNonzero .koalaBear .all)⟩ := rfl
example : row (.field .nonzero .koalaBear4 .all) =
    some ⟨[koalaBear4], [koalaBear4Units], .restricted (.field .isNonzero .koalaBear4 .all)⟩ :=
  rfl
-- `field.from_nonzero`: `nonzero<F> → F`
example : row (.field .fromNonzero .koalaBear .nonzero) =
    pureSignature [koalaBearUnits] [koalaBear] := rfl
example : row (.field .fromNonzero .koalaBear4 .nonzero) =
    pureSignature [koalaBear4Units] [koalaBear4] := rfl
-- `field.from_nat`: `nat → R`
example : row (.field .fromNat .koalaBear .all) = pureSignature [.nat] [koalaBear] := rfl
example : row (.field .fromNat .koalaBear4 .all) = pureSignature [.nat] [koalaBear4] := rfl
-- `field.to_nat`, at a prime field: `F → index<Order>`
example : row (.field .toNat .koalaBear .all) =
    pureSignature [koalaBear] [.fin 2130706433] := rfl
example : row (.field .toNat .bls12381Fr .all) = pureSignature [fr]
    [.fin 52435875175126190479447740508185965837690552500527637822603658699938581184513] := rfl
-- `field.components`, `field.from_components`: `F → [Prime; Dimension]` and back
example : row (.field .components .koalaBear .all) =
    pureSignature [koalaBear] [.seq koalaBear (some 1)] := rfl
example : row (.field .components .koalaBear4 .all) =
    pureSignature [koalaBear4] [.seq koalaBear (some 4)] := rfl
example : row (.field .fromComponents .koalaBear .all) =
    pureSignature [.seq koalaBear (some 1)] [koalaBear] := rfl
example : row (.field .fromComponents .koalaBear4 .all) =
    pureSignature [.seq koalaBear (some 4)] [koalaBear4] := rfl
-- `field.embed`, at the extension: `Base → E`; `nonzero<Base> → nonzero<E>`
example : row (.field .embed .koalaBear4 .all) = pureSignature [koalaBear] [koalaBear4] := rfl
example : row (.field .embed .koalaBear4 .nonzero) =
    pureSignature [koalaBearUnits] [koalaBear4Units] := rfl
-- `field.coefficients`, `field.from_coefficients`, at the extension: `E → [Base; Degree]` and back
example : row (.field .coefficients .koalaBear4 .all) =
    pureSignature [koalaBear4] [.seq koalaBear (some 4)] := rfl
example : row (.field .fromCoefficients .koalaBear4 .all) =
    pureSignature [.seq koalaBear (some 4)] [koalaBear4] := rfl
-- `field.root`: `index<TwoAdicity + 1> → nonzero<F>`
example : row (.field .root .koalaBear .all) = pureSignature [.fin 25] [koalaBearUnits] := rfl
example : row (.field .root .koalaBear4 .all) = pureSignature [.fin 27] [koalaBear4Units] := rfl
example : row (.field .root .bls12381Fr .all) = pureSignature [.fin 33] [frUnits] := rfl

/-! ## The group family, at a group with a generator, at the target group and at a field -/

-- `group.zero`: `→ G`
example : row (.group .zero (.group .g1)) = pureSignature [] [g1] := rfl
example : row (.group .zero (.group .gt)) = pureSignature [] [gt] := rfl
example : row (.group .zero (.field .koalaBear)) = pureSignature [] [koalaBear] := rfl
-- `group.add`, `group.sub`: `G, G → G`
example : row (.group .add (.group .g1)) = pureSignature [g1, g1] [g1] := rfl
example : row (.group .add (.group .gt)) = pureSignature [gt, gt] [gt] := rfl
example : row (.group .sub (.group .g1)) = pureSignature [g1, g1] [g1] := rfl
example : row (.group .sub (.group .gt)) = pureSignature [gt, gt] [gt] := rfl
-- `group.neg`: `G → G`
example : row (.group .neg (.group .g1)) = pureSignature [g1] [g1] := rfl
example : row (.group .neg (.group .gt)) = pureSignature [gt] [gt] := rfl
-- `group.scale`: `G, G::Scalar → G`; the scalar of each group is `bls12-381.fr`, a field's own
example : row (.group .scale (.group .g1)) = pureSignature [g1, fr] [g1] := rfl
example : row (.group .scale (.group .gt)) = pureSignature [gt, fr] [gt] := rfl
example : row (.group .scale (.field .koalaBear)) =
    pureSignature [koalaBear, koalaBear] [koalaBear] := rfl
-- `group.equal`: `G, G → bool`
example : row (.group .equal (.group .g1)) = pureSignature [g1, g1] [.bool] := rfl
example : row (.group .equal (.group .gt)) = pureSignature [gt, gt] [.bool] := rfl
-- `group.generator`, at a group of prime order: `→ G`
example : row (.group .generator (.group .g1)) = pureSignature [] [g1] := rfl
example : row (.group .generator (.group .g2)) = pureSignature [] [g2] := rfl

/-! ## The collection family -/

/-- A field, a group and a sized collection of field elements, as elements of collections. -/
abbrev ofField : Element := .atom (.field .koalaBear)
abbrev ofGroup : Element := .atom (.group .g1)
abbrev ofPairs : Element := .sized ofField 2

-- `seq.add`, `seq.sub`: `[E; n], [E; n] → [E; n]`
example : row (.seq .add ofField (some 3)) =
    pureSignature [.seq koalaBear (some 3), .seq koalaBear (some 3)] [.seq koalaBear (some 3)] :=
  rfl
example : row (.seq .sub ofGroup (some 3)) =
    pureSignature [.seq g1 (some 3), .seq g1 (some 3)] [.seq g1 (some 3)] := rfl
-- `seq.scale`: `[E; n], E::Scalar → [E; n]`
example : row (.seq .scale ofField (some 3)) =
    pureSignature [.seq koalaBear (some 3), koalaBear] [.seq koalaBear (some 3)] := rfl
example : row (.seq .scale ofGroup (some 3)) =
    pureSignature [.seq g1 (some 3), fr] [.seq g1 (some 3)] := rfl
-- `seq.sum`: `[E; n] → E` and `[E] → E`
example : row (.seq .sum ofField (some 3)) =
    pureSignature [.seq koalaBear (some 3)] [koalaBear] := rfl
example : row (.seq .sum ofField none) = pureSignature [.seq koalaBear none] [koalaBear] := rfl
example : row (.seq .sum ofGroup none) = pureSignature [.seq g1 none] [g1] := rfl
-- `seq.product`, at a ring: `[E; n] → E` and `[E] → E`
example : row (.seq .product ofField (some 3)) =
    pureSignature [.seq koalaBear (some 3)] [koalaBear] := rfl
example : row (.seq .product ofField none) =
    pureSignature [.seq koalaBear none] [koalaBear] := rfl
-- `seq.inner`: `[E; n], [E::Scalar; n] → E`
example : row (.seq .inner ofField (some 3)) =
    pureSignature [.seq koalaBear (some 3), .seq koalaBear (some 3)] [koalaBear] := rfl
example : row (.seq .inner ofGroup (some 3)) =
    pureSignature [.seq g1 (some 3), .seq fr (some 3)] [g1] := rfl
-- `seq.equal`: `[E; n], [E; n] → bool` and `[E], [E] → bool`
example : row (.seq .equal ofField (some 3)) =
    pureSignature [.seq koalaBear (some 3), .seq koalaBear (some 3)] [.bool] := rfl
example : row (.seq .equal ofGroup none) =
    pureSignature [.seq g1 none, .seq g1 none] [.bool] := rfl
-- at an element that is itself a sized collection: `[[F; 2]; n]`, with the scalar of `F`
example : row (.seq .sum ofPairs (some 3)) =
    pureSignature [.seq (.seq koalaBear (some 2)) (some 3)] [.seq koalaBear (some 2)] := rfl
example : row (.seq .scale ofPairs (some 3)) =
    pureSignature [.seq (.seq koalaBear (some 2)) (some 3), koalaBear]
      [.seq (.seq koalaBear (some 2)) (some 3)] := rfl

/-! ## The hashes and the pairing -/

-- `hash.sha256`, `hash.keccak256`: `[byte] → [byte; 32]`
example : row (.hash .sha256) = pureSignature [bytes] [sizedBytes 32] := rfl
example : row (.hash .keccak256) = pureSignature [bytes] [sizedBytes 32] := rfl
-- `hash.shake128`, `hash.shake256`: `[byte] → [byte; count]`
example : row (.hash (.shake128 64)) = pureSignature [bytes] [sizedBytes 64] := rfl
example : row (.hash (.shake256 17)) = pureSignature [bytes] [sizedBytes 17] := rfl
-- `pairing.pair`: `G1, G2 → Gt`
example : row .pair = pureSignature [g1, g2] [gt] := rfl

/-! ## Where the reference gives a row no instance -/

-- `field.to_nat` is a member of `PrimeField`; the coefficient rows and `embed` of
-- `ExtensionField`
example : row (.field .toNat .koalaBear4 .all) = none := rfl
example : row (.field .coefficients .koalaBear .all) = none := rfl
example : row (.field .fromCoefficients .bls12381Fr .all) = none := rfl
example : row (.field .embed .koalaBear .all) = none := rfl
-- `group.generator` is a member of `PrimeOrderGroup`: not the target group, not a field
example : row (.group .generator (.group .gt)) = none := rfl
example : row (.group .generator (.field .bls12381Fr)) = none := rfl
-- `+` on `nonzero` operands widens them: `field.add` has no instance at `nonzero<F>`
example : row (.field .add .koalaBear .nonzero) = none := rfl
example : row (.field .sub .koalaBear .nonzero) = none := rfl
-- `field.inverse` takes a `nonzero<F>` only
example : row (.field .inverse .koalaBear .all) = none := rfl
-- `seq.product` needs a ring: not a group, not a sized collection
example : row (.seq .product ofGroup (some 3)) = none := rfl
example : row (.seq .product ofPairs (some 3)) = none := rfl
-- element-wise rows and `inner` apply to sized collections only
example : row (.seq .add ofField none) = none := rfl
example : row (.seq .sub ofField none) = none := rfl
example : row (.seq .scale ofGroup none) = none := rfl
example : row (.seq .inner ofField none) = none := rfl

/-! ## Literals -/

-- of a field: the numbers below its characteristic, also for the extension
example : literal (.field .koalaBear) 2130706432 = true := by decide +kernel
example : literal (.field .koalaBear) 2130706433 = false := by decide +kernel
example : literal (.field .koalaBear4) 2130706432 = true := by decide +kernel
example : literal (.field .koalaBear4) 2130706433 = false := by decide +kernel
example : literal (.field .bls12381Fr)
    52435875175126190479447740508185965837690552500527637822603658699938581184512 = true := by
  decide +kernel
example : literal (.field .bls12381Fr)
    52435875175126190479447740508185965837690552500527637822603658699938581184513 = false := by
  decide +kernel
-- of the elements that are not zero: not 0
example : literal (.nonzero .koalaBear) 0 = false := by decide +kernel
example : literal (.nonzero .koalaBear) 1 = true := by decide +kernel
example : literal (.nonzero .koalaBear) 2130706433 = false := by decide +kernel
-- of a group: none; its zero is the row `group.zero`
example : literal (.group .g1) 0 = false := by decide +kernel
example : literal (.group .gt) 1 = false := by decide +kernel

/-! ## The uniform law (TY15) -/

/-- The signature of the uniform law on a type. -/
def uniformOn (τ : Ty) : Option (LawSignature TypeKey) := some ⟨[], τ⟩

-- a law: `bool`; `index<n>` with `0 < n`; a field; `nonzero<F>`; a group; a tuple of laws;
-- `[L; n]` with `L` a law, or `n == 0`
example : law (.uniform .bool) = uniformOn .bool := rfl
example : law (.uniform (.fin 7)) = uniformOn (.fin 7) := rfl
example : law (.uniform koalaBear4) = uniformOn koalaBear4 := rfl
example : law (.uniform frUnits) = uniformOn frUnits := rfl
example : law (.uniform g1) = uniformOn g1 := rfl
example : law (.uniform (.tuple (.cons koalaBear (.cons .bool .nil)))) =
    uniformOn (.tuple (.cons koalaBear (.cons .bool .nil))) := rfl
example : law (.uniform (.seq (.fin 7) (some 3))) = uniformOn (.seq (.fin 7) (some 3)) := rfl
example : law (.uniform (.seq g1 (some 2))) = uniformOn (.seq g1 (some 2)) := rfl
example : law (.uniform (.seq (.fin 0) (some 0))) = uniformOn (.seq (.fin 0) (some 0)) := rfl
-- not a law: `nat`, `[T]`, `index<0>`, records, variants; nor what holds one of them
example : law (.uniform .nat) = none := rfl
example : law (.uniform (.seq koalaBear none)) = none := rfl
example : law (.uniform (.fin 0)) = none := rfl
example : law (.uniform (.record ⟨1⟩ false (.cons .bool .nil))) = none := rfl
example : law (.uniform (.variant ⟨2⟩ (.cons .bool (.cons .bool .nil)))) = none := rfl
example : law (.uniform (.tuple (.cons .nat .nil))) = none := rfl
example : law (.uniform (.seq (.fin 0) (some 2))) = none := rfl

end Zkc.Vocabulary.TableTests
