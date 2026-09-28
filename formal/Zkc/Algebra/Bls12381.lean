import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Field.ZMod

/-! Mathematical carriers for the exercised BLS12-381 scalar/group profile.

The constants and curve equation match the installed ark-bls12-381 0.6.0
provider. Scalars are residues modulo the actual scalar modulus, and G1 is
the scalar-order torsion subgroup of the nonsingular affine curve points.
Base-field primality is an explicit premise of the group construction. No
native arithmetic, subgroup decoder, fixed generator, sampler distribution,
or byte-codec correctness follows from these definitions.
-/

set_option autoImplicit false
namespace Zkc.Algebra.Bls12381

def scalarModulus : Nat :=
  52435875175126190479447740508185965837690552500527637822603658699938581184513

def baseModulus : Nat :=
  4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787

abbrev Scalar := ZMod scalarModulus
abbrev Challenge := { value : Scalar // value ≠ 0 }

/-- Required by the total group operations. The scalar carrier is fixed;
native realization and generator correspondence remain separate premises. -/
structure GroupModel where
  Carrier : Type
  group : AddCommGroup Carrier
  scalarAction : Module Scalar Carrier
  equality : DecidableEq Carrier
  generator : Carrier

attribute [instance] GroupModel.group GroupModel.scalarAction GroupModel.equality

/-- This law uses no scalar primality or discrete-log assumption. -/
theorem GroupModel.honestEquation (model : GroupModel)
    (witness nonce : Scalar) (challenge : Challenge) (generator : model.Carrier) :
    (nonce + challenge.val * witness) • generator =
      nonce • generator + challenge.val • (witness • generator) := by
  rw [add_smul, mul_smul]

def curve : WeierstrassCurve.Affine (ZMod baseModulus) := ⟨0, 0, 0, 0, 4⟩

/-- State the torsion equation under its algebraic premise. The bare carrier
is available to formation without evaluating group operations or assuming
primality; with that premise it is exactly the scalar-order torsion set. -/
def torsion : Set curve.Point :=
  { point | ∀ (_ : Fact baseModulus.Prime), scalarModulus • point = 0 }

abbrev G1Carrier : Type := torsion

section Group
variable [Fact baseModulus.Prime]

noncomputable def subgroup : AddSubgroup curve.Point where
  carrier := torsion
  zero_mem' := by intro _; simp
  add_mem' := by
    intro a b ha hb premise
    simp only [nsmul_add, ha premise, hb premise, add_zero]
  neg_mem' := by intro a ha premise; simpa using congrArg Neg.neg (ha premise)

noncomputable abbrev G1 := subgroup

noncomputable instance : Module Scalar G1 :=
  AddCommGroup.zmodModule fun point => Subtype.ext (point.property inferInstance)

theorem subgroup_carrier : (G1 : Type) = G1Carrier := rfl

theorem torsion_iff (point : curve.Point) :
    point ∈ torsion ↔ scalarModulus • point = 0 :=
  ⟨fun member => member inferInstance, fun member _ => member⟩

/-- A concrete model under the named base-primality premise. Supplying a
generator value includes its curve and torsion membership proofs. -/
noncomputable def curveModel (generator : G1) : GroupModel where
  Carrier := G1Carrier
  group := inferInstanceAs (AddCommGroup G1)
  scalarAction := inferInstanceAs (Module Scalar G1)
  equality := inferInstanceAs (DecidableEq G1)
  generator := generator

theorem curveModel_carrier (generator : G1) : (curveModel generator).Carrier = G1Carrier := rfl

/-- The verifier equation uses the actual scalar modulus and group action.
No group-order lower bound or discrete-log assumption is needed for honesty. -/
theorem honestEquation (witness nonce : Scalar) (challenge : Challenge) (generator : G1) :
    (nonce + challenge.val * witness) • generator =
      nonce • generator + challenge.val • (witness • generator) := by
  exact (curveModel generator).honestEquation witness nonce challenge generator

end Group
end Zkc.Algebra.Bls12381
