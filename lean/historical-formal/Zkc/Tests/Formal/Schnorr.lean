import Zkc.Tests.Core.VocabularyScheme
import Zkc.Formal.Bls12381.Relation

/-! Completeness of the scheme `Proof = Schnorr<G1>`, from the source instance to what runs.

The subject is the package that the frontend emits for the scheme `Proof = Schnorr<G1>` of the
worked program `schnorr_example` (`Zkc.Tests.Core.VocabularyScheme.Schnorr`, which binds the
package and evaluates what the construction makes of it).

1. **The binding** (`binding`). Which nominal type of the package is the group and which its
   scalars, and which row is which operation, read from the names of the package's rows by
   `Bls12381.bindingOf` and evaluated by the kernel. Nothing of it is written here.
2. **The mathematics** (`equation`, `interactive_complete`). In the model of any arithmetic,
   for every base, every scalar and the point that is the base times the scalar, every run of
   the prover and the verifier together returns. It uses two laws of the points and the
   commutativity of the scalars.
3. **What runs** (`interactive_complete_runs`, `complete`). The rows that the program uses fit
   the arithmetic of BLS12-381 and the program passes the test of the relation theorem; both
   are evaluated by the kernel. So the interactive entry is complete in the model that runs,
   and so are the constructed prover and verifier: on a base that is a point of the group, a
   scalar, and the point that the model's row `group.scale` gives of them, the prover's program
   returns a proof and the verifier's program returns on it.

The hypotheses that remain are named: `Vocabulary.PointCompression`,
`Vocabulary.GroupClosedUnderMultiples` and `Bls12381.CurveLaws`, facts of the arithmetic of
the curve. Their executable checks are at the end, with the axioms of each theorem.
-/

set_option autoImplicit false

namespace Zkc.Formal.Schnorr

open Zkc.Source Zkc.Core Zkc.Core.Concrete
open VocabularyScheme.Schnorr (raw typed model operations declaration entry both header inputsOf
  point scalar verdict grouped_shape commitment)

/-! ## The binding of the package -/

typed_literal binding := Bls12381.bindingOf raw

kernel_refl bound : Bls12381.bindingOf raw equals binding

/-- Completeness of the interactive protocol in a model: for every base and every scalar, with
the point that the model's row `group.scale` gives of them, every run of the prover and the
verifier together returns. -/
def InteractiveComplete (model : Model) : Prop :=
  ∀ (base : model.Value point) (witness : model.Value scalar),
    EveryRun (fun _ => True)
      ((typed.program.protocolTable model Identities.written).get entry [] both
        (inputsOf model base base (commitment model base witness) (commitment model base witness)
          witness))

/-! ## The mathematics -/

section Mathematics

variable (A : Arithmetic)

/-- The verifier's equation: the base times the response is the commitment plus the point times
the challenge. -/
theorem equation (base : A.Point) (witness nonce challenge : A.Scalar) :
    verdict (provider A binding) base base (A.scale base witness) witness nonce challenge = true := by
  show A.same (A.scale base (nonce + challenge * witness))
    (A.combine (A.scale base nonce) (A.scale (A.scale base witness) challenge)) = true
  rw [A.scale_add, A.scale_scale, Lean.Grind.CommSemiring.mul_comm witness challenge]
  exact A.same_self _

/-- Every run of a guard on a flag that holds returns. -/
theorem guard_returns (model : Model) (flag : Bool) (holds : flag = true) :
    EveryRun (model := model) (fun (_ : Values (SideValue model both) header.outputs) => True)
      (((cond flag (.done .nil) (.halt .reject) :
          PIR.Process (Effects model) (Values model.Value [])).bind fun _ =>
        (.done .nil : PIR.Process (Effects model) (Values (SideValue model both) []))).bind
        fun _ => .done .nil) := by
  subst holds
  trivial

/-- Completeness of the interactive protocol in the model of any arithmetic. -/
theorem interactive_complete : InteractiveComplete (provider A binding) := by
  intro base witness
  rw [grouped_shape (provider A binding) base base (commitment (provider A binding) base witness)
    (commitment (provider A binding) base witness) witness]
  intro nonce challenge
  exact guard_returns (provider A binding) _ (equation A base witness nonce challenge)

end Mathematics

/-! ## What runs -/

section Runs

open Bls12381

-- The nominal types 0 and 1 of the package are the group and its scalars; the row
-- `group.scale`, which gives the point of a statement, fits; and every operation of the
-- program is one that the relation theorem covers, on rows that fit.
kernel_refl point_kind : (Bls12381.bindingOf raw).kind 0 equals Kind.point

kernel_refl scalar_kind : (Bls12381.bindingOf raw).kind 1 equals Kind.scalar

kernel_refl scale_fits : (Bls12381.fitted raw operations).contains 1 equals true

kernel_refl relatable : typed.program.relatable (Bls12381.fitted raw operations) equals true

variable (closed : Vocabulary.GroupClosedUnderMultiples) (laws : CurveLaws)

include closed laws in
/-- Completeness of the interactive protocol in the model that runs. The base is a datum that
reads as a point of the group; the scalar is any datum; the point is what the model's row
`group.scale` gives of the two. Then every run of the prover and the verifier together
returns, whatever the model answers to the sample and to the draw. -/
theorem interactive_complete_runs (base witness : Datum)
    (baseOfGroup : Vocabulary.inGroup base.toPoint = true) :
    GroupedComplete
      ((typed.program.protocolTable model Identities.written).get entry [] both
        (inputsOf model base base (commitment model base witness) (commitment model base witness)
          witness))
      (fun _ => True) := by
  let abstract : Model := provider (arithmetic closed laws) (bindingOf raw)
  let abstractBase : abstract.Value point :=
    ((bindingOf raw).kind 0).ofPoint (arithmetic closed laws) ⟨base.toPoint, baseOfGroup⟩
  let abstractWitness : abstract.Value scalar :=
    ((bindingOf raw).kind 1).ofScalar (arithmetic closed laws)
      ⟨witness.toNat % order, Nat.mod_lt _ (by decide)⟩
  have baseRelated : Related (relation closed laws raw) point abstractBase base :=
    related_nominal.mpr (related_ofPoint point_kind rfl)
  have witnessRelated : Related (relation closed laws raw) scalar abstractWitness witness :=
    related_nominal.mpr (related_ofScalar scalar_kind rfl)
  have respects : RowsRespected (relation closed laws raw) operations (fitted raw operations) :=
    respected closed laws raw operations
  have pointRelated : Related (relation closed laws raw) point
      (commitment abstract abstractBase abstractWitness) (commitment model base witness) :=
    respects (⟨1, kernel_rfl%⟩ : Var operations ⟨[point, scalar], [point], .pure⟩)
      (List.contains_iff_mem.mp scale_fits) rfl _ _
      (ValuesRelated.cons (related := Related (relation closed laws raw)) baseRelated
        (ValuesRelated.cons (related := Related (relation closed laws raw)) witnessRelated
          ValuesRelated.nil)) _ Var.here
  have inputsRelated : ValuesRelated (SideRelated (relation closed laws raw) both)
      (inputsOf abstract abstractBase abstractBase (commitment abstract abstractBase abstractWitness)
        (commitment abstract abstractBase abstractWitness) abstractWitness)
      (inputsOf model base base (commitment model base witness) (commitment model base witness)
        witness) :=
    ValuesRelated.cons (related := SideRelated (relation closed laws raw) both) baseRelated
      (ValuesRelated.cons (related := SideRelated (relation closed laws raw) both) baseRelated
        (ValuesRelated.cons (related := SideRelated (relation closed laws raw) both) pointRelated
          (ValuesRelated.cons (related := SideRelated (relation closed laws raw) both) pointRelated
            (ValuesRelated.cons (related := SideRelated (relation closed laws raw) both)
              witnessRelated ValuesRelated.nil))))
  have related := (program_related respects typed.program relatable Identities.written).2 entry []
    both _ _ inputsRelated
  have mathematics : InteractiveComplete abstract :=
    Eq.mpr (congrArg (fun binding => InteractiveComplete (provider (arithmetic closed laws) binding))
      bound) (interactive_complete (arithmetic closed laws))
  exact groupedComplete_iff_everyRun.mpr
    (everyRun_related (fun _ _ _ _ => True.intro) related (mathematics abstractBase abstractWitness))

include closed laws in
open VocabularyScheme.Schnorr (prover verifier acceptedDerived complete_honest) in
/-- Completeness of the scheme `Proof = Schnorr<G1>` in the model that runs, from the source
instance. For every base that reads as a point of the group and every scalar, with the point
that the model's row `group.scale` gives of them: for every sampler, the constructed prover's
program returns a proof, and the constructed verifier's program returns on that proof.

The hypotheses are three facts of the arithmetic of the curve, each named: the compressed
encoding of a point is read back (`PointCompression`), the multiples of a point of the group
are of the group (`GroupClosedUnderMultiples`), and the points of the group are a module over
the scalars (`CurveLaws`). -/
theorem complete (compression : Vocabulary.PointCompression) (base witness : Datum)
    (baseOfGroup : Vocabulary.inGroup base.toPoint = true) :
    DerivedComplete
      (prover (inputsOf model base base (commitment model base witness)
        (commitment model base witness) witness))
      (verifier (inputsOf model base base (commitment model base witness)
        (commitment model base witness) witness))
      (acceptedDerived fun _ => True) :=
  complete_honest compression closed base (commitment model base witness) witness baseOfGroup
    (fun _ => True) (interactive_complete_runs closed laws base witness baseOfGroup)

end Runs

/-! ## Checks -/

#print axioms program_related
#print axioms everyRun_related
#print axioms Bls12381.respected
#print axioms equation
#print axioms interactive_complete
#print axioms interactive_complete_runs
#print axioms complete

/-- The laws of the curve at multiples of the generator, with scalars on both sides of the
order so that the reduction modulo the order is exercised: the executable check of
`Bls12381.CurveLaws`. It is a check at points, not a proof of the hypothesis. -/
def curveLawsHold : Bool :=
  let order := Bls12381.order
  let scalars := [0, 1, 2, 7, order - 3, order - 1, order, order + 5]
  [1, 7, order - 2].all fun base =>
    let point := scalePoint generator base
    Vocabulary.inGroup point && scalars.all fun first => scalars.all fun second =>
      Bls12381.CurveLaws.holdsAt point first second

#eval show IO Unit from do
  unless curveLawsHold do
    throw (IO.userError "the laws of the curve fail at a multiple of the generator")

kernel_refl generator_inGroup : Vocabulary.inGroup (Datum.ofPoint generator).toPoint equals true

open VocabularyScheme.Schnorr (prover verifier acceptedDerived) in
/-- The theorem at the generator and the scalar seven: under the three hypotheses about the
curve, the scheme is complete on that statement. -/
theorem complete_at_seven (compression : Vocabulary.PointCompression)
    (closed : Vocabulary.GroupClosedUnderMultiples) (laws : Bls12381.CurveLaws) :
    DerivedComplete
      (prover (inputsOf model (Datum.ofPoint generator) (Datum.ofPoint generator)
        (commitment model (Datum.ofPoint generator) (Datum.number 7))
        (commitment model (Datum.ofPoint generator) (Datum.number 7)) (Datum.number 7)))
      (verifier (inputsOf model (Datum.ofPoint generator) (Datum.ofPoint generator)
        (commitment model (Datum.ofPoint generator) (Datum.number 7))
        (commitment model (Datum.ofPoint generator) (Datum.number 7)) (Datum.number 7)))
      (acceptedDerived fun _ => True) :=
  complete closed laws compression (Datum.ofPoint generator) (Datum.number 7) generator_inGroup

#print axioms complete_at_seven

end Zkc.Formal.Schnorr
