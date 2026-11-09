module

public import Zkc.Verification.Installations.Sumcheck.Source.HelperBridge
public import Zkc.Protocol.Library.Sumcheck.Source.Representation
public import Zkc.IR.Source.Structured.MultilinearReferenceViews
import Zkc.IR.Source.Structured.CollectionReference
public meta import Zkc.Tools.IR.StructuredSource.HelperPresentation

@[expose] public section

/-! A complete mathematical presentation of the actual sums helper. Only the
low endpoint is retained by the view. Conservation reconstructs the high
endpoint from the input; the view is not invertible on arbitrary raw replies. -/
set_option autoImplicit false
noncomputable section
namespace ZkcExamples.Structured.SumcheckMathematicalHelpers
open Zkc.Source Zkc.Source.Structured PrimitiveLibrary MapFirstLaws
open SumcheckHelperBodies SumcheckHelperLaws
open Zkc.Protocols.Sumcheck.Multilinear (endpoints endpoints_high)

helper_presentation Sums inputs [entries, dimension, columns] outputs [low, high] := sumsBody

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

/-- The unchanged raw guards, including their order, with a scalar result. -/
def reference (entries : List F) (dimension : Nat) (_columns : Nat) : PIR.Outcome F :=
  if dimension < indexLimit then
    if 0 < dimension then
      if 0 < entries.length ∧ entries.length % 2 = 0 then
        .returned (endpoints entries).1
      else .stopped .refused
    else .stopped .reject
  else .stopped .refused

def pack (entries : List F) (_dimension _columns : Nat) (low : F) :
    Sums.Output (ringModel F G) := ⟨low, entries.sum - low⟩

def condition (table : Meanings F G) (_entries : List F) (_dimension _columns : Nat) : Prop :=
  LessAllLaw table ∧ HalvesBodyLaw table

theorem sums_premises (table : Meanings F G) (entries : List F)
    (dimension columns : Nat) (laws : condition table entries dimension columns) :
    (ReferenceLibrary.Multilinear.sums (ringModel F G) "bls12-381.fr"
      MultilinearSourceBindings.common).Requires table (inputs entries dimension columns) := by
  change invoke table MapFirstBodies.halvesHelper (inputs entries dimension columns) =
    primitiveOutcome (ReferenceLibrary.Multilinear.halvesOutcome
      (ringModel F G) "bls12-381.fr" entries dimension)
  rw [laws.2, halves_generic_body_all table laws.1]
  unfold ReferenceLibrary.Multilinear.halvesOutcome
  split_ifs <;> rfl

theorem reachable (table : Meanings F G) (entries : List F) (dimension columns : Nat)
    (laws : condition table entries dimension columns) :
    PIR.Yields (fun result => pack entries dimension columns result.low = result)
      (Sums.run (ringModel F G) table entries dimension columns) := by
  rw [← Sums.run_eq]
  change PIR.Yields _ ((sumsBody.denote (meaning F G table)
    (inputs entries dimension columns).get).bind _)
  have execution := (ReferenceLibrary.Multilinear.sums (ringModel F G) "bls12-381.fr"
    MultilinearSourceBindings.common).valid table (inputs entries dimension columns)
      (sums_premises table entries dimension columns laws)
  change sumsBody.denote (meaning F G table) (inputs entries dimension columns).get = _ at execution
  rw [execution]
  dsimp only [ReferenceLibrary.Multilinear.sums, ReferenceLibrary.Multilinear.halves,
    ReferenceLibrary.Multilinear.halvesOutcome, inputs, Values.get]
  simp only [Values.get_head, Values.get_tail]
  by_cases bound : dimension < indexLimit <;> by_cases positive : 0 < dimension <;>
    by_cases valid : 0 < entries.length ∧ entries.length % 2 = 0 <;>
    simp only [bound, positive, valid, ite_true, ite_false, primitiveOutcome,
      PIR.Process.bind, PIR.Yields]
  change pack entries dimension columns (endpoints entries).1 =
    (⟨(endpoints entries).1, (endpoints entries).2⟩ : Sums.Output (ringModel F G))
  simp only [pack, endpoints_high]

theorem projected (table : Meanings F G) (entries : List F) (dimension columns : Nat)
    (laws : condition table entries dimension columns) :
    (Sums.run (ringModel F G) table entries dimension columns).bind
        (fun result => .done result.low) = primitiveOutcome (reference entries dimension columns) := by
  rw [← Sums.run_eq]
  change ((sumsBody.denote (meaning F G table)
    (inputs entries dimension columns).get).bind _).bind _ = _
  have execution := (ReferenceLibrary.Multilinear.sums (ringModel F G) "bls12-381.fr"
    MultilinearSourceBindings.common).valid table (inputs entries dimension columns)
      (sums_premises table entries dimension columns laws)
  change sumsBody.denote (meaning F G table) (inputs entries dimension columns).get = _ at execution
  rw [execution]
  dsimp only [ReferenceLibrary.Multilinear.sums, ReferenceLibrary.Multilinear.halves,
    ReferenceLibrary.Multilinear.halvesOutcome, inputs, Values.get]
  unfold reference
  simp only [Values.get_head, Values.get_tail]
  by_cases bound : dimension < indexLimit <;> by_cases positive : 0 < dimension <;>
    by_cases valid : 0 < entries.length ∧ entries.length % 2 = 0 <;>
    simp only [bound, positive, valid, ite_true, ite_false] <;> rfl

/-- Checked reachable reconstruction, with only genuine dependency laws as Requires. -/
def sumsLaw : ReferenceLaw (ringModel F G) sumsHelper.inputs sumsHelper.outputs :=
  Sums.lawOfView (ringModel F G) (fun _ _ _ result => result.low) pack reference condition
    reachable projected

/-- Reconstructed outputs are the original endpoints, also on unshaped raw inputs. -/
theorem reference_eq (entries : List F) (dimension columns : Nat) :
    primitiveOutcome (I := closedInterface)
      ((sumsLaw (F := F) (G := G)).reference (inputs entries dimension columns)) =
      if dimension < indexLimit then
        if 0 < dimension then
          if 0 < entries.length ∧ entries.length % 2 = 0 then
            .done (messageResult (endpoints entries).1 (endpoints entries).2)
          else .halt .refused
        else .halt .reject
      else .halt .refused := by
  change primitiveOutcome (Sums.encodeOutcome (ringModel F G)
    (match reference entries dimension columns with
      | .returned low => .returned (pack entries dimension columns low)
      | .stopped reason => .stopped reason)) = _
  unfold reference
  split_ifs <;> simp only [Sums.encodeOutcome, primitiveOutcome, pack, endpoints_high]
  rfl

/-! First has a genuinely smaller carrier too: the remaining dimension and
columns are determined by the inputs. Named rows cover the complete ABI;
the collection bindings remain a parameter rather than a hard-coded choice. -/
named_values FirstInputs [entries, dimension, columns, challenge] := MapFirstBodies.firstHelper.inputs
named_values FirstOutputs [entries, dimension, columns] := MapFirstBodies.firstHelper.outputs

def firstCondition (bindings : MultilinearCollectBodies.Bindings) (table : Meanings F G)
    (arguments : Values (assignment F G) MapFirstBodies.firstHelper.inputs) : Prop :=
  let input := FirstInputs.unpack arguments
  HalvesLaw table ∧ MapLaw table bindings ∧
    HasShape input.entries input.dimension input.columns ∧ input.entries.length < indexLimit

def nominalBindings (bindings : MultilinearCollectBodies.Bindings) :
    MultilinearBodies.Bindings :=
  { MultilinearSourceBindings.common with
    collection := bindings.collection, collectionDomain := bindings.domain,
    callback := bindings.callback, interpolation := bindings.computation }

theorem first_premises (bindings : MultilinearCollectBodies.Bindings)
    (table : Meanings F G) (arguments : Values (assignment F G) MapFirstBodies.firstHelper.inputs)
    (laws : firstCondition bindings table arguments) :
    (ReferenceLibrary.Multilinear.first (ringModel F G) "bls12-381.fr"
      (nominalBindings bindings)).Requires table arguments := by
  obtain ⟨input, rfl⟩ := FirstInputs.pack_surjective arguments
  change HalvesLaw table ∧ MapLaw table bindings ∧
    HasShape input.entries input.dimension input.columns ∧ input.entries.length < indexLimit at laws
  obtain ⟨halves, map, shape, bound⟩ := laws
  have dimensionBound : input.dimension < indexLimit :=
    Nat.lt_trans shape.2.1 (by decide +kernel)
  refine ⟨bound, dimensionBound, fun positive ↦ shape.split_valid positive, ?_, ?_⟩
  · have split := halves input.entries input.dimension input.columns dimensionBound
    change invoke table MapFirstBodies.halvesHelper
      (inputs input.entries input.dimension input.columns) = _
    rw [split]
    change _ = primitiveOutcome (ReferenceLibrary.Multilinear.halvesOutcome
      (ringModel F G) "bls12-381.fr" input.entries input.dimension)
    dsimp only [ReferenceLibrary.Multilinear.halvesOutcome]
    simp only [dimensionBound, ite_true]
    split_ifs <;> rfl
  · intro low high r small same
    exact map low high r same small

/-- Restriction reconstructs retained fields on every admitted return and
preserves zero-dimension rejection. Shape and bounds remain explicit. -/
def firstLaw (bindings : MultilinearCollectBodies.Bindings) :
    ReferenceLaw (ringModel F G) MapFirstBodies.firstHelper.inputs MapFirstBodies.firstHelper.outputs where
  body := MultilinearCollectBodies.firstBody bindings
  Requires := firstCondition bindings
  reference := (ReferenceLibrary.Multilinear.firstView (ringModel F G) "bls12-381.fr"
    (nominalBindings bindings)).reference
  valid table arguments laws :=
    (ReferenceLibrary.Multilinear.firstView (ringModel F G) "bls12-381.fr"
      (nominalBindings bindings)).valid table arguments (first_premises bindings table arguments laws)

theorem first_reference_eq (bindings : MultilinearCollectBodies.Bindings)
    (entries : List F) (dimension columns : Nat) (challenge : F) :
    primitiveOutcome (I := closedInterface)
      ((firstLaw (F := F) (G := G) bindings).reference
        (firstInputs entries dimension columns challenge)) =
      if 0 < dimension then
        .done (inputs (Zkc.Polynomial.Multilinear.restrictValues entries challenge)
          (dimension - 1) columns)
      else .halt .reject := by
  change primitiveOutcome ((ReferenceLibrary.Multilinear.firstView (ringModel F G) "bls12-381.fr"
    (nominalBindings bindings)).reference (firstInputs entries dimension columns challenge)) = _
  rw [ReferenceLibrary.Multilinear.firstView_reference]
  dsimp only [ReferenceLibrary.Multilinear.firstOutcome, firstInputs, Values.get]
  simp only [Values.get_head, Values.get_tail]
  by_cases positive : 0 < dimension <;> simp only [positive, ite_true, ite_false] <;> rfl

end ZkcExamples.Structured.SumcheckMathematicalHelpers
