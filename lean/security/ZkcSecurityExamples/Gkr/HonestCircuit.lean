module

public import ZkcSecurity.Bindings.Gkr.CircuitEncodingLaws
public import ZkcExamples.Structured.GkrSourceLaws
public import ZkcExamples.Structured.GkrGateCompanion
public import ZkcSecurityExamples.Gkr.HonestHelpers
public import ZkcSecurityExamples.Components.GkrRoundsHelpers
public import Zkc.Protocols.Sumcheck.Source.VerifierHelpers
public import Zkc.Protocols.Multilinear.Source.CollectionEncoding
public import ZkcSecurityExamples.Gkr.HonestCircuitCompanion

@[expose] public section

/-! The actual layer-value helper, with scalar and map equations derived from
its checked source associations. No helper correctness is assumed. -/

namespace ZkcSecurity.Realizations.Gkr.HonestCircuit
open Zkc Source Structured
open ZkcExamples.Structured GkrSourceViews GkrSourceLaws
open ZkcExamples.Structured.PrimitiveLibrary
open Zkc.Polynomial Zkc.Polynomial.Multilinear
open ZkcSecurity.Examples.Components

set_option maxRecDepth 20000 in
structured_associations GkrSourceViews
  [helper34 := GkrSourceBodies.helper34]

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
attribute [local implicit_reducible] Op.arguments Op.results Op.regions

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

/-- All four selected bodies are associated once with the admitted unit. -/
theorem gate_bodies : GkrGateGoals.Bodies unit.definitions := by
  bind_structured_bodies

theorem circuit_bodies : Goals.Bodies unit.definitions := by
  bind_structured_bodies

/-- The source gate callback is the independent gate formula. -/
theorem gate_equation (add mul left right : F) :
    invoke (helpers (G := G)) GkrSourceBodies.helper31Helper
      ((GkrGateGoals.Value.Inputs.pack (Value := assignment F G))
        { addWeight := add, mulWeight := mul, left, right }) =
        .done (GkrGateGoals.Value.encode (ringModel F G)
          ⟨Zkc.Protocols.AlgebraicRounds.Gate.value add mul left right⟩) := by
  apply (GkrGateCompanion.valueLaw (ringModel F G)).invokeUniform
    (helper := GkrSourceBodies.helper31Helper)
    unit.definitions unit.linked gate_bodies.value
  trivial

/-- Dependencies use the same actual linked table, with no assumed helper law. -/
theorem gate_value_dependency :
    (GkrGateCompanion.valueLaw (ringModel F G)).Realizes
      (helper := GkrSourceBodies.helper31Helper) (helpers (G := G)) := by
  apply (GkrGateCompanion.valueLaw (ringModel F G)).realizesUniform
    (F := F) (G := G) (helper := GkrSourceBodies.helper31Helper)
    unit.definitions unit.linked gate_bodies.value
  intro arguments
  rw [← GkrGateGoals.Value.Inputs.pack_unpack arguments]
  trivial

theorem gate_realization_dependency :
    (GkrGateCompanion.realizationLaw (ringModel F G)).Realizes
      (helper := GkrSourceBodies.scopedHelper42Helper) (helpers (G := G)) := by
  apply (GkrGateCompanion.realizationLaw (ringModel F G)).realizesUniform
    (F := F) (G := G) (helper := GkrSourceBodies.scopedHelper42Helper)
    unit.definitions unit.linked gate_bodies.realization
  intro arguments
  rw [← GkrGateGoals.Value.Inputs.pack_unpack arguments]
  exact gate_value_dependency

abbrev gateCollection : CollectSpec := GkrGateGoals.collection

/-- The ordered callback retains every input vector in its actual ABI. -/
theorem gate_callback (a m l r : F) (add mul left right : List F) :
    invoke (helpers (G := G)) gateCollection.bodyHelper
      (GkrGateGoals.Callback.Inputs.pack (Value := assignment F G)
        { addWeight := a, mulWeight := m, left := l, right := r,
          addWeights := add, mulWeights := mul, lefts := left, rights := right }) =
      .done (GkrGateGoals.Callback.encode (ringModel F G)
        ⟨Zkc.Protocols.AlgebraicRounds.Gate.value (F := F) a m l r⟩) := by
  apply (GkrGateCompanion.callbackLaw (ringModel F G)).invokeUniform
    (helper := GkrSourceBodies.scopedHelper43Helper)
    unit.definitions unit.linked gate_bodies.callback
  exact gate_realization_dependency

theorem gate_callback_dependency :
    (GkrGateCompanion.callbackLaw (ringModel F G)).Realizes
      (helper := GkrSourceBodies.scopedHelper43Helper) (helpers (G := G)) := by
  apply (GkrGateCompanion.callbackLaw (ringModel F G)).realizesUniform
    (F := F) (G := G) (helper := GkrSourceBodies.scopedHelper43Helper)
    unit.definitions unit.linked gate_bodies.callback
  intro arguments
  rw [← GkrGateGoals.Callback.Inputs.pack_unpack arguments]
  exact gate_realization_dependency

/-- Actual ordered domain admission and the installed complete callback law. -/
theorem gate_map_dependencies (add mul left right : List F) :
    GkrGateCompanion.mapCondition (ringModel F G) (helpers (G := G)) add mul left right := by
  constructor
  · exact GkrRoundsHelpers.values_domain (G := G) add mul left right
  · intro length _ index _
    exact gate_callback (add[index]?.getD 0) (mul[index]?.getD 0)
      (left[index]?.getD 0) (right[index]?.getD 0) add mul left right

/-- Four arbitrary decoded tables, including every operand's shape. -/
theorem gate_map_encodes {n : Nat} (add mul left right : Table F n)
    (small : 2 ^ n < indexLimit) :
    invoke (helpers (G := G)) GkrSourceBodies.scopedHelper44Helper
      (GkrGateGoals.Map.Inputs.pack (Value := assignment F G)
        { addWeights := GkrRoundsLayout.encode add, mulWeights := GkrRoundsLayout.encode mul,
          lefts := GkrRoundsLayout.encode left, rights := GkrRoundsLayout.encode right }) =
      .done (GkrGateGoals.Map.encode (ringModel F G)
        ⟨GkrRoundsLayout.encode (fun bits =>
          Zkc.Protocols.AlgebraicRounds.Gate.value (add bits) (mul bits) (left bits) (right bits))⟩) := by
  rw [(GkrGateCompanion.mapLaw (ringModel F G)).invokeUniform
    (helper := GkrSourceBodies.scopedHelper44Helper)
    unit.definitions unit.linked gate_bodies.map]
  · change primitiveOutcome (GkrGateGoals.Map.encodeOutcome (ringModel F G)
      (GkrGateCompanion.mapReference (ringModel F G)
        (GkrRoundsLayout.encode add) (GkrRoundsLayout.encode mul)
        (GkrRoundsLayout.encode left) (GkrRoundsLayout.encode right))) = _
    simp only [GkrRoundsLayout.encode]
    rw [GkrGateCompanion.map_encodes (ringModel F G) add mul left right small]
    rfl
  · exact gate_map_dependencies _ _ _ _

/-- Install the mathematical dependency contracts in the actual linked table.
Each proof uses the existing helper library, including strict map admission. -/
theorem dependencies : Companion.Dependencies (helpers (F := F) (G := G)) where
  block := fun source position width size shape positive inside bounded =>
    selectBlock_equation source position width size shape positive inside bounded
  power := fun width small => powerOfTwo_equation width small
  replicate := fun source count bounded small => HonestHelpers.replicate_equation source count bounded small
  tile := fun source count small bounded => HonestHelpers.tile_equation source count small bounded
  gates := fun add mul left right small => gate_map_encodes add mul left right small

/-- One actual loop iteration computes the independent value of one gate. -/
theorem layer_step_encodes {width : Nat} (a m : Zkc.Protocols.Gkr.Wiring F width)
    (v : Table F width) (xs : List F) (position : Fin (2 ^ width))
    (small : width + width + width < 64) :
    Goals.Step.body.denote (meaning F G (helpers (G := G)))
      (Goals.Step.Inputs.pack (Value := assignment F G)
        { position := position.val, values := xs, addWeights := GkrRoundsLayout.encode a,
          mulWeights := GkrRoundsLayout.encode m, width,
          left := GkrRoundsLayout.encode (GkrRoundsLayout.replicate width width v),
          right := GkrRoundsLayout.encode (GkrRoundsLayout.tile width width v) }).get =
      .done (Goals.Step.encode (ringModel F G)
        { values := xs ++ [(Zkc.Protocols.Gkr.layer a m v) (vertex width position)],
          addWeights := GkrRoundsLayout.encode a, mulWeights := GkrRoundsLayout.encode m, width,
          left := GkrRoundsLayout.encode (GkrRoundsLayout.replicate width width v),
          right := GkrRoundsLayout.encode (GkrRoundsLayout.tile width width v) }) := by
  rw [Evaluation.denote_meaning_eq_meaningOn]
  exact (Companion.stepLaw (G := G) a m v position small).valid _ _
    ⟨dependencies, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The complete actual helper33 loop, at every representable width. -/
theorem layer_encoded {width : Nat} (a m : Zkc.Protocols.Gkr.Wiring F width)
    (v : Table F width) (small : width + width + width < 64) :
    invoke (helpers (G := G)) GkrSourceBodies.helper33Helper
      (Goals.Layer.Inputs.pack (Value := assignment F G)
        { addWeights := GkrRoundsLayout.encode a, mulWeights := GkrRoundsLayout.encode m,
          below := GkrRoundsLayout.encode v, width }) =
      .done (Goals.Layer.encode (ringModel F G) ⟨GkrRoundsLayout.encode (Zkc.Protocols.Gkr.layer a m v)⟩) := by
  exact (Companion.layerLaw (G := G) a m v small).invokeUniform
    (F := F) (G := G) (helper := GkrSourceBodies.helper33Helper)
    unit.definitions unit.linked circuit_bodies.layer _ ⟨dependencies, rfl, rfl, rfl, rfl⟩

/-- Arbitrary exact raw encodings compute the independent circuit layer. -/
theorem layer_encodes {width : Nat} (add mul below : List F)
    (a m : Zkc.Protocols.Gkr.Wiring F width) (v : Table F width)
    (da : ofList? (width + width + width) add = some a)
    (dm : ofList? (width + width + width) mul = some m)
    (dv : ofList? width below = some v) (small : width + width + width < 64) :
    invoke (helpers (G := G)) GkrSourceBodies.helper33Helper
      (Goals.Layer.Inputs.pack (Value := assignment F G) { addWeights := add, mulWeights := mul, below, width }) =
        .done (Goals.Layer.encode (ringModel F G) ⟨GkrRoundsLayout.encode (Zkc.Protocols.Gkr.layer a m v)⟩) := by
  dsimp only [Goals.Layer.Inputs.pack]
  rw [← HonestHelpers.encode_of_decodes add a da, ← HonestHelpers.encode_of_decodes mul m dm,
    ← HonestHelpers.encode_of_decodes below v dv]
  exact layer_encoded a m v small

end ZkcSecurity.Realizations.Gkr.HonestCircuit
