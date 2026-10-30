module

public import ZkcExamples.Structured.GkrSourceContinuation
public import Zkc.Protocols.Sumcheck.Source.VerifierHelpers
public import Zkc.Protocols.Gkr.Source.VerifierProcess
public import ZkcExamples.Structured.GkrLayerReading

@[expose] public section

/-! Reading the current admitted source root through its actual terminal check.
Shape admission is independent of the adversarial transcript and claim truth. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 50000
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
namespace ZkcExamples.Structured.GkrSourceVerifier
open Zkc.Source Zkc.Source.Structured SumcheckVerifierHelpers
open Zkc.Polynomial Zkc.Polynomial.Multilinear Zkc.Protocols.Gkr
open GkrRoundsReading GkrLayerReading

structured_associations GkrSourceViews [sourceHelper84 := GkrSourceBodies.sourceHelper84]

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

theorem terminal_plain (n : Nat) (xs point : List F) (table : Table F n) (claim : F)
    (decoded : ofList? n xs = some table) (length : point.length = n) (small : n < 64)
    (vectorBound : xs.length < indexLimit) :
    invoke (GkrRoundsReading.closed (F := F) (G := G)) GkrSourceBodies.sourceHelper84Helper
      (.cons xs (.cons point (.cons claim .nil))) =
      .done (.cons (decide (extension n table (coordinates n point) = claim)) .nil) := by
  apply GkrRoundsReading.invoke_law
  rw [sourceHelper84_association.invoke GkrSourceViews.unit.linked]
  simp [GkrSourceBodies.sourceHelper84Body, Region.denote, meaning, Evaluation.meaning,
    Evaluation.operation, Operands.eval, Regions.denote, TypedABI.get_cons_here, TypedABI.get_cons_there, Values.get_cons,
    Environment.prepend, Environment.push, SiteObservations.closed,
    SiteObservations.silent, PIR.Process.bind, Primitive.evaluate, primitiveOutcome,
    GkrSourceLaws.evaluate_extension n xs point table decoded length small vectorBound]

theorem verifier_reads (handle : Nat) (inputs outputs add mul : List F) (layers selector width : Nat)
    (outputsTable inputsTable : Table F width)
    (outputsDecoded : ofList? width outputs = some outputsTable)
    (inputsDecoded : ofList? width inputs = some inputsTable)
    (addTables mulTables : Nat → Wiring F width)
    (addShape : add.length = 2 ^ selector * 2 ^ (width + width + width))
    (mulShape : mul.length = 2 ^ selector * 2 ^ (width + width + width))
    (addBound : add.length < indexLimit) (mulBound : mul.length < indexLimit)
    (addDecoded : ∀ layer < layers, ofList? (width + width + width)
      (GkrSourceLaws.block add layer (2 ^ (width + width + width))) = some (addTables layer))
    (mulDecoded : ∀ layer < layers, ofList? (width + width + width)
      (GkrSourceLaws.block mul layer (2 ^ (width + width + width))) = some (mulTables layer))
    (selectorBound : layers ≤ 2 ^ selector) (widthBound : width ≤ 4) (layersBound : layers ≤ 4) :
    ((GkrSourceViews.program.participant F G 1 (.cons (some inputs) (.cons (some outputs) (.cons (some add)
        (.cons (some mul) (.cons (some layers) (.cons (some selector) (.cons (some width)
          (.cons (some handle) .nil))))))))).bind fun result => .done (result.get .here)).interpret
        CommonAdapter.project =
      GkrVerifier.verifier {} handle layers width outputsTable inputsTable addTables mulTables := by
  obtain ⟨separate, -, -⟩ := contexts_separate
  have small : width < 64 := by omega
  have tableBound : 2 ^ width < indexLimit := by
    unfold indexLimit
    exact Nat.pow_lt_pow_right (by decide) small
  have outputsBound : outputs.length < indexLimit := by
    rw [ofList?_length _ _ outputsDecoded]; exact tableBound
  have inputsBound : inputs.length < indexLimit := by
    rw [ofList?_length _ _ inputsDecoded]; exact tableBound
  have dimensions : selector + width + width + width < 64 := by
    have bound := addBound
    rw [addShape, ← Nat.pow_add] at bound
    by_contra outside
    have ge : 64 ≤ selector + (width + width + width) := by omega
    exact (not_lt_of_ge (Nat.pow_le_pow_right (by decide : 0 < 2) ge)) bound
  change ((GkrSourceAdmission.participant inputs outputs add mul layers selector width handle).bind
    fun result => .done (result.get .here)).interpret CommonAdapter.project = _
  rw [GkrSourceContinuation.participant inputs outputs add mul layers selector width handle
    widthBound layersBound (ofList?_length _ _ inputsDecoded) (ofList?_length _ _ outputsDecoded)
    (by simpa only [← Nat.pow_add, Nat.add_assoc] using addShape)
    (by simpa only [← Nat.pow_add, Nat.add_assoc] using mulShape) dimensions selectorBound]
  unfold GkrSourceContinuation.process
  rw [GkrRoundsReading.empty_plain]
  simp only [PIR.Process.bind, TypedABI.get_cons_here, TypedABI.get_cons_there, Values.get_cons]
  have outputFold := Generated.Presentations.Gkr.Root.verifierOutput_fold (F := F) (G := G) {} (.ofSeparate separate (by decide)) (some handle)
    width widthBound (.cons (some []) (.cons none .nil)) (some [])
    (Generated.Presentations.Gkr.Root.verifierOutputState_masked {} _ rfl (some []))
  erw [outputFold]
  rw [Finite.fold_range_repeatN (fun result => Generated.Presentations.Gkr.Root.verifierOutputProcess (G := G) {}
      (some handle) result) 0 width (some []),
    PIR.Process.bind_assoc, PIR.Process.bind_assoc, PIR.Process.interpret_bind,
    repeatN_reads CommonAdapter.project _ (GkrVerifier.outputRound {} handle) some
      (fun point => output_reads {} handle point) width []]
  unfold GkrVerifier.verifier
  rw [PIR.Process.bind_assoc]
  have outputsYield := PIR.Yields.repeatN (invariant := fun index (point : List F) => point.length = index)
    (step := GkrVerifier.outputRound (G := G) {} handle)
    (fun index point length => (outputRound_yields {} handle point).mono fun next same => by omega)
    width 0 [] rfl
  refine outputsYield.bind_congr fun point pointLength => ?_
  simp only [Nat.zero_add] at pointLength
  simp only [PIR.Process.bind, Generated.Presentations.Gkr.Root.verifierOutputState, TypedABI.get_cons_here, TypedABI.get_cons_there, Values.get_cons,
    evaluate_plain width outputs point outputsTable outputsDecoded pointLength small outputsBound, GkrLayerReading.tuple19_plain, PIR.Process.bind]
  have layerFold := Generated.Presentations.Gkr.Root.verifierLayer_fold (F := F) (G := G) {} (.ofSeparate separate (by decide)) (some inputs)
    (some add) (some mul) (some layers) (some selector) (some width) (some handle) layers layersBound
    (.cons none (.cons (some point) (.cons (some (extension width outputsTable (coordinates width point))) .nil)))
    (some point, some (extension width outputsTable (coordinates width point)))
    (Generated.Presentations.Gkr.Root.verifierLayerState_masked {} _ rfl (some point)
      (some (extension width outputsTable (coordinates width point))))
  erw [layerFold]
  rw [PIR.Process.bind_assoc, PIR.Process.bind_assoc, PIR.Process.interpret_bind]
  have layersRead := layers_reads (G := G) handle layers width selector add mul addTables mulTables addShape
    mulShape addBound mulBound addDecoded mulDecoded selectorBound widthBound layers
    (0, point, extension width outputsTable (coordinates width point)) (by simp) pointLength
  erw [layersRead]
  unfold GkrVerifier.afterOutputs
  rw [PIR.Process.bind_assoc]
  have layersYield := PIR.Yields.repeatN
    (invariant := fun index (state : GkrVerifier.State F) => state.1 = index ∧ state.2.1.length = width)
    (step := GkrVerifier.layerStep (G := G) {} handle width addTables mulTables)
    (fun index state valid => (layerStep_yields handle width addTables mulTables state).mono
      fun next advanced => ⟨by rw [advanced.1, valid.1], advanced.2⟩)
    layers 0 (0, point, extension width outputsTable (coordinates width point)) ⟨rfl, pointLength⟩
  refine layersYield.bind_congr fun final valid => ?_
  simp only [PIR.Process.bind, Generated.Presentations.Gkr.Root.verifierLayerState, TypedABI.get_cons_here, TypedABI.get_cons_there, Values.get_cons]
  erw [GkrInputInvocation.invoke (F := F) (G := G)
    (({} : ProtocolContext).enter "label_696e707574" [1])
    (some inputs) (some final.2.1) (some final.2.2)]
  simp only [Evaluation.ComponentTables.toOn, Generated.Presentations.Gkr.payload, Generated.Presentations.Gkr.program, GkrSourceViews.program, Generated.Presentations.Gkr.Input.verifierProcess, terminal_plain width inputs final.2.1
    inputsTable final.2.2 inputsDecoded valid.2 small inputsBound, PIR.Process.bind,
    TypedABI.get_cons_here, TypedABI.get_cons_there, Values.get_cons, PIR.Process.interpret, GkrVerifier.decision]


end ZkcExamples.Structured.GkrSourceVerifier
