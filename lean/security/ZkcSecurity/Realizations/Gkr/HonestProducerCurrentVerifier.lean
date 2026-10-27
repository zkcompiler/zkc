module

public import ZkcSecurity.Realizations.Gkr.HonestProducerCurrent
public import ZkcExamples.Structured.GkrSourceVerifier

@[expose] public section

/-! The observed honest validator reads as the actual current source verifier
through the common interface used by the verifier's soundness presentation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ZkcSecurity.Realizations.Gkr.HonestProducerCurrentVerifier
open Zkc Source Structured
open Zkc.Polynomial Zkc.Polynomial.Multilinear
open ZkcExamples.Structured
open HonestProducerSource HonestProducerObserved HonestProducerOccurrences
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem output_erase (ctx : ProtocolContext) (handle : Nat) (site : String)
    (index count : Nat) (point : List F) :
    (validatorOutput (G := G) ctx handle site index count point).interpret Occurrence.erase =
      (PIR.repeatN count (GkrVerifier.outputRound ctx handle) point).interpret CommonAdapter.embed := by
  induction count generalizing index point with
  | zero => rfl
  | succ count ih =>
    rw [validatorOutput, PIR.Process.interpret_bind,
      IterationObservations.within_interpret _ Occurrence.iterations_erase,
      IterationObservations.silent_within, actions_erase, PIR.repeatN, PIR.Process.interpret_bind]
    apply congrArg (PIR.Process.bind _)
    funext next
    exact ih (index + 1) next

omit [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem layers_erase (ctx : ProtocolContext) (handle : Nat) (sites : Sites)
    (encoding : CircuitEncoding F) (index count : Nat) (value : Nat × List F × F) :
    (validatorLayers (G := G) ctx handle sites encoding index count value).interpret Occurrence.erase =
      (PIR.repeatN count (GkrVerifier.layerStep ctx handle encoding.width
        encoding.circuit.add encoding.circuit.mul) value).interpret CommonAdapter.embed := by
  induction count generalizing index value with
  | zero => rfl
  | succ count ih =>
    rw [validatorLayers, PIR.Process.interpret_bind,
      IterationObservations.within_interpret _ Occurrence.iterations_erase,
      IterationObservations.silent_within, HonestProducerObservedLayers.validatorLayer_erase,
      PIR.repeatN, PIR.Process.interpret_bind]
    apply congrArg (PIR.Process.bind _)
    funext next
    exact ih (index + 1) next

omit [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem validator_erase (ctx : ProtocolContext) (handle : Nat) (sites : Sites)
    (encoding : CircuitEncoding F) (outputs : List F) :
    (validator (G := G) ctx handle sites encoding outputs).interpret Occurrence.erase =
      (GkrVerifier.verifier ctx handle encoding.layers encoding.width
        ((ofList? encoding.width outputs).getD 0) encoding.circuit.inputs
        encoding.circuit.add encoding.circuit.mul).interpret CommonAdapter.embed := by
  unfold validator GkrVerifier.verifier GkrVerifier.afterOutputs
  simp only [PIR.Process.interpret_bind, output_erase, layers_erase, PIR.Process.interpret]

/-- The claims owner's actual-source reading, specialized using only independent
circuit admission. No producer success or target truth is needed. -/
theorem original (encoding : CircuitEncoding F) (outputs : List F)
    (admitted : encoding.Admitted 4 4 outputs) (handle : Nat) :
    ((GkrSourceViews.program.participant F G 1 (currentInputs encoding outputs (some handle))).bind
      fun result => .done (result.get .here)).interpret CommonAdapter.project =
    GkrVerifier.verifier {} handle encoding.layers encoding.width
      ((ofList? encoding.width outputs).getD 0) encoding.circuit.inputs
      encoding.circuit.add encoding.circuit.mul := by
  have shape := admitted.1
  have addBound : encoding.add.length < indexLimit := by
    rw [shape.2.1, ← Nat.pow_add]
    apply Nat.pow_lt_pow_right (by decide)
    have dimension := admitted.2.2.2.2
    omega
  have mulBound : encoding.mul.length < indexLimit := by
    rw [shape.2.2.1, ← Nat.pow_add]
    apply Nat.pow_lt_pow_right (by decide)
    have dimension := admitted.2.2.2.2
    omega
  exact GkrSourceVerifier.verifier_reads handle encoding.inputs outputs encoding.add encoding.mul
    encoding.layers encoding.selector encoding.width _ _
    (CircuitEncoding.decode_getD outputs admitted.2.1) (encoding.inputs_decode shape)
    encoding.circuit.add encoding.circuit.mul shape.2.1 shape.2.2.1 addBound mulBound
    (encoding.add_decode shape) (encoding.mul_decode shape) shape.2.2.2
    admitted.2.2.1 admitted.2.2.2.1

/-- Both presentations are associated with the same complete common verifier,
including stops and all replies, not only its accepting executions. -/
theorem same_verifier (encoding : CircuitEncoding F) (outputs : List F)
    (admitted : encoding.Admitted 4 4 outputs) (handle : Nat) :
    ((validator (G := G) {} handle currentSites encoding outputs).interpret Occurrence.erase).interpret
      CommonAdapter.project =
    ((GkrSourceViews.program.participant F G 1 (currentInputs encoding outputs (some handle))).bind
      fun result => .done (result.get .here)).interpret CommonAdapter.project := by
  rw [validator_erase, CommonAdapter.project_embed, original encoding outputs admitted handle]
end ZkcSecurity.Realizations.Gkr.HonestProducerCurrentVerifier
