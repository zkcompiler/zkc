module

public import ZkcSecurityExamples.Gkr.HonestProducerAlgorithm
public import Zkc.Protocols.Sumcheck.Source.VerifierHelpers
public import ZkcSecurityExamples.Gkr.HonestProducerPackets
public import ZkcSecurityExamples.Gkr.HonestCircuitSource
public import ZkcSecurity.Bindings.Gkr.Encoding
public import ZkcExamples.Structured.GkrProverContinuation
public import Zkc.Source.TypedABI
public import Zkc.Source.Structured.OccurrencePresentation
public import ZkcSecurityExamples.Gkr.HonestProducerObserved
public import Zkc.Source.Structured.LoopPresentation
public meta import ZkcTools.StructuredSource.Composition

@[expose] public section

/-! Algorithmic source correspondence for the complete GKR honest producer.
The reference is the independently evaluated circuit. Helper correctness is
discharged here, rather than included in the honest input policy. -/



set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false

namespace ZkcSecurity.Realizations.Gkr.HonestProducerSource
open Zkc Source Structured
open Zkc.Polynomial Zkc.Polynomial.Multilinear CoefficientRows
open ZkcExamples.Structured GkrSourceLaws SumcheckVerifierHelpers Generated.Presentations.Gkr.Root
open ZkcSecurity.Examples.Components
open HonestProducerRounds HonestProducerPackets

variable {F G : Type} [Field F] [DecidableEq F]

variable [AddCommGroup G] [Module F G] [DecidableEq G]

/-- Current source block selection, transported from the exact helper body. -/
theorem selectBlock_plain (xs : List F) (position bits size : Nat)
    (shape : xs.length = 2 ^ bits * size) (positive : 0 < size) (inside : position < 2 ^ bits)
    (vectorBound : xs.length < indexLimit) :
    invoke (plainHelpers (F := F) (G := G) GkrSourceViews.unit).closed
      GkrSourceBodies.selectBlockHelper (.cons xs (.cons position (.cons bits .nil))) =
      .done (.cons (GkrSourceLaws.block xs position size) .nil) :=
  helper_plain _ _ _ (GkrSourceLaws.selectBlock_equation xs position bits size shape positive inside vectorBound)

/-- Current source line-point computation, for all challenge replies. -/
theorem linePoint_plain (start finish : List F) (t : F) (sameLength : finish.length = start.length)
    (small : start.length < indexLimit) :
    invoke (plainHelpers (F := F) (G := G) GkrSourceViews.unit).closed
      GkrSourceBodies.linePointHelper (.cons start (.cons finish (.cons t .nil))) =
      .done (.cons (linePoints start finish t) .nil) :=
  helper_plain _ _ _ (GkrSourceLaws.linePoint_equation start finish t sameLength small)

omit [DecidableEq F] in
theorem add_stack (encoding : CircuitEncoding F) (shape : encoding.Shape) :
    HonestCircuit.StackedEncoding encoding.add encoding.layers encoding.selector encoding.circuit.add :=
  ⟨shape.2.1, fun index inside => encoding.add_decode shape index inside⟩

omit [DecidableEq F] in
theorem mul_stack (encoding : CircuitEncoding F) (shape : encoding.Shape) :
    HonestCircuit.StackedEncoding encoding.mul encoding.layers encoding.selector encoding.circuit.mul :=
  ⟨shape.2.2.1, fun index inside => encoding.mul_decode shape index inside⟩

abbrev observedHelpers := Occurrence.helpers (ringModel F G) GkrSourceViews.unit

abbrev beforeInput : ProtocolTable (assignment F G) (Occurrence.signature (uniformCarriers F G)) :=
  extendProtocolTableOn (ringModel F G) (.silent _) Occurrence.actions observedHelpers []
    GkrSourceViews.roundsDefinition Occurrence.iterations
abbrev beforeRoot : ProtocolTable (assignment F G) (Occurrence.signature (uniformCarriers F G)) :=
  extendProtocolTableOn (ringModel F G) (.silent _) Occurrence.actions observedHelpers beforeInput
    GkrSourceViews.sourceProtocol80Definition Occurrence.iterations

theorem beforeInput_masked : ProtocolPresentation.Masked (beforeInput (F := F) (G := G)) :=
  ProtocolPresentation.masked_extend (ringModel F G) _ _ _ _
    (ProtocolPresentation.masked_empty _ _) _ _

theorem beforeRoot_masked : ProtocolPresentation.Masked (beforeRoot (F := F) (G := G)) :=
  ProtocolPresentation.masked_extend (ringModel F G) _ _ _ _ beforeInput_masked _ _

theorem participant_body (self : Nat)
    (args : Values (Component (assignment F G)) GkrSourceBodies.gkrSignature.inputs) :
    Occurrence.participant (ringModel F G) GkrSourceViews.program self args =
      GkrSourceViews.gkrDefinition.denoteWithOn (ringModel F G) (.silent _) Occurrence.actions
        observedHelpers beforeRoot Occurrence.iterations {} self args := by
  change invokeProtocol (extendProtocolTableOn (ringModel F G) (.silent _) Occurrence.actions
    observedHelpers beforeRoot GkrSourceViews.gkrDefinition Occurrence.iterations)
    GkrSourceViews.gkrDefinition.signature {} self args = _
  rw [extendProtocolTableOn, invokeProtocol_cons_same]

theorem rounds_body (ctx : ProtocolContext) (self : Nat)
    (args : Values (Component (assignment F G)) GkrSourceBodies.roundsSignature.inputs) :
    invokeProtocol (beforeRoot (F := F) (G := G)) GkrSourceBodies.roundsSignature ctx self args =
      (Generated.Presentations.Gkr.Rounds.roundsBody.denote
        (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions
          observedHelpers self [] ctx Occurrence.iterations)
        (maskValues self (ctx.mapScopes GkrSourceBodies.roundsSignature.inputScopes) args).get).bind
        (fun out => .done (maskValues self (ctx.mapScopes GkrSourceBodies.roundsSignature.outputScopes) out)) := by
  change invokeProtocol (⟨GkrSourceViews.sourceProtocol80Definition.signature, _⟩ :: _)
    GkrSourceViews.roundsDefinition.signature ctx self args = _
  rw [invokeProtocol_cons_other _ _ _ (by
    change GkrSourceBodies.sourceProtocol80Signature.name ≠ GkrSourceBodies.roundsSignature.name
    decide)]
  unfold beforeInput extendProtocolTableOn
  rw [invokeProtocol_cons_same]
  unfold CheckedProtocol.denoteWithOn
  erw [GkrSourceViews.roundsDefinition.body_eq_of_raw _ Generated.Presentations.Gkr.Rounds.roundsBody_raw]
  rfl


/-- The current source round callbacks, with each actual occurrence frame, compute
exactly the proved four-vector round algorithm for every received field value. -/
theorem observed_rounds_fold (ctx : ProtocolContext) (site : String) (start count : Nat) {n : Nat}
    (reference : GkrRoundsReference.State F (n + count)) (raw : Raw F)
    (decoded : Decodes raw reference) (capacity : 2 ^ (n + count) < indexLimit) (point : List F) :
    Finite.fold (fun result index => Occurrence.iterations.within site index
      ((Generated.Presentations.Gkr.Rounds.proverProcess (G := G) ctx result.1 result.2.1 result.2.2.1
        result.2.2.2.1 result.2.2.2.2).interpret Occurrence.actions))
      (List.range' start count) (values raw point) =
      (HonestProducerOccurrences.producerRounds ctx site start count reference raw point).bind
        (fun result => .done (values result.raw result.point)) := by
  induction count generalizing start raw point with
  | zero => rfl
  | succ count ih =>
    have smaller : 2 ^ (n + count) < indexLimit :=
      (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)).trans_lt capacity
    rw [List.range'_succ, Finite.fold]
    change (Occurrence.iterations.within site start
      ((Generated.Presentations.Gkr.Rounds.proverProcess ctx (some raw.add) (some raw.mul)
        (some raw.left) (some raw.right) (some point)).interpret Occurrence.actions)).bind _ = _
    have step := HonestProducerRounds.round_process (G := G) ctx (sourceRaw raw) reference decoded smaller point
    dsimp only [sourceRaw] at step
    rw [step]
    simp only [HonestProducerOccurrences.producerRounds, IterationObservations.within_eq,
      Occurrence.iterations, IterationObservations.enter, IterationObservations.leave,
      execute, PIR.Process.interpret, Occurrence.actions, PIR.Process.bind]
    congr 1; funext _; congr 1; funext _; congr 1; funext _; congr 1; funext _
    congr 1; funext challenge; congr 1; funext _
    exact ih (start + 1) (GkrRoundsReference.restrict reference challenge) (raw.restrict challenge)
      (restriction_decodes raw reference decoded challenge) smaller (point ++ [challenge])

noncomputable def roundsPresentation (ctx : ProtocolContext) (add mul left right : Option (List F)) (count : Option Nat) :
    PIR.Process (Occurrence.signature (uniformCarriers F G))
      (Values (Component (assignment F G)) Generated.Presentations.Gkr.Rounds.roundsOutputs) :=
  (invoke (observedHelpers (F := F) (G := G)).closed GkrSourceBodies.emptyHelper .nil).bind fun empty =>
  (denoteRepeatOn (carriers := uniformCarriers F G) Generated.Presentations.Gkr.Rounds.roundSpec ctx 0 count
    (Generated.Presentations.Gkr.Rounds.proverState add mul left right (some (empty.get .here)))
    (.cons none .nil)
    (fun args => Generated.Presentations.Gkr.Rounds.roundBody.denote
      (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions observedHelpers 0 [] ctx Occurrence.iterations) args.get)
    Occurrence.iterations "s9").bind fun result =>
  .done (.cons (result.get (.there (.there (.there (.there .here)))))
    (.cons (result.get .here) (.cons (result.get (.there .here))
    (.cons (result.get (.there (.there .here))) (.cons (result.get (.there (.there (.there .here))))
    (.cons none (.cons none .nil)))))))

theorem rounds_presentation (ctx : ProtocolContext) (zero : ctx.roles 0 = 0) (one : ctx.roles 1 = 1)
    (add mul left right : Option (List F)) (count : Option Nat) :
  Generated.Presentations.Gkr.Rounds.roundsBody.denote
    (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions observedHelpers 0 [] ctx Occurrence.iterations)
    ((.cons add (.cons mul (.cons left (.cons right (.cons none (.cons none (.cons count (.cons none .nil)))))))) : Values (Component (assignment F G)) Generated.Presentations.Gkr.Rounds.roundsInputs).get =
    roundsPresentation (G := G) ctx add mul left right count := by
  have normalized := Generated.Presentations.Gkr.Rounds.proverRounds_observed (F := F) (G := G)
    ctx (.ofSeparate (show ctx.roles 1 ≠ ctx.roles 0 from by omega) (by decide))
    [] (ProtocolPresentation.masked_empty (ringModel F G) _)
    add mul left right count
  dsimp only [NormalForm.runsAtOn, NormalForm.meaningAtOn] at normalized
  repeat rw [zero] at normalized
  refine normalized.trans ?_
  source_composition_equation atoms [invoke, denoteRepeatOn]



/-- Exact current Rounds invocation in the occurrence view. Input and output
masks remain those of the current eight-input source declaration. -/
theorem rounds_invocation (ctx : ProtocolContext) (zero : ctx.roles 0 = 0) (one : ctx.roles 1 = 1)
    (add mul left right : Option (List F)) (count : Option Nat)
    (pending : Option (List F)) (claim : Option F) (service : Option Nat) :
    invokeProtocol (beforeRoot (F := F) (G := G)) GkrSourceBodies.roundsSignature ctx 0
      (.cons add (.cons mul (.cons left (.cons right (.cons pending (.cons claim (.cons count (.cons service .nil)))))))) =
      roundsPresentation ctx add mul left right count := by
  rw [rounds_body]
  have masked : maskValues 0 (ctx.mapScopes GkrSourceBodies.roundsSignature.inputScopes)
      ((.cons add (.cons mul (.cons left (.cons right (.cons pending (.cons claim (.cons count (.cons service .nil)))))))) : Values (Component (assignment F G)) Generated.Presentations.Gkr.Rounds.roundsInputs) =
      (.cons add (.cons mul (.cons left (.cons right (.cons none (.cons none (.cons count (.cons none .nil)))))))) := by
    iterate 9 unfold maskValues
    simp [ProtocolContext.mapScopes, GkrSourceBodies.roundsSignature,
      Participant.restrict, zero, one, Generated.Presentations.Gkr.payload, Generated.Presentations.Gkr.program, GkrSourceViews.program,
    Generated.Presentations.Gkr.Rounds.roundsDefinition, GkrSourceViews.roundsDefinition]
  rw [masked, rounds_presentation ctx zero one]
  unfold roundsPresentation
  simp only [PIR.Process.bind_assoc]
  apply congrArg (PIR.Process.bind _)
  funext empty
  apply congrArg (PIR.Process.bind _)
  funext result
  simp only [PIR.Process.bind]
  apply congrArg PIR.Process.done
  change maskValues 0 _ (show Values (Component (assignment F G)) GkrSourceBodies.roundsSignature.outputs from _) = _
  iterate 8 unfold maskValues
  simp [ProtocolContext.mapScopes, GkrSourceBodies.roundsSignature,
    Participant.restrict, zero, one, Generated.Presentations.Gkr.payload, Generated.Presentations.Gkr.program, GkrSourceViews.program,
    Generated.Presentations.Gkr.Rounds.roundsDefinition, GkrSourceViews.roundsDefinition]

/-- The observed repeat uses the same exact helper computation as the plain
callback. Each frame encloses precisely one complete round. -/
theorem rounds_repeat (ctx : ProtocolContext) (separate : ctx.roles 1 ≠ ctx.roles 0)
    (site : String) (count : Nat) (bounded : count ≤ 4)
    (raw : Raw F) (point : List F) :
    denoteRepeatOn (carriers := uniformCarriers F G) Generated.Presentations.Gkr.Rounds.roundSpec ctx (ctx.roles 0)
      (some count) (Generated.Presentations.Gkr.Rounds.proverState (some raw.add) (some raw.mul)
        (some raw.left) (some raw.right) (some point)) (.cons none .nil)
      (fun args => Generated.Presentations.Gkr.Rounds.roundBody.denote
        (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions observedHelpers
          (ctx.roles 0) [] ctx Occurrence.iterations) args.get)
      Occurrence.iterations site =
      (Finite.fold (fun result index => Occurrence.iterations.within
        (qualifyProtocolSite ctx.applicationPrefix site) index
        ((Generated.Presentations.Gkr.Rounds.proverProcess ctx result.1 result.2.1 result.2.2.1
          result.2.2.2.1 result.2.2.2.2).interpret Occurrence.actions))
        (List.range' 0 count) (values raw point)).bind fun result =>
          .done (Generated.Presentations.Gkr.Rounds.proverState result.1 result.2.1 result.2.2.1
            result.2.2.2.1 result.2.2.2.2) := by
  apply Zkc.Source.Structured.LoopPresentation.present Generated.Presentations.Gkr.Rounds.roundSpec ctx (ctx.roles 0) (by simp) _ _ _ site
    (fun result : Result F => Generated.Presentations.Gkr.Rounds.proverState result.1 result.2.1 result.2.2.1
      result.2.2.2.1 result.2.2.2.2)
    (fun result => Generated.Presentations.Gkr.Rounds.proverState_masked ctx _ rfl _ _ _ _ _)
    _ _ count bounded _ (values raw point)
      (Generated.Presentations.Gkr.Rounds.proverState_masked ctx _ rfl _ _ _ _ _)
  intro result index
  erw [Generated.Presentations.Gkr.Rounds.round_occurrence (F := F) (G := G) ctx (ctx.roles 0) []
    (.cons (some index) ((Generated.Presentations.Gkr.Rounds.proverState result.1 result.2.1 result.2.2.1 result.2.2.2.1 result.2.2.2.2).append (.cons none .nil))), Generated.Presentations.Gkr.Rounds.prover_process ctx _ rfl (.ofSeparate separate (by decide))]
  rw [PIR.Process.interpret_bind]
  rfl


/-- The current output-point callback, retaining every delivery and frame. -/
theorem output_repeat (ctx : ProtocolContext) (separate : ctx.roles 1 ≠ ctx.roles 0)
    (site : String) (count : Nat) (bounded : count ≤ 4) (point : List F) :
    denoteRepeatOn (carriers := uniformCarriers F G) outputSpec ctx (ctx.roles 0) (some count)
      (proverOutputState (some point)) (.cons none .nil)
      (fun args => outputBody.denote (participantMeaningWithOn (ringModel F G) (.silent _)
        Occurrence.actions observedHelpers (ctx.roles 0) [] ctx Occurrence.iterations) args.get)
      Occurrence.iterations site =
      (HonestProducerObserved.producerOutput ctx
        (qualifyProtocolSite ctx.applicationPrefix site) 0 count point).bind
          (fun result => .done (proverOutputState (some result))) := by
  have repeated := Zkc.Source.Structured.LoopPresentation.present (carriers := uniformCarriers F G) outputSpec ctx (ctx.roles 0) (by simp)
    (.cons none .nil)
    (fun args => outputBody.denote (participantMeaningWithOn (ringModel F G) (.silent _)
      Occurrence.actions observedHelpers (ctx.roles 0) [] ctx Occurrence.iterations) args.get)
    Occurrence.iterations site (fun point : List F => proverOutputState (some point))
    (fun point => proverOutputState_masked ctx _ rfl _) (fun point _ =>
      (output (G := G) ctx 1 point).interpret Occurrence.actions) (by
      intro point index
      erw [output_occurrence (F := F) (G := G) ctx (ctx.roles 0) []
        (.cons (some index) ((proverOutputState (some point)).append (.cons none .nil))), proverOutput_process ctx _ rfl (.ofSeparate separate (by decide)), HonestProducerPackets.output_point]
      rfl) count bounded _ point (proverOutputState_masked ctx _ rfl _)
  rw [repeated]
  rw [Zkc.Source.Structured.LoopPresentation.foldCounted _
    (HonestProducerObserved.producerOutput (G := G) ctx
      (qualifyProtocolSite ctx.applicationPrefix site))
    (fun _ _ => rfl) (fun _ _ _ => rfl)]

/-- All coefficient packets are computed by the current read-after helper,
inside their real source iteration frames. -/
theorem coefficient_fold_observed (ctx : ProtocolContext) (site : String) (line : List F)
    (start count : Nat) (lineBound : line.length < indexLimit) (indexBound : start + count < indexLimit) :
    Finite.fold (fun (_ : Unit) index => Occurrence.iterations.within site index
      ((proverCoefficientProcess (G := G) ctx index (some line)).interpret Occurrence.actions))
      (List.range' start count) () =
      HonestProducerObservedLayers.producerCoefficients ctx site start (tail line start count) := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
    rw [List.range'_succ, Finite.fold, HonestProducerPackets.line_coefficient ctx line start lineBound (by omega), tail_succ]
    simp only [HonestProducerObservedLayers.producerCoefficients, IterationObservations.within_eq,
      Occurrence.iterations, IterationObservations.enter, IterationObservations.leave,
      PIR.Process.interpret, Occurrence.actions, PIR.Process.bind]
    congr 1; funext _; congr 1; funext _; congr 1; funext _
    exact ih (start + 1) (by omega)

theorem coefficients_observed (ctx : ProtocolContext) (separate : ctx.roles 1 ≠ ctx.roles 0)
    (site : String) (line : List F) (count : Nat) (bounded : count ≤ 4)
    (lineBound : line.length < indexLimit) :
    denoteRepeatOn (carriers := uniformCarriers F G) coefficientSpec ctx (ctx.roles 0) (some count)
      proverCoefficientState (.cons (some line) .nil)
      (fun args => coefficientBody.denote (participantMeaningWithOn (ringModel F G) (.silent _)
        Occurrence.actions observedHelpers (ctx.roles 0) [] ctx Occurrence.iterations) args.get)
      Occurrence.iterations site =
      (HonestProducerObservedLayers.producerCoefficients ctx
        (qualifyProtocolSite ctx.applicationPrefix site) 0 (tail line 0 count)).bind
          (fun _ => .done proverCoefficientState) := by
  have repeated := Zkc.Source.Structured.LoopPresentation.present (carriers := uniformCarriers F G) coefficientSpec ctx (ctx.roles 0) (by simp)
    (.cons (some line) .nil)
    (fun args => coefficientBody.denote (participantMeaningWithOn (ringModel F G) (.silent _)
      Occurrence.actions observedHelpers (ctx.roles 0) [] ctx Occurrence.iterations) args.get)
    Occurrence.iterations site (fun _ : Unit => proverCoefficientState)
    (fun _ => proverCoefficientState_masked ctx _ rfl)
    (fun _ index => (proverCoefficientProcess (G := G) ctx index (some line)).interpret Occurrence.actions)
    (by
      intro value index
      cases value
      erw [coefficient_occurrence (F := F) (G := G) ctx (ctx.roles 0) []
        (.cons (some index) (proverCoefficientState.append (.cons (some line) .nil))), proverCoefficient_process ctx _ rfl (.ofSeparate separate (by decide))]
      rw [PIR.Process.interpret_bind]
      rfl) count bounded _ () (proverCoefficientState_masked ctx _ rfl)
  rw [repeated, coefficient_fold_observed ctx _ line 0 count lineBound (by simp only [indexLimit]; omega)]


/-- The actual current source Rounds call equals the proved observed algorithm.
No transcript or helper-success premise is supplied. -/
theorem rounds_observed (ctx : ProtocolContext) (zero : ctx.roles 0 = 0) (one : ctx.roles 1 = 1)
    (count : Nat) (bounded : count ≤ 4) {n : Nat}
    (reference : GkrRoundsReference.State F (n + count)) (raw : Raw F)
    (decoded : Decodes raw reference) (capacity : 2 ^ (n + count) < indexLimit)
    (pending : Option (List F)) (claim : Option F) (service : Option Nat) :
    invokeProtocol (beforeRoot (F := F) (G := G)) GkrSourceBodies.roundsSignature ctx 0
      (.cons (some raw.add) (.cons (some raw.mul) (.cons (some raw.left) (.cons (some raw.right)
        (.cons pending (.cons claim (.cons (some count) (.cons service .nil)))))))) =
      (HonestProducerOccurrences.producerRounds ctx
        (qualifyProtocolSite ctx.applicationPrefix "s9") 0 count reference raw []).bind
          (fun result => .done (returned (values result.raw result.point))) := by
  rw [rounds_invocation ctx zero one, roundsPresentation, OccurrencePresentation.closed_helper, HonestProducerRounds.empty_plain]
  simp only [PIR.Process.interpret, PIR.Process.bind, Values.get]
  have repeated := rounds_repeat (F := F) (G := G) ctx (by omega) "s9" count bounded raw []
  rw [zero] at repeated
  rw [repeated, observed_rounds_fold ctx _ 0 count reference raw decoded capacity [], PIR.Process.bind_assoc]
  simp only [PIR.Process.bind_assoc, PIR.Process.bind]
  rfl

end ZkcSecurity.Realizations.Gkr.HonestProducerSource
