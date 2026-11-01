module

public import ZkcSecurityExamples.Gkr.HonestProducerAlgorithm
public import Zkc.Protocols.Sumcheck.Source.VerifierHelpers
public import ZkcSecurityExamples.Gkr.HonestProducerPackets
public import ZkcSecurityExamples.Gkr.HonestCircuitSource
public import ZkcSecurity.Bindings.Gkr.Encoding
public import Zkc.Source.TypedABI
public import Zkc.Source.Structured.OccurrencePresentation
public import ZkcSecurityExamples.Gkr.HonestProducerObserved
public import Zkc.Source.Structured.OccurrenceYields
public import Zkc.Source.Structured.LoopPresentation
public import ZkcSecurityExamples.Gkr.SourceReferences
public import ZkcSecurityExamples.Gkr.SourceRows

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
open ZkcSecurity.Examples.Components.GkrRoundsRealization
open HonestProducerRounds HonestProducerPackets

variable {F G : Type} [Field F] [DecidableEq F]

variable [AddCommGroup G] [Module F G] [DecidableEq G]

/-- Current source block selection, transported from the exact helper body. -/
theorem selectBlock_plain (xs : List F) (position bits size : Nat)
    (shape : xs.length = 2 ^ bits * size) (positive : 0 < size) (inside : position < 2 ^ bits)
    (vectorBound : xs.length < indexLimit) :
    invoke (plainHelpers (F := F) (G := G) GkrSourceViews.unit).closed
      GkrSourceBodies.selectBlockHelper ((SourceRows.SelectBlockInputs.pack { table := xs, position := position, bits := bits })) =
      .done ((SourceRows.SelectBlockResults.pack { block := GkrSourceLaws.block xs position size })) :=
  closed_invoke_returned GkrSourceViews.unit _ _ _ (GkrSourceLaws.selectBlock_equation xs position bits size shape positive inside vectorBound)

/-- Current source line-point computation, for all challenge replies. -/
theorem linePoint_plain (start finish : List F) (t : F) (sameLength : finish.length = start.length)
    (small : start.length < indexLimit) :
    invoke (plainHelpers (F := F) (G := G) GkrSourceViews.unit).closed
      GkrSourceBodies.linePointHelper ((SourceRows.LinePointInputs.pack { start := start, finish := finish, challenge := t })) =
      .done ((SourceRows.LinePointResults.pack { point := linePoints start finish t })) :=
  closed_invoke_returned GkrSourceViews.unit _ _ _ (GkrSourceLaws.linePoint_equation start finish t sameLength small)

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
    (reference : GkrRoundsReference.State F (n + count)) (raw : RawState F)
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
    have step : Generated.Presentations.Gkr.Rounds.proverProcess (G := G) ctx
        (some raw.add) (some raw.mul) (some raw.left) (some raw.right) (some point) =
        (execute ctx 1 reference raw point).bind
          (fun result => .done (values result.raw result.point)) := by
      rw [execute_erases]
      simpa only [loop, execute, PIR.Process.bind, round_result, values] using
        HonestProducerRounds.round_process (G := G) ctx raw reference decoded smaller point
    have preserved : PIR.Yields (fun result => Decodes result.raw result.reference)
        ((execute (G := G) ctx 1 reference raw point).interpret Occurrence.actions) := by
      apply PIR.Yields.interpret
      simp only [execute, PIR.Yields]
      intro _ _ _ challenge
      exact restriction_decodes raw reference decoded challenge
    rw [List.range'_succ, Finite.fold]
    change (Occurrence.iterations.within site start
      ((Generated.Presentations.Gkr.Rounds.proverProcess ctx (some raw.add) (some raw.mul)
        (some raw.left) (some raw.right) (some point)).interpret Occurrence.actions)).bind _ = _
    rw [step, HonestProducerOccurrences.producerRounds, ObservedLoop.descending_succ]
    simp only [PIR.Process.interpret_bind, IterationObservations.within_eq,
      PIR.Process.bind_assoc, PIR.Process.bind]
    apply congrArg (PIR.Process.bind _)
    funext entered
    apply preserved.bind_congr
    intro result related
    simp only [PIR.Process.interpret, PIR.Process.bind]
    apply congrArg (PIR.Process.bind _)
    funext left
    exact ih (start + 1) result.reference result.raw related smaller result.point

/-- Exact current Rounds invocation in the occurrence view. Input and output
masks remain those of the current eight-input source declaration. -/
theorem rounds_invocation (ctx : ProtocolContext) (zero : ctx.roles 0 = 0) (one : ctx.roles 1 = 1)
    (add mul left right : Option (List F)) (count : Option Nat)
    (pending : Option (List F)) (claim : Option F) (service : Option Nat) :
    invokeProtocol (beforeRoot (F := F) (G := G)) GkrSourceBodies.roundsSignature ctx 0
      ((SourceRows.RoundsInputs.pack {
          add := add,
          mul := mul,
          left := left,
          right := right,
          pending := pending,
          claim := claim,
          count := count,
          service := service
        })) =
      roundsPresentation ctx [] add mul left right count := by
  rw [rounds_body]
  have distinct : NormalForm.RosterDistinct ctx 0 2 :=
    .ofSeparate (show ctx.roles 1 ≠ ctx.roles 0 from by omega) (by decide)
  have inputMask := SourceRows.RoundsInputs.mask_context (ringModel F G) ctx 0 distinct
    { add, mul, left, right, pending, claim, count, service }
  rw [zero] at inputMask
  rw [inputMask]
  have normalized := roundsPresentation_equation (F := F) (G := G) ctx
    distinct
    [] (ProtocolPresentation.masked_empty (ringModel F G) _) add mul left right count
  rw [zero] at normalized
  erw [normalized]
  have outputMask := SourceRows.RoundsResults.mask_context (ringModel F G) ctx 0 distinct
  rw [zero] at outputMask
  conv_lhs =>
    arg 2
    ext out
    arg 1
    rw [← SourceRows.RoundsResults.pack_unpack out, outputMask]
  dsimp only [roundsPresentation, roundsPresentation_certificate, NormalForm.runsAtOn, NormalForm.meaningAtOn]
  simp only [PIR.Process.bind_assoc, PIR.Process.bind]
  rfl

/-- The observed repeat uses the same exact helper computation as the plain
callback. Each frame encloses precisely one complete round. -/
theorem rounds_repeat (ctx : ProtocolContext) (separate : ctx.roles 1 ≠ ctx.roles 0)
    (site : String) (count : Nat) (bounded : count ≤ 4)
    (raw : RawState F) (point : List F) :
    denoteRepeatOn (carriers := uniformCarriers F G) Generated.Presentations.Gkr.Rounds.roundSpec ctx (ctx.roles 0)
      (some count) (Generated.Presentations.Gkr.Rounds.proverState (some raw.add) (some raw.mul)
        (some raw.left) (some raw.right) (some point)) ((SourceRows.RoundCaptures.pack { service := none }))
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
    ((SourceRows.RoundArguments.pack {
        index := some index,
        add := result.1,
        mul := result.2.1,
        left := result.2.2.1,
        right := result.2.2.2.1,
        point := result.2.2.2.2,
        pending := none,
        claim := none,
        service := none
      })), Generated.Presentations.Gkr.Rounds.prover_process ctx _ rfl (.ofSeparate separate (by decide)) index result.1 result.2.1 result.2.2.1 result.2.2.2.1 result.2.2.2.2 none]
  rw [PIR.Process.interpret_bind]
  rfl

/-- The current output-point callback, retaining every delivery and frame. -/
theorem output_repeat (ctx : ProtocolContext) (separate : ctx.roles 1 ≠ ctx.roles 0)
    (site : String) (count : Nat) (bounded : count ≤ 4) (point : List F) :
    denoteRepeatOn (carriers := uniformCarriers F G) outputSpec ctx (ctx.roles 0) (some count)
      (proverOutputState (some point)) ((SourceRows.OutputCaptures.pack { service := none }))
      (fun args => outputBody.denote (participantMeaningWithOn (ringModel F G) (.silent _)
        Occurrence.actions observedHelpers (ctx.roles 0) [] ctx Occurrence.iterations) args.get)
      Occurrence.iterations site =
      (HonestProducerObserved.producerOutput ctx
        (qualifyProtocolSite ctx.applicationPrefix site) 0 count point).bind
          (fun result => .done (proverOutputState (some result))) := by
  have repeated := Zkc.Source.Structured.LoopPresentation.present (carriers := uniformCarriers F G) outputSpec ctx (ctx.roles 0) (by simp)
    ((SourceRows.OutputCaptures.pack { service := none }))
    (fun args => outputBody.denote (participantMeaningWithOn (ringModel F G) (.silent _)
      Occurrence.actions observedHelpers (ctx.roles 0) [] ctx Occurrence.iterations) args.get)
    Occurrence.iterations site (fun point : List F => proverOutputState (some point))
    (fun point => proverOutputState_masked ctx _ rfl _) (fun point _ =>
      (output (G := G) ctx 1 point).interpret Occurrence.actions) (by
      intro point index
      erw [output_occurrence (F := F) (G := G) ctx (ctx.roles 0) []
        ((SourceRows.OutputArguments.pack {
            index := some index,
            verifierPoint := none,
            proverPoint := some point,
            service := none
          })), proverOutput_process ctx _ rfl (.ofSeparate separate (by decide)) index (some point) none, HonestProducerPackets.output_point]
      rfl) count bounded _ point (proverOutputState_masked ctx _ rfl _)
  rw [repeated]
  rfl

/-- All coefficient packets are computed by the current read-after helper,
inside their real source iteration frames. -/
theorem coefficient_fold_observed (ctx : ProtocolContext) (site : String) (line : List F)
    (start count : Nat) (lineBound : line.length < indexLimit) (indexBound : start + count < indexLimit) :
    Finite.fold (fun (_ : Unit) index => Occurrence.iterations.within site index
      ((proverCoefficientProcess (G := G) ctx index (some line)).interpret Occurrence.actions))
      (List.range' start count) () =
      HonestProducerObservedLayers.producerCoefficients ctx site start (tail line start count) := by
  let packet (index : Nat) : PIR.Process (Occurrence.signature (uniformCarriers F G)) Unit :=
    (@PIR.Process.call (participantInterface F G) Unit
      (.send (ty := .field scalarDomain) (GkrVerifier.lineCoefficientSite ctx) (ctx.roles 1)
        ((line)[index + 1]?.getD 0)) .done).interpret Occurrence.actions
  let step (_ : Unit) (index : Nat) := Occurrence.iterations.within site index (packet index)
  have translated := Zkc.Source.Structured.LoopPresentation.foldInvariant
    (fun (_ : Unit) index => Occurrence.iterations.within site index
      ((proverCoefficientProcess (G := G) ctx index (some line)).interpret Occurrence.actions))
    step (fun _ value => value) (fun _ _ => True) (start + count)
    (by
      intro index value inside _
      cases value
      rw [HonestProducerPackets.line_coefficient ctx line index lineBound (by omega)]
      exact (PIR.Process.bind_done _).symm)
    (by
      intro index value _ _
      exact Zkc.Source.Structured.OccurrenceYields.within _ _ _ (by intro reply; trivial))
    start count (by omega) () trivial
  rw [translated, PIR.Process.bind_done]
  exact Zkc.Source.Structured.LoopPresentation.foldCounted step
    (fun index count (_ : Unit) =>
      HonestProducerObservedLayers.producerCoefficients ctx site index (tail line index count))
    (by intro index value; cases value; rfl)
    (by
      intro index count value
      cases value
      rw [tail_succ, HonestProducerObservedLayers.producerCoefficients, ObservedLoop.forEach_cons]
      rfl)
    start count ()

theorem coefficients_observed (ctx : ProtocolContext) (separate : ctx.roles 1 ≠ ctx.roles 0)
    (site : String) (line : List F) (count : Nat) (bounded : count ≤ 4)
    (lineBound : line.length < indexLimit) :
    denoteRepeatOn (carriers := uniformCarriers F G) coefficientSpec ctx (ctx.roles 0) (some count)
      proverCoefficientState ((SourceRows.CoefficientCaptures.pack { line := some line }))
      (fun args => coefficientBody.denote (participantMeaningWithOn (ringModel F G) (.silent _)
        Occurrence.actions observedHelpers (ctx.roles 0) [] ctx Occurrence.iterations) args.get)
      Occurrence.iterations site =
      (HonestProducerObservedLayers.producerCoefficients ctx
        (qualifyProtocolSite ctx.applicationPrefix site) 0 (tail line 0 count)).bind
          (fun _ => .done proverCoefficientState) := by
  have repeated := Zkc.Source.Structured.LoopPresentation.present (carriers := uniformCarriers F G) coefficientSpec ctx (ctx.roles 0) (by simp)
    ((SourceRows.CoefficientCaptures.pack { line := some line }))
    (fun args => coefficientBody.denote (participantMeaningWithOn (ringModel F G) (.silent _)
      Occurrence.actions observedHelpers (ctx.roles 0) [] ctx Occurrence.iterations) args.get)
    Occurrence.iterations site (fun _ : Unit => proverCoefficientState)
    (fun _ => proverCoefficientState_masked ctx _ rfl)
    (fun _ index => (proverCoefficientProcess (G := G) ctx index (some line)).interpret Occurrence.actions)
    (by
      intro value index
      cases value
      erw [coefficient_occurrence (F := F) (G := G) ctx (ctx.roles 0) []
        ((SourceRows.CoefficientArguments.pack {
            index := some index,
            coefficients := none,
            line := some line
          })), proverCoefficient_process ctx _ rfl (.ofSeparate separate (by decide)) index (some line)]
      rw [PIR.Process.interpret_bind]
      rfl) count bounded _ () (proverCoefficientState_masked ctx _ rfl)
  rw [repeated, coefficient_fold_observed ctx _ line 0 count lineBound (by simp only [indexLimit]; omega)]


/-- The actual current source Rounds call equals the proved observed algorithm.
No transcript or helper-success premise is supplied. -/
theorem rounds_observed (ctx : ProtocolContext) (zero : ctx.roles 0 = 0) (one : ctx.roles 1 = 1)
    (count : Nat) (bounded : count ≤ 4) {n : Nat}
    (reference : GkrRoundsReference.State F (n + count)) (raw : RawState F)
    (decoded : Decodes raw reference) (capacity : 2 ^ (n + count) < indexLimit)
    (pending : Option (List F)) (claim : Option F) (service : Option Nat) :
    invokeProtocol (beforeRoot (F := F) (G := G)) GkrSourceBodies.roundsSignature ctx 0
      ((SourceRows.RoundsInputs.pack {
          add := some raw.add,
          mul := some raw.mul,
          left := some raw.left,
          right := some raw.right,
          pending := pending,
          claim := claim,
          count := some count,
          service := service
        })) =
      (HonestProducerOccurrences.producerRounds ctx
        (qualifyProtocolSite ctx.applicationPrefix (Generated.Presentations.Gkr.Rounds.roundSite.site)) 0 count reference raw []).bind
          (fun result => .done (SourceRows.roundsResult (values result.raw result.point))) := by
  rw [rounds_invocation ctx zero one]
  dsimp only [roundsPresentation, roundsPresentation_certificate, NormalForm.runsAtOn, NormalForm.meaningAtOn]
  simp only [zero]
  erw [OccurrencePresentation.closed_helper, HonestProducerRounds.empty_plain]
  simp only [PIR.Process.interpret, PIR.Process.bind, Values.get,
    NormalForm.runsAtOn, NormalForm.meaningAtOn, zero]
  have repeated := rounds_repeat (F := F) (G := G) ctx (by omega) (Generated.Presentations.Gkr.Rounds.roundSite.site) count bounded raw []
  repeat rw [zero] at repeated
  repeat rw [zero]
  erw [repeated, observed_rounds_fold ctx _ 0 count reference raw decoded capacity [], PIR.Process.bind_assoc]
  simp only [PIR.Process.bind_assoc, PIR.Process.bind]
  rfl

end ZkcSecurity.Realizations.Gkr.HonestProducerSource
