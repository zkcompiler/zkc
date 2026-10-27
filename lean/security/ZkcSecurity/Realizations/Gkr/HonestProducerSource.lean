module

public import ZkcSecurity.Realizations.Gkr.HonestProducerAlgorithm
public import ZkcSecurity.Realizations.Gkr.HonestProducerPackets
public import ZkcSecurity.Realizations.Gkr.HonestCircuitSource
public import ZkcSecurity.Realizations.Gkr.Encoding
public import ZkcExamples.Structured.GkrProverContinuation
public import Zkc.Source.TypedABI
public import ZkcSecurity.Realizations.Gkr.HonestProducerObserved

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
open ZkcExamples.Structured GkrSourceLaws SumcheckVerifierHelpers GkrSourceCallbacks
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

/-- Complete layer computation, including both actual source Rounds calls,
actual circuit-value helper, actual layout, actual line helper and every
coefficient readback. Capacity assumptions are runtime data bounds only. -/
theorem layer_source (ctx : ProtocolContext) (separate : ctx.roles 1 ≠ ctx.roles 0)
    (encoding : CircuitEncoding F) (shape : encoding.Shape) (index : Nat)
    (inside : index < encoding.layers) (point : List F) (pointSize : point.length = encoding.width)
    (widthBound : encoding.width ≤ 4) (layersBound : encoding.layers < indexLimit)
    (small : encoding.width + encoding.width + encoding.width + encoding.selector < 64)
    (addBound : encoding.add.length < indexLimit) (mulBound : encoding.mul.length < indexLimit)
    (roundCapacity : 2 ^ (encoding.width + encoding.width) < indexLimit)
    (lineCapacity : 2 ^ encoding.width * (encoding.width + 1) < indexLimit) :
    proverLayerProcess (G := G) ctx index (some encoding.inputs) (some encoding.add)
      (some encoding.mul) (some encoding.layers) (some encoding.selector) (some encoding.width)
      (some point) =
      (layer ctx encoding.circuit (encoding.layers - index - 1) index point).bind
        fun result => .done (some result) := by
  have belowDecoded := GkrRoundsLayout.decode_encode
    (encoding.circuit.wires (encoding.layers - index - 1) (index + 1))
  have position : index < 2 ^ encoding.selector := lt_of_lt_of_le inside shape.2.2.2
  have widthSmall : encoding.width + encoding.width + encoding.width < 64 := by omega
  have leftSeparate : (leftContext ctx).roles 1 ≠ (leftContext ctx).roles 0 := by
    simpa [leftContext, ProtocolContext.enter, roleSubstitution] using separate
  have rightSeparate : (rightContext ctx).roles 1 ≠ (rightContext ctx).roles 0 := by
    simpa [rightContext, ProtocolContext.enter, roleSubstitution] using separate
  have pointBound : encoding.width < indexLimit := by simp only [indexLimit]; omega
  have lineBound : encoding.width + 1 < indexLimit := by simp only [indexLimit]; omega
  have smaller : 2 ^ encoding.width < indexLimit :=
    (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)).trans_lt roundCapacity
  simp only [proverLayerProcess]
  rw [HonestCircuit.values_below_plain encoding.add encoding.mul encoding.inputs
    encoding.layers encoding.selector index encoding.circuit (add_stack encoding shape)
    (mul_stack encoding shape) (encoding.inputs_decode shape) shape.2.2.2 small layersBound inside]
  simp only [PIR.Process.bind, Values.get]
  rw [selectBlock_plain encoding.add index encoding.selector _ shape.2.1
      (by positivity) position addBound]
  simp only [PIR.Process.bind, Values.get]
  rw [selectBlock_plain encoding.mul index encoding.selector _ shape.2.2.1
      (by positivity) position mulBound]
  simp only [PIR.Process.bind, Values.get]
  rw [HonestHelpers.layout_plain (block encoding.add index (2 ^ (encoding.width + encoding.width + encoding.width)))
    (block encoding.mul index (2 ^ (encoding.width + encoding.width + encoding.width))) _ point (encoding.circuit.add index)
    (encoding.circuit.mul index) _ (encoding.add_decode shape index inside)
    (encoding.mul_decode shape index inside) belowDecoded pointSize widthSmall]
  simp only [PIR.Process.bind, Values.get]
  let reference := Circuit.factors encoding.circuit (encoding.layers - index - 1) index
    (coordinates encoding.width point)
  change (GkrRoundsNormalForms.proverRoundsProcess (leftContext ctx)
    (some (encode reference).add) (some (encode reference).mul)
    (some (encode reference).left) (some (encode reference).right) (some encoding.width)).bind _ = _
  rw [source_execute (leftContext ctx) leftSeparate encoding.width widthBound reference
    (encode reference) (encode_decodes reference) roundCapacity, PIR.Process.bind_assoc]
  simp only [PIR.Process.bind, returned, values, TypedABI.get_cons_here, TypedABI.get_cons_there]
  unfold layer
  dsimp only
  rw [PIR.Process.bind_assoc]
  apply (execute_yields (G := G) (leftContext ctx) encoding.width reference
    (encode reference) [] (encode_decodes reference)
    (Circuit.factors_admissible _ _ _ _)).bind_congr
  rintro left ⟨leftDecoded, leftAllowed, leftSuffix, leftPoint, leftSize, _⟩
  have leftLength : left.point.length = encoding.width := by simp_all
  let rightReference : GkrRoundsReference.State F (0 + encoding.width) :=
    (Nat.zero_add encoding.width).symm ▸ left.reference
  have rightDecoded := cast_decodes (Nat.zero_add encoding.width).symm left.reference left.raw leftDecoded
  have rightAllowed := cast_admissible (Nat.zero_add encoding.width).symm left.reference leftAllowed
  rw [source_execute (rightContext ctx) rightSeparate encoding.width widthBound rightReference
    left.raw rightDecoded (by simpa only [Nat.zero_add] using smaller), PIR.Process.bind_assoc]
  simp only [PIR.Process.bind, returned, values, TypedABI.get_cons_here]
  rw [PIR.Process.bind_assoc]
  apply (execute_yields (G := G) (rightContext ctx) encoding.width rightReference
    left.raw [] rightDecoded rightAllowed).bind_congr
  rintro right ⟨_, _, rightSuffix, rightPoint, rightSize, _⟩
  have rightLength : right.point.length = encoding.width := by simp_all
  rw [HonestLine.coefficients_plain encoding.width _ left.point right.point _ belowDecoded
    leftLength rightLength lineCapacity]
  simp only [PIR.Process.bind, Values.get]
  rw [HonestHelpers.element_plain _ 0 (by simpa only [row_length] using lineBound) (by decide)]
  simp only [PIR.Process.bind, line]
  congr 1
  funext _
  rw [coefficients ctx separate _ encoding.width widthBound (by simpa only [row_length] using lineBound)]
  simp only [PIR.Process.bind_assoc, PIR.Process.bind]
  apply congrArg (PIR.Process.bind _)
  funext _
  congr 1
  funext challenge
  rw [linePoint_plain left.point right.point challenge
    (by rw [leftLength, rightLength]) (by rw [leftLength]; exact pointBound)]
  rfl

theorem output_fold (ctx : ProtocolContext) (start count : Nat) (point : List F) :
    Finite.fold (fun result _ => proverOutputProcess (G := G) ctx result)
      (List.range' start count) (some point) =
      (output ctx count point).bind fun result => .done (some result) := by
  induction count generalizing start point with
  | zero => rfl
  | succ count ih =>
    rw [List.range'_succ, Finite.fold, HonestProducerPackets.output_point]
    simp only [PIR.Process.bind, output]
    congr 1
    funext r
    exact ih (start + 1) (point ++ [r])

theorem layers_fold (ctx : ProtocolContext) (separate : ctx.roles 1 ≠ ctx.roles 0)
    (encoding : CircuitEncoding F) (shape : encoding.Shape)
    (widthBound : encoding.width ≤ 4) (layersBound : encoding.layers < indexLimit)
    (small : encoding.width + encoding.width + encoding.width + encoding.selector < 64)
    (addBound : encoding.add.length < indexLimit) (mulBound : encoding.mul.length < indexLimit)
    (roundCapacity : 2 ^ (encoding.width + encoding.width) < indexLimit)
    (lineCapacity : 2 ^ encoding.width * (encoding.width + 1) < indexLimit)
    (index count : Nat) (inside : index + count ≤ encoding.layers)
    (point : List F) (pointSize : point.length = encoding.width) :
    Finite.fold (fun result index => proverLayerProcess (G := G) ctx index
        (some encoding.inputs) (some encoding.add) (some encoding.mul)
        (some encoding.layers) (some encoding.selector) (some encoding.width) result)
      (List.range' index count) (some point) =
      (layers ctx encoding index count point).bind fun result => .done (some result) := by
  induction count generalizing index point with
  | zero => rfl
  | succ count ih =>
    rw [List.range'_succ, Finite.fold, layer_source ctx separate encoding shape index (by omega)
      point pointSize widthBound layersBound small addBound mulBound roundCapacity lineCapacity]
    simp only [PIR.Process.bind_assoc, PIR.Process.bind, layers]
    apply (layer_yields ctx encoding.circuit (encoding.layers - index - 1) index point).bind_congr
    intro next nextSize
    exact ih (index + 1) (by omega) next nextSize


abbrev observedHelpers : Evaluation.ComponentTablesOn (uniformCarriers F G)
    (Occurrence.signature (uniformCarriers F G)) :=
  GkrSourceViews.unit.definitions.foldl
    (Evaluation.ComponentTablesOn.extend (ringModel F G) (.silent _)) ⟨[], []⟩
theorem helpers_interpret :
    Evaluation.ComponentTablesOn.Interprets (model := ringModel F G) Occurrence.actions
      (Zkc.Source.Structured.plainHelpers (F := F) (G := G) GkrSourceViews.unit).toOn
      observedHelpers := by
  unfold Zkc.Source.Structured.plainHelpers
  rw [Evaluation.ComponentTables.fold_toOn]
  exact Evaluation.ComponentTablesOn.fold_interpret _ (SiteObservations.silent_interpret _)
    (.empty _) _

theorem observed_helper (helper : Helper) (args : Values (assignment F G) helper.inputs) :
    invoke (observedHelpers (F := F) (G := G)).closed helper args =
      (invoke (Zkc.Source.Structured.plainHelpers (F := F) (G := G) GkrSourceViews.unit).closed helper args).interpret Occurrence.actions :=
  (helpers_interpret.closed helper args).symm

theorem round_callback (ctx : ProtocolContext) (self : Nat)
    (args : Values (Component (assignment F G))
      (.index :: (GkrRoundsNormalForms.roundSpec.state ++ GkrRoundsNormalForms.roundSpec.captures))) :
    GkrRoundsNormalForms.roundBody.denote
      (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions
        observedHelpers self [] ctx Occurrence.iterations) args.get =
      (GkrRoundsNormalForms.roundFn (F := F) (G := G) ctx self args).interpret Occurrence.actions := by
  change GkrRoundsNormalForms.roundBody.denote
      (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions
        observedHelpers self [] ctx .silent) args.get = _
  rw [GkrRoundsNormalForms.roundFn, denote_participantMeaningWith_eq]
  change _ = (GkrRoundsNormalForms.roundBody.denote
      (participantMeaningWithOn (ringModel F G) (.silent _) (participantActionsOn _)
        (Zkc.Source.Structured.plainHelpers GkrSourceViews.unit).toOn self [] ctx .silent) args.get).interpret _
  symm
  exact participant_denoteOn_interpret _ (SiteObservations.silent_interpret _)
    (fun _ => by rfl) helpers_interpret self _ args.get (.empty _) ctx
    (by constructor <;> intros <;> rfl)
omit [Field F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- The existing observed repeat retains its actual index and masks. -/
theorem observed_repeat {I : PIR.Signature} (spec : RepeatSpec) (ctx : ProtocolContext) (self : Nat)
    (inside : (spec.roles.map ctx.roles).contains self = true)
    (captures : Values (Component (assignment F G)) spec.captures)
    (body : RegionFunction (Component (assignment F G)) I
      (.index :: (spec.state ++ spec.captures), spec.state))
    (iterations : IterationObservations I) (site : String)
    {S : Type} (embed : S → Values (Component (assignment F G)) spec.state)
    (masked : ∀ value, maskValues self (ctx.mapScopes spec.stateScopes) (embed value) = embed value)
    (process : S → Nat → PIR.Process I S)
    (equation : ∀ value index, body (.cons (some index) ((embed value).append captures)) =
      (process value index).bind (fun result => .done (embed result)))
    (count : Nat) (bounded : count ≤ spec.maximum)
    (state : Values (Component (assignment F G)) spec.state) (initial : S)
    (start : maskValues self (ctx.mapScopes spec.stateScopes) state = embed initial) :
    denoteRepeatOn (carriers := uniformCarriers F G) spec ctx self (some count) state captures body iterations site =
      (Finite.fold (fun value index => iterations.within
        (qualifyProtocolSite ctx.applicationPrefix site) index (process value index))
        (List.range' 0 count) initial).bind (fun result => .done (embed result)) := by
  simp only [denoteRepeatOn, inside, bounded, ite_true, Finite.execute, Finite.Domain.admit,
    Finite.admitThen, List.range_eq_range', start]
  have fold (indices : List Nat) (value : S) :
      Finite.fold (fun state index => Repeat.stepOn spec ctx self captures body state index iterations site)
        indices (embed value) =
      (Finite.fold (fun value index => iterations.within
        (qualifyProtocolSite ctx.applicationPrefix site) index (process value index)) indices value).bind
        (fun result => .done (embed result)) := by
    induction indices generalizing value with
    | nil => rfl
    | cons index rest ih =>
      simp only [Finite.fold, Repeat.stepOn, masked, equation, IterationObservations.within_eq,
        PIR.Process.bind_assoc, PIR.Process.bind]
      apply congrArg (PIR.Process.bind _)
      funext _
      apply congrArg (PIR.Process.bind _)
      funext result
      apply congrArg (PIR.Process.bind _)
      funext _
      simpa only [Repeat.stepOn, IterationObservations.within_eq,
        PIR.Process.bind_assoc, PIR.Process.bind] using ih result
  exact fold _ initial

theorem output_callback (ctx : ProtocolContext) (self : Nat)
    (args : Values (Component (assignment F G))
      (.index :: (GkrSourceCallbacks.outputSpec.state ++ GkrSourceCallbacks.outputSpec.captures))) :
    GkrSourceCallbacks.outputBody.denote
      (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions
        observedHelpers self [] ctx Occurrence.iterations) args.get =
      (GkrSourceCallbacks.outputFn (F := F) (G := G) ctx self args).interpret Occurrence.actions := by
  change GkrSourceCallbacks.outputBody.denote
      (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions
        observedHelpers self [] ctx .silent) args.get = _
  rw [GkrSourceCallbacks.outputFn, denote_participantMeaningWith_eq]
  change _ = (GkrSourceCallbacks.outputBody.denote
      (participantMeaningWithOn (ringModel F G) (.silent _) (participantActionsOn _)
        (Zkc.Source.Structured.plainHelpers GkrSourceViews.unit).toOn self [] ctx .silent) args.get).interpret _
  symm
  exact participant_denoteOn_interpret _ (SiteObservations.silent_interpret _)
    (fun _ => by rfl) helpers_interpret self _ args.get (.empty _) ctx
    (by constructor <;> intros <;> rfl)

theorem coefficient_callback (ctx : ProtocolContext) (self : Nat)
    (args : Values (Component (assignment F G))
      (.index :: (GkrSourceCallbacks.coefficientSpec.state ++ GkrSourceCallbacks.coefficientSpec.captures))) :
    GkrSourceCallbacks.coefficientBody.denote
      (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions
        observedHelpers self [] ctx Occurrence.iterations) args.get =
      (GkrSourceCallbacks.coefficientFn (F := F) (G := G) ctx self args).interpret Occurrence.actions := by
  change GkrSourceCallbacks.coefficientBody.denote
      (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions
        observedHelpers self [] ctx .silent) args.get = _
  rw [GkrSourceCallbacks.coefficientFn, denote_participantMeaningWith_eq]
  change _ = (GkrSourceCallbacks.coefficientBody.denote
      (participantMeaningWithOn (ringModel F G) (.silent _) (participantActionsOn _)
        (Zkc.Source.Structured.plainHelpers GkrSourceViews.unit).toOn self [] ctx .silent) args.get).interpret _
  symm
  exact participant_denoteOn_interpret _ (SiteObservations.silent_interpret _)
    (fun _ => by rfl) helpers_interpret self _ args.get (.empty _) ctx
    (by constructor <;> intros <;> rfl)

abbrev beforeInput : ProtocolTable (assignment F G) (Occurrence.signature (uniformCarriers F G)) :=
  extendProtocolTableOn (ringModel F G) (.silent _) Occurrence.actions observedHelpers []
    GkrSourceViews.roundsDefinition Occurrence.iterations
abbrev beforeRoot : ProtocolTable (assignment F G) (Occurrence.signature (uniformCarriers F G)) :=
  extendProtocolTableOn (ringModel F G) (.silent _) Occurrence.actions observedHelpers beforeInput
    GkrSourceViews.sourceProtocol80Definition Occurrence.iterations

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
      (GkrRoundsNormalForms.roundsBody.denote
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
  erw [GkrSourceViews.roundsDefinition.body_eq_of_raw _ GkrRoundsNormalForms.roundsBody_raw]
  rfl


/-- The current source round callbacks, with each actual occurrence frame, compute
exactly the proved four-vector round algorithm for every received field value. -/
theorem observed_rounds_fold (ctx : ProtocolContext) (site : String) (start count : Nat) {n : Nat}
    (reference : GkrRoundsReference.State F (n + count)) (raw : Raw F)
    (decoded : Decodes raw reference) (capacity : 2 ^ (n + count) < indexLimit) (point : List F) :
    Finite.fold (fun result index => Occurrence.iterations.within site index
      ((GkrRoundsNormalForms.proverProcess (G := G) ctx result.1 result.2.1 result.2.2.1
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
      ((GkrRoundsNormalForms.proverProcess ctx (some raw.add) (some raw.mul)
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

def roundsPresentation (ctx : ProtocolContext) (add mul left right : Option (List F)) (count : Option Nat) :
    PIR.Process (Occurrence.signature (uniformCarriers F G))
      (Values (Component (assignment F G)) GkrRoundsNormalForms.roundsOutputs) :=
  (invoke (observedHelpers (F := F) (G := G)).closed GkrSourceBodies.emptyHelper .nil).bind fun empty =>
  (denoteRepeatOn (carriers := uniformCarriers F G) GkrRoundsNormalForms.roundSpec ctx 0 count
    (GkrRoundsNormalForms.proverState add mul left right (some (empty.get .here)))
    (.cons none .nil)
    (fun args => GkrRoundsNormalForms.roundBody.denote
      (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions observedHelpers 0 [] ctx Occurrence.iterations) args.get)
    Occurrence.iterations "s9").bind fun result =>
  .done (.cons (result.get (.there (.there (.there (.there .here)))))
    (.cons (result.get .here) (.cons (result.get (.there .here))
    (.cons (result.get (.there (.there .here))) (.cons (result.get (.there (.there (.there .here))))
    (.cons none (.cons none .nil)))))))

theorem rounds_presentation (ctx : ProtocolContext) (zero : ctx.roles 0 = 0) (one : ctx.roles 1 = 1)
    (add mul left right : Option (List F)) (count : Option Nat) :
  GkrRoundsNormalForms.roundsBody.denote
    (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions observedHelpers 0 [] ctx Occurrence.iterations)
    ((.cons add (.cons mul (.cons left (.cons right (.cons none (.cons none (.cons count (.cons none .nil)))))))) : Values (Component (assignment F G)) GkrRoundsNormalForms.roundsInputs).get =
    roundsPresentation (G := G) ctx add mul left right count := by
  simp [roundsPresentation, GkrRoundsNormalForms.roundsBody, Region.denote, participantMeaningWithOn,
    protocolOperationWithOn, SiteObservations.silent, PIR.Process.bind, Values.get,
    Operands.eval, Regions.denote, Environment.prepend, zero, one, Participant.owned, RoleFamily.sequence,
    GkrRoundsNormalForms.proverState, PIR.Process.bind_assoc, Values.absent,
    Values.present, Values.split, GkrRoundsNormalForms.roundState, Environment.push, ProtocolOp.results,
    GkrSourceBodies.sourceHelper40Helper, GkrSourceBodies.sourceHelper49Helper]
  apply congrArg (PIR.Process.bind _)
  funext empty
  cases empty with | cons point rest =>
    cases rest
    simp [Environment.prepend, Environment.push, Values.present, Values.get]
    apply congrArg (PIR.Process.bind _)
    funext result
    cases result with | cons a result =>
      cases result with | cons b result =>
        cases result with | cons c result =>
          cases result with | cons d result =>
            cases result with | cons e result =>
              cases result with | cons f result =>
                cases result with | cons g result =>
                  cases result
                  rfl


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
      ((.cons add (.cons mul (.cons left (.cons right (.cons pending (.cons claim (.cons count (.cons service .nil)))))))) : Values (Component (assignment F G)) GkrRoundsNormalForms.roundsInputs) =
      (.cons add (.cons mul (.cons left (.cons right (.cons none (.cons none (.cons count (.cons none .nil)))))))) := by
    iterate 9 unfold maskValues
    simp [ProtocolContext.mapScopes, GkrSourceBodies.roundsSignature,
      Participant.restrict, zero, one]
  rw [masked, rounds_presentation ctx zero one]
  unfold roundsPresentation
  simp only [PIR.Process.bind_assoc]
  apply congrArg (PIR.Process.bind _)
  funext empty
  apply congrArg (PIR.Process.bind _)
  funext result
  simp only [PIR.Process.bind]
  iterate 8 unfold maskValues
  simp [ProtocolContext.mapScopes, GkrSourceBodies.roundsSignature,
    Participant.restrict, zero, one]

/-- The observed repeat uses the same exact helper computation as the plain
callback. Each frame encloses precisely one complete round. -/
theorem rounds_repeat (ctx : ProtocolContext) (separate : ctx.roles 1 ≠ ctx.roles 0)
    (site : String) (count : Nat) (bounded : count ≤ 4)
    (raw : Raw F) (point : List F) :
    denoteRepeatOn (carriers := uniformCarriers F G) GkrRoundsNormalForms.roundSpec ctx (ctx.roles 0)
      (some count) (GkrRoundsNormalForms.proverState (some raw.add) (some raw.mul)
        (some raw.left) (some raw.right) (some point)) (.cons none .nil)
      (fun args => GkrRoundsNormalForms.roundBody.denote
        (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions observedHelpers
          (ctx.roles 0) [] ctx Occurrence.iterations) args.get)
      Occurrence.iterations site =
      (Finite.fold (fun result index => Occurrence.iterations.within
        (qualifyProtocolSite ctx.applicationPrefix site) index
        ((GkrRoundsNormalForms.proverProcess ctx result.1 result.2.1 result.2.2.1
          result.2.2.2.1 result.2.2.2.2).interpret Occurrence.actions))
        (List.range' 0 count) (values raw point)).bind fun result =>
          .done (GkrRoundsNormalForms.proverState result.1 result.2.1 result.2.2.1
            result.2.2.2.1 result.2.2.2.2) := by
  apply observed_repeat GkrRoundsNormalForms.roundSpec ctx (ctx.roles 0) (by simp) _ _ _ site
    (fun result : Result F => GkrRoundsNormalForms.proverState result.1 result.2.1 result.2.2.1
      result.2.2.2.1 result.2.2.2.2)
    (fun result => GkrRoundsNormalForms.proverState_masked ctx _ rfl _ _ _ _ _)
    _ _ count bounded _ (values raw point)
      (GkrRoundsNormalForms.proverState_masked ctx _ rfl _ _ _ _ _)
  intro result index
  rw [round_callback, GkrRoundsNormalForms.prover_process ctx _ rfl separate]
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
  have repeated := observed_repeat (F := F) (G := G) outputSpec ctx (ctx.roles 0) (by simp)
    (.cons none .nil)
    (fun args => outputBody.denote (participantMeaningWithOn (ringModel F G) (.silent _)
      Occurrence.actions observedHelpers (ctx.roles 0) [] ctx Occurrence.iterations) args.get)
    Occurrence.iterations site (fun point : List F => proverOutputState (some point))
    (fun point => proverOutputState_masked ctx _ rfl _) (fun point _ =>
      (output (G := G) ctx 1 point).interpret Occurrence.actions) (by
      intro point index
      rw [output_callback, proverOutput_process ctx _ rfl separate, HonestProducerPackets.output_point]
      rfl) count bounded _ point (proverOutputState_masked ctx _ rfl _)
  rw [repeated]
  have folded (start count : Nat) (point : List F) :
      Finite.fold (fun point index => Occurrence.iterations.within
        (qualifyProtocolSite ctx.applicationPrefix site) index
        ((output (G := G) ctx 1 point).interpret Occurrence.actions))
        (List.range' start count) point =
        HonestProducerObserved.producerOutput ctx (qualifyProtocolSite ctx.applicationPrefix site) start count point := by
    induction count generalizing start point with
    | zero => rfl
    | succ count ih =>
      rw [List.range'_succ, Finite.fold, HonestProducerObserved.producerOutput]
      apply congrArg (PIR.Process.bind _)
      funext next
      exact ih (start + 1) next
  rw [folded]

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
  have repeated := observed_repeat (F := F) (G := G) coefficientSpec ctx (ctx.roles 0) (by simp)
    (.cons (some line) .nil)
    (fun args => coefficientBody.denote (participantMeaningWithOn (ringModel F G) (.silent _)
      Occurrence.actions observedHelpers (ctx.roles 0) [] ctx Occurrence.iterations) args.get)
    Occurrence.iterations site (fun _ : Unit => proverCoefficientState)
    (fun _ => proverCoefficientState_masked ctx _ rfl)
    (fun _ index => (proverCoefficientProcess (G := G) ctx index (some line)).interpret Occurrence.actions)
    (by
      intro value index
      cases value
      rw [coefficient_callback, proverCoefficient_process ctx _ rfl separate]
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
  rw [rounds_invocation ctx zero one, roundsPresentation, observed_helper, HonestProducerRounds.empty_plain]
  simp only [PIR.Process.interpret, PIR.Process.bind, Values.get]
  have repeated := rounds_repeat (F := F) (G := G) ctx (by omega) "s9" count bounded raw []
  rw [zero] at repeated
  rw [repeated, observed_rounds_fold ctx _ 0 count reference raw decoded capacity [], PIR.Process.bind_assoc]
  simp only [PIR.Process.bind_assoc, PIR.Process.bind]
  rfl

theorem producer_source (encoding : CircuitEncoding F) (outputs : List F)
    (admitted : encoding.Admitted 4 4 outputs) :
    GkrSourceViews.program.participant F G 0
      (GkrProverContinuation.inputs (G := G) encoding.inputs encoding.add encoding.mul
        encoding.layers encoding.selector encoding.width) = producer {} encoding := by
  obtain ⟨shape, _, widthBound, layersBound, dimension⟩ := admitted
  have layersSmall : encoding.layers < indexLimit := lt_of_le_of_lt layersBound (by decide)
  have addBound : encoding.add.length < indexLimit := by
    rw [shape.2.1, ← Nat.pow_add]
    apply Nat.pow_lt_pow_right (by decide)
    omega
  have mulBound : encoding.mul.length < indexLimit := by
    rw [shape.2.2.1, ← Nat.pow_add]
    apply Nat.pow_lt_pow_right (by decide)
    omega
  have roundsCapacity : 2 ^ (encoding.width + encoding.width) < indexLimit := by
    apply Nat.pow_lt_pow_right (by decide)
    omega
  have lineCapacity : 2 ^ encoding.width * (encoding.width + 1) < indexLimit := by
    have : 2 ^ encoding.width ≤ 2 ^ 4 := Nat.pow_le_pow_right (by decide) widthBound
    calc
      _ ≤ 16 * 5 := Nat.mul_le_mul this (by omega)
      _ < indexLimit := by decide
  rw [GkrProverContinuation.participant]
  unfold GkrProverContinuation.process
  rw [GkrSourceContinuation.empty_plain]
  simp only [PIR.Process.bind, Values.get]
  erw [proverOutput_fold {} (by decide) none encoding.width widthBound _ (some [])
    (proverOutputState_masked {} 0 rfl (some [])), output_fold]
  simp only [PIR.Process.bind_assoc, PIR.Process.bind]
  unfold producer
  apply (output_yields (G := G) {} encoding.width []).bind_congr
  intro point size
  have pointSize : point.length = encoding.width := by simpa using size
  erw [proverLayer_fold {} (by decide) _ _ _ _ _ _ _ encoding.layers layersBound _ (some point)
    (proverLayerState_masked {} 0 rfl (some point))]
  rw [layers_fold {} (by decide) encoding shape widthBound layersSmall (by omega) addBound mulBound
    roundsCapacity lineCapacity 0 encoding.layers (by omega) point pointSize]
  simp only [PIR.Process.bind_assoc, PIR.Process.bind]

end ZkcSecurity.Realizations.Gkr.HonestProducerSource
