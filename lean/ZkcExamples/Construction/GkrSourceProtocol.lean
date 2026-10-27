module

public import ZkcExamples.Structured.GkrSourceVerifier
public import Zkc.Construction.Compiled
public import ZkcExamples.Construction.GkrProofParticipant

@[expose] public section

/-! All-input source forms of the full GKR verifier. Helpers retain their exact
closed source invocation, including every stop. Reference-table validity and
honest bounds play no role in these equations. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
namespace ZkcExamples.Construction.GkrSourceProtocol
open Zkc Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcExamples.Structured
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

abbrev program := GkrSourceViews.program
abbrev imported := GkrSourceViews.imported
abbrev artifact := GkrProofParticipant.participant

def context : Context := .fiatShamir
  "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2"
  ["role00000000", "role00000001"] 0 1 7 "random.bls12-381.fr/0"
  (some (.draw "bls12-381.fr")) "merlin3.bls12-381.fr64be/0"
  [("label_6f7574707574", "label_6f75747075745f64656c6976657279_0"),
   ("apply_14_label_6c656674_label_6368616c6c656e6765", "apply_14_label_6c656674_label_64656c6976657279_0"),
   ("apply_16_label_7269676874_label_6368616c6c656e6765", "apply_16_label_7269676874_label_64656c6976657279_0"),
   ("label_6c696e655f6368616c6c656e6765", "label_6c696e655f64656c6976657279_0")]

theorem checked : Construction.checkCompiled imported artifact = .ok () := by decide +kernel
theorem context_checked : exportContext GkrSourceData.snapshot artifact = some context := by decide +kernel

def sourceInputs (inputs outputs add mul : List F) (layers selector width handle : Nat) :
    Values (Component (assignment F G)) program.payload.entry.inputs :=
  .cons (some inputs) (.cons (some outputs) (.cons (some add) (.cons (some mul)
    (.cons (some layers) (.cons (some selector) (.cons (some width) (.cons (some handle) .nil)))))))

def sourceVerifier (inputs outputs add mul : List F) (layers selector width handle : Nat) :
    PIR.Process (Actions F G) (Option Bool) :=
  ((program.participant F G 1 (sourceInputs inputs outputs add mul layers selector width handle)).bind
    fun result => .done (result.get .here)).interpret CommonAdapter.project

def helper (entry : Helper) (args : Values (assignment F G) entry.inputs) :
    PIR.Process (Actions F G) (Values (assignment F G) entry.outputs) :=
  (invoke (GkrSourceVerifier.closed (F := F) (G := G)) entry args).interpret CommonAdapter.project

def rounds (ctx : ProtocolContext) (handle count : Nat) (claim : F) :
    PIR.Process (Actions F G) (List F × F) :=
  if count ≤ 4 then GkrVerifier.rounds ctx handle count claim else .halt .refused

theorem rounds_source (ctx : ProtocolContext) (separate : ctx.roles 0 ≠ ctx.roles 1)
    (handle count : Nat) (claim : F) :
    (GkrRoundsNormalForms.verifierRoundsProcess (F := F) (G := G) ctx (some claim)
      (some count) (some handle)).interpret CommonAdapter.project =
      (rounds ctx handle count claim).bind fun result => .done (GkrSourceVerifier.roundsResults result) := by
  by_cases bounded : count ≤ 4
  · simpa only [rounds, bounded, ite_true] using
      GkrSourceVerifier.rounds_reads ctx separate handle count bounded claim
  · simp only [GkrRoundsNormalForms.verifierRoundsProcess, GkrSourceVerifier.empty_plain,
      PIR.Process.bind, Values.get, rounds, bounded, ite_false,
      denoteRepeat, denoteRepeatOn, GkrRoundsNormalForms.repeatSpec,
      List.map_cons, List.map_nil, List.contains_cons, List.contains_nil,
      beq_self_eq_true, Bool.or_true, Bool.true_or, ↓reduceIte, PIR.Process.interpret]

def coefficients (ctx : ProtocolContext) (width : Nat) (initial : List F) :
    PIR.Process (Actions F G) (List F) :=
  if width ≤ 4 then PIR.repeatN width (GkrVerifier.lineCoefficient ctx) initial else .halt .refused

theorem coefficients_source (ctx : ProtocolContext) (separate : ctx.roles 0 ≠ ctx.roles 1)
    (width : Nat) (initial : List F) :
    ((denoteRepeat GkrSourceNormalForms.coefficientSpec ctx (ctx.roles 1) (some width)
      (.cons (some initial) .nil) (.cons none .nil)
      (GkrSourceNormalForms.coefficientFn (F := F) (G := G) ctx (ctx.roles 1))).bind
        fun result => .done (result.get .here)).interpret CommonAdapter.project =
      (coefficients ctx width initial).bind fun result => .done (some result) := by
  by_cases bounded : width ≤ 4
  · rw [GkrSourceNormalForms.verifierCoefficient_fold ctx separate none width bounded
      (.cons (some initial) .nil) (some initial)
      (GkrSourceNormalForms.verifierCoefficientState_masked ctx _ rfl (some initial))]
    rw [Finite.fold_range_repeatN _ 0 width]
    simp only [PIR.Process.bind_assoc, PIR.Process.bind, Values.get, PIR.Process.interpret_bind]
    rw [GkrSourceVerifier.repeatN_reads CommonAdapter.project _ (GkrVerifier.lineCoefficient ctx)
      some (fun state => GkrSourceVerifier.coefficient_reads ctx state) width initial]
    simp only [coefficients, bounded, ite_true, PIR.Process.bind_assoc, PIR.Process.bind, GkrSourceNormalForms.verifierCoefficientState, Values.get, PIR.Process.interpret]
  · simp only [coefficients, bounded, ite_false, denoteRepeat, denoteRepeatOn,
      GkrSourceNormalForms.coefficientSpec, GkrSourceNormalForms.coefficientMaximum,
      List.map_cons, List.map_nil, List.contains_cons, List.contains_nil,
      beq_self_eq_true, Bool.or_true, Bool.true_or, ↓reduceIte, PIR.Process.bind, PIR.Process.interpret]

def layer (ctx : ProtocolContext) (index handle selector width : Nat)
    (add mul point : List F) (claim : F) : PIR.Process (Actions F G) (List F × F) :=
  (rounds (GkrSourceNormalForms.leftContext ctx) handle width claim).bind fun left =>
  (rounds (GkrSourceNormalForms.rightContext ctx) handle width left.2).bind fun right =>
  .call (.receive (.field "bls12-381.fr") (GkrSourceNormalForms.lineConstantSite ctx) (ctx.roles 0)) fun first =>
  (coefficients ctx width [first]).bind fun line =>
  (helper GkrSourceBodies.sumHelper (.cons line .nil)).bind fun total =>
  (helper GkrSourceBodies.selectBlockHelper (.cons add (.cons index (.cons selector .nil)))).bind fun addBlock =>
  (helper GkrSourceBodies.evaluateWiringHelper (.cons (addBlock.get .here)
    (.cons point (.cons left.1 (.cons right.1 .nil))))).bind fun addValue =>
  (helper GkrSourceBodies.selectBlockHelper (.cons mul (.cons index (.cons selector .nil)))).bind fun mulBlock =>
  (helper GkrSourceBodies.evaluateWiringHelper (.cons (mulBlock.get .here)
    (.cons point (.cons left.1 (.cons right.1 .nil))))).bind fun mulValue =>
  if right.2 = (addValue.get .here) * (first + total.get .here) +
      (mulValue.get .here) * first * total.get .here then
    .call (.query (GkrSourceNormalForms.lineChallengeSite ctx) "bls12-381.fr" (.cons handle .nil)) fun challenge =>
    .call (.send (ty := .field "bls12-381.fr") (GkrSourceNormalForms.lineDeliverySite ctx)
      (ctx.roles 0) challenge) fun _ =>
    (helper GkrSourceBodies.evaluateCoefficientsHelper (.cons line (.cons challenge .nil))).bind fun value =>
    (helper GkrSourceBodies.linePointHelper (.cons left.1 (.cons right.1 (.cons challenge .nil)))).bind fun next =>
    .done (next.get .here, value.get .here)
  else .halt .reject

theorem layer_source (ctx : ProtocolContext) (separate : ctx.roles 0 ≠ ctx.roles 1)
    (index handle selector width : Nat) (add mul point : List F) (claim : F) :
    (GkrSourceNormalForms.verifierLayerProcess (F := F) (G := G) ctx index (some add) (some mul)
      (some selector) (some width) (some handle) (some point) (some claim)).interpret CommonAdapter.project =
      (layer ctx index handle selector width add mul point claim).bind fun result =>
        .done (some result.1, some result.2) := by
  have leftSeparate : (GkrSourceNormalForms.leftContext ctx).roles 0 ≠
      (GkrSourceNormalForms.leftContext ctx).roles 1 := by simpa [GkrSourceNormalForms.leftContext, GkrSourceNormalForms.rightContext, ProtocolContext.enter, roleSubstitution] using separate
  have rightSeparate : (GkrSourceNormalForms.rightContext ctx).roles 0 ≠
      (GkrSourceNormalForms.rightContext ctx).roles 1 := by simpa [GkrSourceNormalForms.leftContext, GkrSourceNormalForms.rightContext, ProtocolContext.enter, roleSubstitution] using separate
  simp only [GkrSourceNormalForms.verifierLayerProcess, PIR.Process.interpret_bind,
    rounds_source _ leftSeparate, rounds_source _ rightSeparate,
    PIR.Process.bind_assoc, PIR.Process.bind, GkrSourceVerifier.roundsResults, Values.get,
    PIR.Process.interpret, CommonAdapter.project, GkrSourceVerifier.empty_plain,
    GkrSourceVerifier.append_plain, List.nil_append, layer, helper]
  congr 1
  funext left
  congr 1
  funext right
  congr 1
  funext first
  have coefficient := coefficients_source (F := F) (G := G) ctx separate width [first]
  have coefficient' := congrArg (fun process => process.bind fun coefficients =>
    match coefficients with
    | none => (.halt .incomplete : PIR.Process (Actions F G) (Option (List F) × Option F))
    | some line => ((helper GkrSourceBodies.sumHelper (.cons line .nil)).bind fun total =>
        (helper GkrSourceBodies.selectBlockHelper (.cons add (.cons index (.cons selector .nil)))).bind fun addBlock =>
        (helper GkrSourceBodies.evaluateWiringHelper (.cons (addBlock.get .here) (.cons point (.cons left.1 (.cons right.1 .nil))))).bind fun addValue =>
        (helper GkrSourceBodies.selectBlockHelper (.cons mul (.cons index (.cons selector .nil)))).bind fun mulBlock =>
        (helper GkrSourceBodies.evaluateWiringHelper (.cons (mulBlock.get .here) (.cons point (.cons left.1 (.cons right.1 .nil))))).bind fun mulValue =>
        if right.2 = (addValue.get .here) * (first + total.get .here) + (mulValue.get .here) * first * total.get .here then
          .call (.query (GkrSourceNormalForms.lineChallengeSite ctx) "bls12-381.fr" (.cons handle .nil)) fun challenge =>
          .call (.send (ty := .field "bls12-381.fr") (GkrSourceNormalForms.lineDeliverySite ctx) (ctx.roles 0) challenge) fun _ =>
          (helper GkrSourceBodies.evaluateCoefficientsHelper (.cons line (.cons challenge .nil))).bind fun value =>
          (helper GkrSourceBodies.linePointHelper (.cons left.1 (.cons right.1 (.cons challenge .nil)))).bind fun next =>
          .done (some (next.get .here), some (value.get .here))
        else .halt .reject)) coefficient
  convert coefficient' using 1 <;>
    simp only [PIR.Process.interpret_bind, PIR.Process.bind_assoc, PIR.Process.bind,
      PIR.Process.interpret, helper, GkrSourceVerifier.closed, CommonAdapter.project,
      scalarDomain]
  · congr 1
    funext result
    cases result.get .here <;> simp only [PIR.Process.interpret, PIR.Process.interpret_bind]
    congr 1
    funext total
    congr 1
    funext addBlock
    congr 1
    funext addValue
    congr 1
    funext mulBlock
    congr 1
    funext mulValue
    split <;> simp only [PIR.Process.interpret, CommonAdapter.project, PIR.Process.bind,
      PIR.Process.interpret_bind, scalarDomain]
  · congr 1
    funext line
    congr 1
    funext total
    congr 1
    funext addBlock
    congr 1
    funext addValue
    congr 1
    funext mulBlock
    congr 1
    funext mulValue
    split <;> simp only [PIR.Process.bind]
    simp only [PIR.Process.bind, PIR.Process.bind_assoc]


theorem finite_reads {I J : PIR.Signature} {Item S T : Type}
    (operations : PIR.OperationInterpretation I J)
    (source : S → Item → PIR.Process I S) (target : T → Item → PIR.Process J T)
    (embed : T → S)
    (same : ∀ state item, (source (embed state) item).interpret operations =
      (target state item).bind fun next => .done (embed next))
    (items : List Item) (initial : T) :
    (Finite.fold source items (embed initial)).interpret operations =
      (Finite.fold target items initial).bind fun result => .done (embed result) := by
  induction items generalizing initial with
  | nil => rfl
  | cons item rest ih =>
      simp only [Finite.fold, PIR.Process.interpret_bind, same,
        PIR.Process.bind_assoc, PIR.Process.bind]
      congr 1
      funext next
      exact ih next

def output (ctx : ProtocolContext) (handle count : Nat) (point : List F) :
    PIR.Process (Actions F G) (List F) :=
  if count ≤ 4 then PIR.repeatN count (GkrVerifier.outputRound ctx handle) point else .halt .refused

theorem output_source (ctx : ProtocolContext) (separate : ctx.roles 0 ≠ ctx.roles 1)
    (handle count : Nat) (point : List F) :
    (denoteRepeat GkrSourceNormalForms.outputSpec ctx (ctx.roles 1) (some count)
      (.cons (some point) (.cons none .nil)) (.cons (some handle) .nil)
      (GkrSourceNormalForms.outputFn (F := F) (G := G) ctx (ctx.roles 1))).interpret CommonAdapter.project =
      (output ctx handle count point).bind fun result =>
        .done (GkrSourceNormalForms.verifierOutputState (some result)) := by
  by_cases bounded : count ≤ 4
  · rw [GkrSourceNormalForms.verifierOutput_fold ctx separate (some handle) count bounded
      (.cons (some point) (.cons none .nil)) (some point)
      (GkrSourceNormalForms.verifierOutputState_masked ctx _ rfl (some point))]
    rw [Finite.fold_range_repeatN _ 0 count]
    simp only [PIR.Process.interpret_bind]
    rw [GkrSourceVerifier.repeatN_reads CommonAdapter.project _ (GkrVerifier.outputRound ctx handle)
      some (GkrSourceVerifier.output_reads ctx handle) count point]
    simp only [output, bounded, ite_true, PIR.Process.bind_assoc, PIR.Process.bind, PIR.Process.interpret]
  · simp only [denoteRepeat, denoteRepeatOn, GkrSourceNormalForms.outputSpec, output,
      GkrSourceNormalForms.outputMaximum, bounded, ite_false,
      List.map_cons, List.map_nil, List.contains_cons, List.contains_nil,
      beq_self_eq_true, Bool.or_true, Bool.true_or, ↓reduceIte, PIR.Process.bind, PIR.Process.interpret]

def layers (ctx : ProtocolContext) (handle selector width count : Nat)
    (add mul : List F) (state : List F × F) : PIR.Process (Actions F G) (List F × F) :=
  if count ≤ 4 then Finite.fold (fun state index =>
    layer ctx index handle selector width add mul state.1 state.2) (List.range' 0 count) state
  else .halt .refused

theorem layers_source (ctx : ProtocolContext) (separate : ctx.roles 0 ≠ ctx.roles 1)
    (handle selector width count : Nat) (inputs add mul point : List F) (claim : F) :
    (denoteRepeat GkrSourceNormalForms.layerSpec ctx (ctx.roles 1) (some count)
      (GkrSourceNormalForms.verifierLayerState (some point) (some claim))
      (.cons (some inputs) (.cons (some add) (.cons (some mul) (.cons (some count)
        (.cons (some selector) (.cons (some width) (.cons (some handle) .nil)))))))
      (GkrSourceNormalForms.layerFn (F := F) (G := G) ctx (ctx.roles 1))).interpret CommonAdapter.project =
      (layers ctx handle selector width count add mul (point, claim)).bind fun result =>
        .done (GkrSourceNormalForms.verifierLayerState (some result.1) (some result.2)) := by
  by_cases bounded : count ≤ 4
  · rw [GkrSourceNormalForms.verifierLayer_fold ctx separate (some inputs) (some add) (some mul)
      (some count) (some selector) (some width) (some handle) count bounded _ (some point, some claim)
      (GkrSourceNormalForms.verifierLayerState_masked ctx _ rfl (some point) (some claim))]
    simp only [PIR.Process.interpret_bind]
    have foldLaw := finite_reads CommonAdapter.project
      (fun (state : Option (List F) × Option F) index =>
        GkrSourceNormalForms.verifierLayerProcess (F := F) (G := G) ctx index (some add) (some mul)
          (some selector) (some width) (some handle) state.1 state.2)
      (fun (state : List F × F) index => layer ctx index handle selector width add mul state.1 state.2)
      (fun (state : List F × F) => (some state.1, some state.2))
      (fun state index => layer_source ctx separate index handle selector width add mul state.1 state.2)
      (List.range' 0 count) (point, claim)
    rw [foldLaw]
    simp only [layers, bounded, ite_true, PIR.Process.bind_assoc, PIR.Process.bind, PIR.Process.interpret]
  · simp only [denoteRepeat, denoteRepeatOn, GkrSourceNormalForms.layerSpec, layers,
      GkrSourceNormalForms.layerMaximum, bounded, ite_false,
      List.map_cons, List.map_nil, List.contains_cons, List.contains_nil,
      beq_self_eq_true, Bool.or_true, Bool.true_or, ↓reduceIte, PIR.Process.bind, PIR.Process.interpret]

def verifier (inputs outputs add mul : List F) (count selector width handle : Nat) :
    PIR.Process (Actions F G) Bool :=
  (output {} handle width []).bind fun point =>
  (helper GkrSourceBodies.evaluateHelper (.cons outputs (.cons point .nil))).bind fun initial =>
  (layers {} handle selector width count add mul (point, initial.get .here)).bind fun state =>
  (helper GkrSourceBodies.evaluateHelper (.cons inputs (.cons state.1 .nil))).bind fun final =>
  .done (decide (final.get .here = state.2))

theorem source_equation (inputs outputs add mul : List F) (count selector width handle : Nat) :
    sourceVerifier (F := F) (G := G) inputs outputs add mul count selector width handle =
      (verifier inputs outputs add mul count selector width handle).bind fun decision => .done (some decision) := by
  unfold sourceVerifier sourceInputs
  rw [GkrSourceNormalForms.verifier_participant]
  simp only [GkrSourceNormalForms.verifierProcess, GkrSourceVerifier.empty_plain,
    PIR.Process.bind, Values.get, PIR.Process.bind_assoc, PIR.Process.interpret_bind]
  rw [output_source {} (by decide)]
  simp only [PIR.Process.bind_assoc, PIR.Process.bind, GkrSourceNormalForms.verifierOutputState, Values.get,
    PIR.Process.interpret]
  unfold verifier helper
  simp only [PIR.Process.bind_assoc]
  congr 1
  funext point
  simp only [PIR.Process.interpret_bind, PIR.Process.bind_assoc, Values.get]
  congr 1
  funext initial
  change ((denoteRepeat GkrSourceNormalForms.layerSpec {} 1 (some count)
    (GkrSourceNormalForms.verifierLayerState (some point) (some (initial.get .here)))
    (.cons (some inputs) (.cons (some add) (.cons (some mul) (.cons (some count)
      (.cons (some selector) (.cons (some width) (.cons (some handle) .nil)))))))
    (GkrSourceNormalForms.layerFn (F := F) (G := G) {} 1)).interpret CommonAdapter.project).bind _ = _
  erw [layers_source {} (by decide) handle selector width count inputs add mul point (initial.get .here)]
  simp only [PIR.Process.bind_assoc, PIR.Process.bind, GkrSourceNormalForms.verifierLayerState, Values.get,
    PIR.Process.interpret, PIR.Process.interpret_bind]
  rfl

end ZkcExamples.Construction.GkrSourceProtocol
