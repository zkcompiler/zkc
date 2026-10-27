module

public import ZkcExamples.Structured.GkrSourceVerifier
public import ZkcExamples.Structured.GkrRootNormalForms
public import Zkc.Construction.Compiled
public import ZkcExamples.Construction.GkrProofParticipant
public meta import Mathlib.Tactic.FailIfNoProgress

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
  (invoke (GkrRoundsReading.closed (F := F) (G := G)) entry args).interpret CommonAdapter.project

def rounds (ctx : ProtocolContext) (handle count : Nat) (point : List F) (claim : F) :
    PIR.Process (Actions F G) (List F × F) :=
  if count ≤ 4 then PIR.repeatN count (GkrVerifier.round ctx handle) (point, claim)
  else .halt .refused

theorem rounds_source (ctx : ProtocolContext) (separate : ctx.roles 0 ≠ ctx.roles 1)
    (handle count : Nat) (point : List F) (claim : F) :
    (GkrRoundsNormalForms.verifierRoundsProcess (F := F) (G := G) ctx (some point)
      (some claim) (some count) (some handle)).interpret CommonAdapter.project =
      (rounds ctx handle count point claim).bind fun result => .done (GkrRoundsReading.roundsResults result) := by
  by_cases bounded : count ≤ 4
  · rw [GkrRoundsReading.reads ctx separate handle count bounded point claim]
    simp only [rounds, bounded, ite_true]
    have prefixed := GkrRoundsReading.repeat_prefix (G := G) ctx handle count point ([], claim)
    simp only [List.append_nil] at prefixed
    rw [prefixed, PIR.Process.bind_assoc]
    rfl
  · simp only [GkrRoundsNormalForms.verifierRoundsProcess,
      GkrRoundsReading.tuple40_plain, PIR.Process.bind, Values.get_cons,
      rounds, bounded, ite_false, denoteRepeat, denoteRepeatOn,
      GkrRoundsNormalForms.roundSpec, List.map_cons, List.map_nil,
      List.contains_cons, List.contains_nil, beq_self_eq_true, Bool.or_true,
      Bool.true_or, ↓reduceIte, PIR.Process.interpret]

def coefficients (ctx : ProtocolContext) (width : Nat) (initial : List F) :
    PIR.Process (Actions F G) (List F) :=
  if width ≤ 4 then PIR.repeatN width (GkrVerifier.lineCoefficient ctx) initial else .halt .refused

theorem coefficients_source (ctx : ProtocolContext) (separate : ctx.roles 0 ≠ ctx.roles 1)
    (width : Nat) (initial : List F) :
    ((denoteRepeat GkrSourceCallbacks.coefficientSpec ctx (ctx.roles 1) (some width)
      (.cons (some initial) .nil) (.cons none .nil)
      (GkrSourceCallbacks.coefficientFn (F := F) (G := G) ctx (ctx.roles 1))).bind
        fun result => .done (result.get .here)).interpret CommonAdapter.project =
      (coefficients ctx width initial).bind fun result => .done (some result) := by
  by_cases bounded : width ≤ 4
  · rw [GkrSourceCallbacks.verifierCoefficient_fold ctx separate none width bounded
      (.cons (some initial) .nil) (some initial)
      (GkrSourceCallbacks.verifierCoefficientState_masked ctx _ rfl (some initial))]
    rw [Finite.fold_range_repeatN _ 0 width]
    simp only [PIR.Process.bind_assoc, PIR.Process.bind, Values.get, PIR.Process.interpret_bind]
    rw [GkrRoundsReading.repeatN_reads CommonAdapter.project _ (GkrVerifier.lineCoefficient ctx)
      some (fun state => GkrLayerReading.coefficient_reads ctx state) width initial]
    simp only [coefficients, bounded, ite_true, PIR.Process.bind_assoc, PIR.Process.bind, GkrSourceCallbacks.verifierCoefficientState, Values.get, PIR.Process.interpret]
  · simp only [coefficients, bounded, ite_false, denoteRepeat, denoteRepeatOn,
      GkrSourceCallbacks.coefficientSpec, GkrSourceCallbacks.coefficientMaximum,
      List.map_cons, List.map_nil, List.contains_cons, List.contains_nil,
      beq_self_eq_true, Bool.or_true, Bool.true_or, ↓reduceIte, PIR.Process.bind, PIR.Process.interpret]

def afterCoefficients (ctx : ProtocolContext) (index handle selector : Nat)
    (add mul : List F)
    (current combined : Values (assignment F G) [.vector "bls12-381.fr", .field "bls12-381.fr"])
    (split : Values (assignment F G) [.vector "bls12-381.fr", .vector "bls12-381.fr"])
    (first : F) (line : List F) : PIR.Process (Actions F G) (List F × F) :=
  (helper GkrSourceBodies.sumHelper (.cons line .nil)).bind fun total =>
  (helper GkrSourceBodies.selectBlockHelper (.cons add (.cons index (.cons selector .nil)))).bind fun addBlock =>
  (helper GkrSourceBodies.evaluateWiringHelper (.cons (addBlock.get .here)
    (.cons (current.get .here) (.cons (split.get .here) (.cons (split.get (.there .here)) .nil))))).bind fun addValue =>
  (helper GkrSourceBodies.selectBlockHelper (.cons mul (.cons index (.cons selector .nil)))).bind fun mulBlock =>
  (helper GkrSourceBodies.evaluateWiringHelper (.cons (mulBlock.get .here)
    (.cons (current.get .here) (.cons (split.get .here) (.cons (split.get (.there .here)) .nil))))).bind fun mulValue =>
  if combined.get (.there .here) = (addValue.get .here) * (first + total.get .here) +
      (mulValue.get .here) * first * total.get .here then
    .call (.query (GkrSourceCallbacks.lineChallengeSite ctx) "bls12-381.fr" (.cons handle .nil)) fun challenge =>
    .call (.send (ty := .field "bls12-381.fr") (GkrSourceCallbacks.lineDeliverySite ctx)
      (ctx.roles 0) challenge) fun _ =>
    (helper GkrSourceBodies.linePointHelper (.cons (split.get .here)
      (.cons (split.get (.there .here)) (.cons challenge .nil)))).bind fun next =>
    (helper GkrSourceBodies.evaluateCoefficientsHelper (.cons line (.cons challenge .nil))).bind fun value =>
    (helper GkrSourceBodies.sourceHelper19Helper (.cons (next.get .here)
      (.cons (value.get .here) .nil))).bind fun packed =>
    .done (packed.get .here, packed.get (.there .here))
  else .halt .reject

def layer (ctx : ProtocolContext) (index handle selector width : Nat)
    (add mul point : List F) (claim : F) : PIR.Process (Actions F G) (List F × F) :=
  (helper GkrSourceBodies.sourceHelper20Helper (.cons point (.cons claim .nil))).bind fun current =>
  (helper GkrSourceBodies.sourceHelper37Helper (.cons (current.get (.there .here)) .nil)).bind fun pending =>
  (rounds (GkrSourceCallbacks.leftContext ctx) handle width (pending.get .here)
    (pending.get (.there .here))).bind fun left =>
  (rounds (GkrSourceCallbacks.rightContext ctx) handle width left.1 left.2).bind fun right =>
  (helper GkrSourceBodies.sourceHelper40Helper (.cons right.1 (.cons right.2 .nil))).bind fun combined =>
  (helper GkrSourceBodies.sourceHelper50Helper (.cons (combined.get .here) .nil)).bind fun split =>
  .call (.receive (.field "bls12-381.fr") (GkrSourceCallbacks.lineConstantSite ctx) (ctx.roles 0)) fun first =>
  (coefficients ctx width [first]).bind fun line =>
  afterCoefficients ctx index handle selector add mul current combined split first line

theorem layer_source (ctx : ProtocolContext) (separate : ctx.roles 0 ≠ ctx.roles 1)
    (index handle selector width : Nat) (add mul point : List F) (claim : F) :
    (GkrSourceCallbacks.verifierLayerProcess (F := F) (G := G) ctx index (some add) (some mul)
      (some selector) (some width) (some handle) (some point) (some claim)).interpret CommonAdapter.project =
      (layer ctx index handle selector width add mul point claim).bind fun result =>
        .done (some result.1, some result.2) := by
  have leftSeparate : (GkrSourceCallbacks.leftContext ctx).roles 0 ≠
      (GkrSourceCallbacks.leftContext ctx).roles 1 := by
    simpa [GkrSourceCallbacks.leftContext, ProtocolContext.enter, roleSubstitution] using separate
  have rightSeparate : (GkrSourceCallbacks.rightContext ctx).roles 0 ≠
      (GkrSourceCallbacks.rightContext ctx).roles 1 := by
    simpa [GkrSourceCallbacks.rightContext, ProtocolContext.enter, roleSubstitution] using separate
  simp only [GkrSourceCallbacks.verifierLayerProcess, layer, helper,
    PIR.Process.interpret_bind, PIR.Process.bind_assoc, PIR.Process.bind,
    rounds_source _ leftSeparate, rounds_source _ rightSeparate,
    GkrRoundsReading.roundsResults, Values.get_cons, TypedABI.get_cons_here,
    TypedABI.get_cons_there, GkrRoundsReading.empty_plain, GkrRoundsReading.append_plain,
    List.nil_append]
  apply congrArg (PIR.Process.bind _); funext current
  apply congrArg (PIR.Process.bind _); funext pending
  apply congrArg (PIR.Process.bind _); funext left
  apply congrArg (PIR.Process.bind _); funext right
  apply congrArg (PIR.Process.bind _); funext combined
  apply congrArg (PIR.Process.bind _); funext split
  apply congrArg (PIR.Process.call _); funext first
  have coefficient := coefficients_source (F := F) (G := G) ctx separate width [first]
  have continued := congrArg (fun process => process.bind fun maybe =>
    match maybe with
    | none => (.halt .incomplete : PIR.Process (Actions F G) (Option (List F) × Option F))
    | some line => (afterCoefficients ctx index handle selector add mul current combined split first line).bind
        fun next => .done (some next.1, some next.2)) coefficient
  convert continued using 1 <;>
    simp only [PIR.Process.interpret_bind, PIR.Process.bind_assoc, PIR.Process.bind,
      PIR.Process.interpret, CommonAdapter.project, scalarDomain, afterCoefficients, helper,
      PIR.Process.bind_ite]
  apply congrArg (PIR.Process.bind _)
  funext result
  cases result.get .here <;>
    simp only [PIR.Process.interpret, PIR.Process.interpret_bind, PIR.Process.bind_assoc, PIR.Process.bind,
      CommonAdapter.project, scalarDomain]
  repeat' (apply congrArg (PIR.Process.bind _); funext result)
  split <;> simp only [PIR.Process.interpret, PIR.Process.interpret_bind, PIR.Process.bind,
    CommonAdapter.project, scalarDomain]


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
    (denoteRepeat GkrSourceCallbacks.outputSpec ctx (ctx.roles 1) (some count)
      (.cons (some point) (.cons none .nil)) (.cons (some handle) .nil)
      (GkrSourceCallbacks.outputFn (F := F) (G := G) ctx (ctx.roles 1))).interpret CommonAdapter.project =
      (output ctx handle count point).bind fun result =>
        .done (GkrSourceCallbacks.verifierOutputState (some result)) := by
  by_cases bounded : count ≤ 4
  · rw [GkrSourceCallbacks.verifierOutput_fold ctx separate (some handle) count bounded
      (.cons (some point) (.cons none .nil)) (some point)
      (GkrSourceCallbacks.verifierOutputState_masked ctx _ rfl (some point))]
    rw [Finite.fold_range_repeatN _ 0 count]
    simp only [PIR.Process.interpret_bind]
    rw [GkrRoundsReading.repeatN_reads CommonAdapter.project _ (GkrVerifier.outputRound ctx handle)
      some (GkrLayerReading.output_reads ctx handle) count point]
    simp only [output, bounded, ite_true, PIR.Process.bind_assoc, PIR.Process.bind, PIR.Process.interpret]
  · simp only [denoteRepeat, denoteRepeatOn, GkrSourceCallbacks.outputSpec, output,
      GkrSourceCallbacks.outputMaximum, bounded, ite_false,
      List.map_cons, List.map_nil, List.contains_cons, List.contains_nil,
      beq_self_eq_true, Bool.or_true, Bool.true_or, ↓reduceIte, PIR.Process.bind, PIR.Process.interpret]

def layers (ctx : ProtocolContext) (handle selector width count : Nat)
    (add mul : List F) (state : List F × F) : PIR.Process (Actions F G) (List F × F) :=
  if count ≤ 4 then Finite.fold (fun state index =>
    layer ctx index handle selector width add mul state.1 state.2) (List.range' 0 count) state
  else .halt .refused

theorem layers_source (ctx : ProtocolContext) (separate : ctx.roles 0 ≠ ctx.roles 1)
    (handle selector width count : Nat) (inputs add mul point : List F) (claim : F) :
    (denoteRepeat GkrSourceCallbacks.layerSpec ctx (ctx.roles 1) (some count)
      (GkrSourceCallbacks.verifierLayerState (some point) (some claim))
      (.cons (some inputs) (.cons (some add) (.cons (some mul) (.cons (some count)
        (.cons (some selector) (.cons (some width) (.cons (some handle) .nil)))))))
      (GkrSourceCallbacks.layerFn (F := F) (G := G) ctx (ctx.roles 1))).interpret CommonAdapter.project =
      (layers ctx handle selector width count add mul (point, claim)).bind fun result =>
        .done (GkrSourceCallbacks.verifierLayerState (some result.1) (some result.2)) := by
  by_cases bounded : count ≤ 4
  · rw [GkrSourceCallbacks.verifierLayer_fold ctx separate (some inputs) (some add) (some mul)
      (some count) (some selector) (some width) (some handle) count bounded _ (some point, some claim)
      (GkrSourceCallbacks.verifierLayerState_masked ctx _ rfl (some point) (some claim))]
    simp only [PIR.Process.interpret_bind]
    have foldLaw := finite_reads CommonAdapter.project
      (fun (state : Option (List F) × Option F) index =>
        GkrSourceCallbacks.verifierLayerProcess (F := F) (G := G) ctx index (some add) (some mul)
          (some selector) (some width) (some handle) state.1 state.2)
      (fun (state : List F × F) index => layer ctx index handle selector width add mul state.1 state.2)
      (fun (state : List F × F) => (some state.1, some state.2))
      (fun state index => layer_source ctx separate index handle selector width add mul state.1 state.2)
      (List.range' 0 count) (point, claim)
    rw [foldLaw]
    simp only [layers, bounded, ite_true, PIR.Process.bind_assoc, PIR.Process.bind, PIR.Process.interpret]
  · simp only [denoteRepeat, denoteRepeatOn, GkrSourceCallbacks.layerSpec, layers,
      GkrSourceCallbacks.layerMaximum, bounded, ite_false,
      List.map_cons, List.map_nil, List.contains_cons, List.contains_nil,
      beq_self_eq_true, Bool.or_true, Bool.true_or, ↓reduceIte, PIR.Process.bind, PIR.Process.interpret]

/-- The actual admission calls and guards, including all closed-helper stops. -/
def verifier (inputs outputs add mul : List F) (count selector width handle : Nat) :
    PIR.Process (Actions F G) Bool :=
  (helper PrimitiveShapeViews.lessHelper (.cons 4 (.cons width .nil))).bind fun wide =>
  if wide.get .here = false then
  (helper PrimitiveShapeViews.lessHelper (.cons 4 (.cons count .nil))).bind fun deep =>
  if deep.get .here = false then
  (helper GkrSourceBodies.helper4Helper (.cons inputs (.cons width (.cons 1 .nil)))).bind fun initialShape =>
  if initialShape.get .here = true then
  (helper GkrSourceBodies.helper4Helper (.cons outputs (.cons width (.cons 1 .nil)))).bind fun outputShape =>
  if outputShape.get .here = true then
  (helper GkrSourceBodies.sourceHelper4Helper (.cons selector (.cons width .nil))).bind fun a1 =>
  (helper GkrSourceBodies.sourceHelper4Helper (.cons (a1.get .here) (.cons width .nil))).bind fun a2 =>
  (helper GkrSourceBodies.sourceHelper4Helper (.cons (a2.get .here) (.cons width .nil))).bind fun a3 =>
  (helper GkrSourceBodies.helper4Helper (.cons add (.cons (a3.get .here) (.cons 1 .nil)))).bind fun addShape =>
  if addShape.get .here = true then
  (helper GkrSourceBodies.sourceHelper4Helper (.cons selector (.cons width .nil))).bind fun m1 =>
  (helper GkrSourceBodies.sourceHelper4Helper (.cons (m1.get .here) (.cons width .nil))).bind fun m2 =>
  (helper GkrSourceBodies.sourceHelper4Helper (.cons (m2.get .here) (.cons width .nil))).bind fun m3 =>
  (helper GkrSourceBodies.helper4Helper (.cons mul (.cons (m3.get .here) (.cons 1 .nil)))).bind fun mulShape =>
  if mulShape.get .here = true then
  (helper GkrSourceBodies.helper18Helper (.cons selector .nil)).bind fun power =>
  (helper PrimitiveShapeViews.lessHelper (.cons (power.get .here) (.cons count .nil))).bind fun capacity =>
  if capacity.get .here = false then
  (output {} handle width []).bind fun point =>
  (helper GkrSourceBodies.evaluateHelper (.cons outputs (.cons point .nil))).bind fun initial =>
  (helper GkrSourceBodies.sourceHelper19Helper (.cons point (.cons (initial.get .here) .nil))).bind fun packed =>
  (layers {} handle selector width count add mul (packed.get .here, packed.get (.there .here))).bind fun state =>
  (helper GkrSourceBodies.sourceHelper84Helper (.cons inputs (.cons state.1 (.cons state.2 .nil)))).bind fun final =>
  .done (final.get .here)
  else .halt .reject
  else .halt .reject
  else .halt .reject
  else .halt .reject
  else .halt .reject
  else .halt .reject
  else .halt .reject

set_option maxHeartbeats 300000 in
theorem source_equation (inputs outputs add mul : List F) (count selector width handle : Nat) :
    sourceVerifier (F := F) (G := G) inputs outputs add mul count selector width handle =
      (verifier inputs outputs add mul count selector width handle).bind fun decision => .done (some decision) := by
  unfold sourceVerifier sourceInputs
  change ((GkrSourceViews.program.participant F G 1
    (.cons (some inputs) (.cons (some outputs) (.cons (some add) (.cons (some mul)
      (.cons (some count) (.cons (some selector) (.cons (some width)
        (.cons (some handle) .nil))))))))).bind
      fun result => .done (result.get .here)).interpret CommonAdapter.project = _
  rw [GkrRootNormalForms.verifier_participant]
  have output_fn (ctx : ProtocolContext) (self : Nat) :
      GkrRootNormalForms.outputFn (F := F) (G := G) ctx self =
        GkrSourceCallbacks.outputFn ctx self := rfl
  have layer_fn (ctx : ProtocolContext) (self : Nat) :
      GkrRootNormalForms.layerFn (F := F) (G := G) ctx self =
        GkrSourceCallbacks.layerFn ctx self := rfl
  have interpret_branch {A : Type} (condition : Prop) [Decidable condition]
      (yes no : PIR.Process (participantInterface F G) A) :
      (if condition then yes else no).interpret CommonAdapter.project =
        (if condition then yes.interpret CommonAdapter.project else no.interpret CommonAdapter.project) := by
    split <;> rfl
  have false_guard (value : Bool) : ((value == false) = true) ↔ value = false := by
    cases value <;> decide
  have branch_congr {A : Type} (condition : Prop) [Decidable condition]
      {yes no yes' no' : PIR.Process (Actions F G) A}
      (yesEq : yes = yes') (noEq : no = no') :
      (if condition then yes else no) = (if condition then yes' else no') := by
    rw [yesEq, noEq]
  simp only [GkrRootNormalForms.verifierProcess, output_fn, layer_fn,
    sourceInputs, GkrRoundsReading.closed,
    PIR.Process.bind_assoc, PIR.Process.bind, Values.get, PIR.Process.interpret_bind,
    PIR.Process.bind_ite, interpret_branch, false_guard, Values.get_cons,
    TypedABI.get_cons_here, TypedABI.get_cons_there,
    GkrRoundsReading.empty_plain, output_source {} (by decide),
    layers_source {} (by decide), GkrSourceCallbacks.verifierOutputState,
    GkrSourceCallbacks.verifierLayerState, GkrInputNormalForms.verifierProcess,
    PIR.Process.interpret, CommonAdapter.project, scalarDomain, verifier, helper]
  repeat' first
    | (fail_if_no_progress (simp only [PIR.Process.bind_assoc, PIR.Process.bind, PIR.Process.interpret_bind,
        PIR.Process.bind_ite, interpret_branch, false_guard, Values.get_cons,
        TypedABI.get_cons_here, TypedABI.get_cons_there,
        output_source {} (by decide), layers_source {} (by decide),
        GkrSourceCallbacks.verifierOutputState, GkrSourceCallbacks.verifierLayerState]))
    | (apply congrArg (PIR.Process.bind _); funext result)
    | (apply branch_congr)
  erw [layers_source {} (by decide)]
  simp only [PIR.Process.bind_assoc, PIR.Process.bind, GkrSourceCallbacks.verifierLayerState,
    TypedABI.get_cons_here, TypedABI.get_cons_there, PIR.Process.interpret_bind,
    PIR.Process.interpret]

end ZkcExamples.Construction.GkrSourceProtocol
