import Zkc.Source.Structured.NormalForm.Observation
import Zkc.Source.Structured.UnitViews
import ZkcExamples.Structured.RepeatData
import Mathlib.Algebra.Field.Rat

/-! Admitted synthetic source: shared component calls in nested symbolic repeats.
The provider is arbitrary in the semantic equations. Concrete traces below are
controls for unequal reached coordinates, call paths, full returns and stops. -/
set_option autoImplicit false
set_option smartUnfolding false
noncomputable section
namespace Tests.StructuredOccurrenceNormalForm
open Zkc.Source Zkc.Source.Structured NormalForm

abbrev fieldType : Ty := .field "bls12-381.fr"
abbrev serviceType : Ty := .service "random.bls12-381.fr/0"
abbrev stateTypes : List Ty := [.index, fieldType]
abbrev stepInputs : List Ty := [.boolean, .boolean, .index, serviceType]
abbrev rootInputs : List Ty := [.index, .index, .boolean, .boolean, .index, fieldType, serviceType]

def gateHelper : Helper := ⟨"gate", .local, [.boolean, .index], [.index]⟩
def gateBody : Region dialect gateHelper.inputs gateHelper.outputs :=
  .letOp (.mark "branch") .nil .nil <|
  .letOp (.branch [.index] [.index]) (.cons (.here) (.cons (.there (.here)) .nil))
    (.cons (.ret (.cons .here .nil))
      (.cons (.letOp (.mark "abort") .nil .nil (.stop .abort)) .nil)) <|
  .ret (.cons .here .nil)

def stepSignature : ProtocolSignature :=
  ⟨"step", ["P"], stepInputs, stateTypes, [[0], [0], [0], [0]], [[0], [0]]⟩
def runSignature : ProtocolSignature :=
  ⟨"main", ["P"], rootInputs, stateTypes, [[0], [0], [0], [0], [0], [0], [0]], [[0], [0]]⟩

def stepBody : Region protocolDialect stepInputs stateTypes :=
  .letOp (.mark "guard") .nil .nil <|
  .letOp (.guard 0 "guard") (.cons (.here) .nil) .nil <|
  .letOp (.mark "helper") .nil .nil <|
  .letOp (.localCall gateHelper rfl 0 "helper") (.cons (.there (.here)) (.cons (.there (.there (.here))) .nil)) .nil <|
  .letOp (.mark "query") .nil .nil <|
  .letOp (.draw 0 "bls12-381.fr" "query") (.cons (.there (.there (.there (.there (.here))))) .nil) .nil <|
  .ret (.cons (.there (.here)) (.cons (.here) .nil))

def innerSpec : RepeatSpec := ⟨stateTypes, [.boolean, .boolean, serviceType], [0], [[0], [0]], 4⟩
def outerSpec : RepeatSpec := ⟨stateTypes, [.index, .boolean, .boolean, serviceType], [0], [[0], [0]], 3⟩

def innerBody : Region protocolDialect (.index :: (innerSpec.state ++ innerSpec.captures)) stateTypes :=
  .letOp (.mark "first") .nil .nil <|
  .letOp (.protocolApply stepSignature [0] "first") (.cons (.there (.there (.there (.here)))) (.cons (.there (.there (.there (.there (.here))))) (.cons (.there (.here)) (.cons (.there (.there (.there (.there (.there (.here)))))) .nil)))) .nil <|
  .letOp (.mark "second") .nil .nil <|
  .letOp (.protocolApply stepSignature [0] "second") (.cons (.there (.there (.there (.there (.there (.here)))))) (.cons (.there (.there (.there (.there (.there (.there (.here))))))) (.cons (.here) (.cons (.there (.there (.there (.there (.there (.there (.there (.here)))))))) .nil)))) .nil <|
  .ret (.cons (.here) (.cons (.there (.here)) .nil))

def outerBody : Region protocolDialect (.index :: (outerSpec.state ++ outerSpec.captures)) stateTypes :=
  .letOp (.mark "inner") .nil .nil <|
  .letOp (.repeat innerSpec "inner") (.cons (.there (.there (.there (.here)))) (.cons (.there (.here)) (.cons (.there (.there (.here))) (.cons (.there (.there (.there (.there (.here))))) (.cons (.there (.there (.there (.there (.there (.here)))))) (.cons (.there (.there (.there (.there (.there (.there (.here))))))) .nil)))))) (.cons innerBody .nil) <|
  .ret (.cons (.here) (.cons (.there (.here)) .nil))

def runBody : Region protocolDialect rootInputs stateTypes :=
  .letOp (.mark "outer") .nil .nil <|
  .letOp (.repeat outerSpec "outer") (.cons (.here) (.cons (.there (.there (.there (.there (.here))))) (.cons (.there (.there (.there (.there (.there (.here)))))) (.cons (.there (.here)) (.cons (.there (.there (.here))) (.cons (.there (.there (.there (.here)))) (.cons (.there (.there (.there (.there (.there (.there (.here))))))) .nil))))))) (.cons outerBody .nil) <|
  .ret (.cons (.here) (.cons (.there (.here)) .nil))

private def protocol (signature : ProtocolSignature) (body : Block) : Definition :=
  .function ⟨signature.name, .protocol, .publicDef, signature.inputs, signature.outputs,
    some ⟨["P"], signature.inputs.map (fun _ => ["P"]), signature.outputs.map (fun _ => ["P"])⟩,
    [], some (.protocol ⟨signature.name, []⟩), body⟩

private def rawInner : Block := .block [
  .instruction (.protocolApply "step" ["P"]) [3, 4, 1, 5] stateTypes [] "first",
  .instruction (.protocolApply "step" ["P"]) [5, 6, 0, 7] stateTypes [] "second"] (.yield [0, 1])
private def rawOuter : Block := .block [
  .instruction (.protocolRepeat 2 4 ["P"] [["P"], ["P"]]) [3, 1, 2, 4, 5, 6] stateTypes
    [.region [.index, .index, fieldType, .boolean, .boolean, serviceType] stateTypes rawInner] "inner"] (.yield [0, 1])

def snapshot : Snapshot where
  source := "sha256:" ++ String.ofList (List.replicate 64 '0')
  entry := "main"
  domains := []
  relations := []
  bindings := []
  definitions := [
    .function ⟨"gate", .local, .privateDef, [.boolean, .index], [.index], none, [],
      some (.local "gate" []), .block [
        .instruction .branch [0, 1] [.index]
          [.region [.index] [.index] (.block [] (.yield [0])),
           .region [.index] [.index] (.block [] (.stop .abort "abort"))] "branch"] (.ret [0])⟩,
    protocol stepSignature (.block [
      .instruction (.guard "P") [0] [] [] "guard",
      .instruction (.localCall "gate" "P") [1, 2] [.index] [] "helper",
      .instruction (.draw "P" "bls12-381.fr") [4] [fieldType] [] "query"] (.ret [1, 0])),
    protocol runSignature (.block [
      .instruction (.protocolRepeat 2 3 ["P"] [["P"], ["P"]]) [0, 4, 5, 1, 2, 3, 6] stateTypes
        [.region [.index, .index, fieldType, .index, .boolean, .boolean, serviceType] stateTypes rawOuter]
        "outer"] (.ret [0, 1]))]
  contracts := [⟨"step", []⟩, ⟨"main", []⟩]
  catalogue := ZkcExamples.Structured.RepeatData.snapshot.catalogue

structured_views snapshot helpers [gate] protocols [step, run]

/-- The test source is admitted, with these exact typed helper/protocol bodies. -/
example : check snapshot = .ok program := kernel_admission

def stepPattern : InputPattern stepInputs :=
  .cons .optional (.cons .optional (.cons .optional (.cons .optional .nil)))
def rootPattern : InputPattern rootInputs :=
  .cons .optional (.cons .optional (.cons .optional (.cons .optional
    (.cons .optional (.cons .optional (.cons .optional .nil))))))
def stepNormalizer : Signature := { kept := [gateHelper] }
def stepForm : Form stepNormalizer.laws stepNormalizer.callees stepPattern.scope stateTypes :=
  (normalize stepNormalizer stepBody 0 1 stepPattern).toOption.getD (.halt .refused)
def rootForm : Form [] [] rootPattern.scope stateTypes :=
  (normalize {} runBody 0 1 rootPattern).toOption.getD (.halt .refused)

example : normalize stepNormalizer stepBody 0 1 stepPattern = .ok stepForm := by kernel_rfl
example : stepForm.CallsMatch := by kernel_rfl
example : normalize {} runBody 0 1 rootPattern = .ok rootForm := by kernel_rfl
example : rootForm.CallsMatch := by kernel_rfl

variable (model : DomainModel)
abbrev occurrenceInterface := Occurrence.signature model.toCarriers

def helpers : Tables model (occurrenceInterface model) :=
  program.payload.definitions.foldl (Evaluation.ComponentTablesOn.extend model (.silent _)) ⟨[], []⟩

def stepProcess (context : ProtocolContext) (binders : Binders model stepPattern.scope) :=
  stepForm.denoteOn model Occurrence.actions (helpers model) (LawResults.empty model) context
    (runsAtOn model Occurrence.actions Occurrence.iterations (helpers model) [] context 0)
    (noCallees model _) binders

/-- No protocol-reference mathematics or successful-helper premise is used. -/
theorem step_exact (context : ProtocolContext) (binders : Binders model stepPattern.scope) :
    stepBody.denote (meaningAtOn model Occurrence.actions Occurrence.iterations (helpers model) [] context 0)
      (stepPattern.environment model binders).get = stepProcess model context binders :=
  normalize_occurrence_sound stepNormalizer stepBody 0 1 stepPattern stepForm (by kernel_rfl) (by kernel_rfl)
    (fun other bound different => False.elim (different (by omega))) (LawResults.empty model) (noCallees model _) binders
    (LawsHold.empty _ _) (noCallees_hold _ _)

/-- The same admitted root is normalized for every optional input and symbolic
count, including missing counts, excessive counts and stopped callbacks. -/
theorem root_exact (binders : Binders model rootPattern.scope) :
    runBody.denote (meaningAtOn model Occurrence.actions Occurrence.iterations (helpers model)
        (Occurrence.table model program.payload) {} 0) (rootPattern.environment model binders).get =
      rootForm.denoteOn model Occurrence.actions (helpers model) (LawResults.empty model) {}
        (runsAtOn model Occurrence.actions Occurrence.iterations (helpers model)
          (Occurrence.table model program.payload) {} 0) (noCallees model _) binders :=
  normalize_occurrence_sound {} runBody 0 1 rootPattern rootForm (by kernel_rfl) (by kernel_rfl)
    (RosterDistinct.root 0 1) (LawResults.empty model) (noCallees model _) binders
    (LawsHold.empty _ _) (noCallees_hold _ _)

set_option smartUnfolding true

/-- The callee table is the root closure's actual captured prefix. -/
def protocols : ProtocolTable model.Value (occurrenceInterface model) :=
  extendProtocolTableOn model (.silent _) Occurrence.actions (helpers model) [] stepDefinition Occurrence.iterations

def stepKey : CalleeKey := ⟨stepSignature, 0, stepPattern, []⟩
def innerNormalizer : Signature := { callees := [stepKey] }
def innerPattern : InputPattern (.index :: (innerSpec.state ++ innerSpec.captures)) :=
  .cons .optional (.cons .optional (.cons .optional (.cons .optional (.cons .optional (.cons .optional .nil)))))
def innerForm : Form innerNormalizer.laws innerNormalizer.callees innerPattern.scope stateTypes :=
  (normalize innerNormalizer innerBody 0 1 innerPattern).toOption.getD (.halt .refused)

example : normalize innerNormalizer innerBody 0 1 innerPattern = .ok innerForm := by kernel_rfl
example : innerForm.CallsMatch := by kernel_rfl

/-- Both applications reuse this one process, at their respective child contexts. -/
def processes : CalleeProcesses model [stepKey] (occurrenceInterface model) :=
  fun callee => by
    have zero : callee = ⟨0, by decide⟩ := Fin.eq_zero callee
    subst callee
    exact stepProcess model

private theorem mask_state (context : ProtocolContext) (values : Values (Component model.Value) stateTypes) :
    maskValues (context.roles 0) (context.mapScopes [[0], [0]]) values = values := by
  cases values with
  | cons index rest => cases rest with
    | cons field rest =>
      cases rest
      simp [maskValues, ProtocolContext.mapScopes, Participant.restrict]

private theorem static_state (values : Values (Component model.Value) stateTypes) :
    staticMask 0 values [[0], [0]] (Operands.identity stateTypes) = values := by
  cases values with
  | cons index rest => cases rest with
    | cons field rest => cases rest; rfl

/-- The callee equation is proved from its actual checked body and helper table.
It is input pinned by the optional pattern, includes failures, and has no
assumed equation for the root or any protocol reference function. -/
theorem callees_hold {Γ : List Ty} (inputs : Values (Component model.Value) Γ) :
    CalleesHold (protocols model) (processes model) inputs := by
  intro callee context binders others _ distinct
  have zero : callee = ⟨0, by decide⟩ := Fin.eq_zero callee
  subst callee
  cases others
  change invokeProtocol (protocols model) stepSignature context (context.roles 0)
    (stepPattern.fill model binders .nil) = _
  unfold protocols extendProtocolTableOn
  erw [invokeProtocol_cons_same]
  change stepDefinition.denoteWithOn model (.silent _) Occurrence.actions (helpers model) []
    Occurrence.iterations context (context.roles 0) (stepPattern.environment model binders) = _
  erw [normalize_checkedProtocol_soundOn Occurrence.actions Occurrence.iterations
    (helpers model) [] context stepDefinition stepNormalizer 0 stepPattern stepForm
    (by kernel_rfl) (by kernel_rfl) distinct (LawResults.empty model) (noCallees model _)
    _ binders (by
      cases binders with
      | cons g rest => cases rest with
        | cons h rest => cases rest with
          | cons n rest => cases rest with
            | cons q rest =>
              cases rest
              change maskValues (context.roles 0) (context.mapScopes [[0], [0], [0], [0]])
                (.cons g (.cons h (.cons n (.cons q .nil)))) = .cons g (.cons h (.cons n (.cons q .nil)))
              simp [maskValues, ProtocolContext.mapScopes, Participant.restrict])
    (LawsHold.empty _ _) (noCallees_hold _ _)]
  change (stepProcess model context binders).bind (fun values => .done (maskValues (context.roles 0) (context.mapScopes [[0], [0]]) values)) =
    (stepProcess model context binders).bind (fun values => .done (staticMask 0 values [[0], [0]] (Operands.identity stateTypes)))
  simp only [mask_state, static_state]

/-- Shared-callee soundness for both calls, before putting this callback in the
nested repeat. The dynamic induction argument is optional and symbolic. -/
theorem inner_exact (context : ProtocolContext) (binders : Binders model innerPattern.scope) :
    innerBody.denote (meaningAtOn model Occurrence.actions Occurrence.iterations
        (helpers model) (protocols model) context 0) (innerPattern.environment model binders).get =
      innerForm.denoteOn model Occurrence.actions (helpers model) (LawResults.empty model) context
        (runsAtOn model Occurrence.actions Occurrence.iterations (helpers model) (protocols model) context 0)
        (processes model) binders :=
  normalize_occurrence_sound innerNormalizer innerBody 0 1 innerPattern innerForm (by kernel_rfl) (by kernel_rfl)
    (fun other bound different => False.elim (different (by omega))) (LawResults.empty model)
    (processes model) binders (LawsHold.empty _ _) (callees_hold model _)

/-- Direct equality with the existing occurrence participant of the admitted
source. Counts and all inputs remain symbolic; no repeat is unrolled. -/
theorem participant_exact (outer inner : Option Nat) (guard helper : Option Bool) (seed : Option Nat)
    (initial : Option (model.Value fieldType)) (service : Option Nat) :
    let binders : Binders model rootPattern.scope :=
      .cons outer (.cons inner (.cons guard (.cons helper (.cons seed (.cons initial (.cons service .nil))))))
    Occurrence.participant model program 0 (rootPattern.environment model binders) =
      rootForm.denoteOn model Occurrence.actions (helpers model) (LawResults.empty model) {}
        (runsAtOn model Occurrence.actions Occurrence.iterations (helpers model) (protocols model) {} 0)
        (noCallees model _) binders := by
  dsimp only
  change runDefinition.denoteWithOn model (.silent _) Occurrence.actions (helpers model) (protocols model)
    Occurrence.iterations {} 0 _ = _
  erw [normalize_checkedProtocol_soundOn Occurrence.actions Occurrence.iterations
    (helpers model) (protocols model) {} runDefinition {} 0 rootPattern rootForm
    (by kernel_rfl) (by kernel_rfl) (RosterDistinct.root 0 1) (LawResults.empty model) (noCallees model _)
    _ (.cons outer (.cons inner (.cons guard (.cons helper (.cons seed (.cons initial (.cons service .nil)))))))
    (by rfl) (LawsHold.empty _ _) (noCallees_hold _ _)]
  change (rootForm.denoteOn model Occurrence.actions (helpers model) (LawResults.empty model) {}
    (runsAtOn model Occurrence.actions Occurrence.iterations (helpers model) (protocols model) {} 0)
    (noCallees model _) _).bind (fun values => .done (maskValues (({} : ProtocolContext).roles 0) (({} : ProtocolContext).mapScopes [[0], [0]]) values)) = _
  rw [show (fun values : Values (Component model.Value) stateTypes =>
    PIR.Process.done (maskValues (({} : ProtocolContext).roles 0) (({} : ProtocolContext).mapScopes [[0], [0]]) values)) = PIR.Process.done by
      funext values
      rw [mask_state model]]
  exact PIR.Process.bind_done _

namespace Trace

abbrev traceModel : DomainModel := (ringModel ℚ ℚ)
abbrev State := List Occurrence.Frame × Nat
inductive Event where
  | enter (frame : Occurrence.Frame)
  | leave (frame : Occurrence.Frame)
  | query (stack : List Occurrence.Frame) (site : String) (handle : Nat)
  deriving DecidableEq, Repr

/-- A deterministic provider used only for kernel-checked controls. The generic
soundness theorem above quantifies over every provider reply. -/
def handler : PIR.Handler (occurrenceInterface traceModel) State Event
  | .enter frame, (stack, counter) =>
      ⟨.returned (), (stack ++ [frame], counter), [.enter frame]⟩
  | .leave frame, (stack, counter) =>
      ⟨.returned (), (stack.dropLast, counter), [.leave frame]⟩
  | .action (.query site _ (.cons handle .nil)), (stack, counter) =>
      ⟨.returned (counter : ℚ), (stack, counter + 1), [.query stack site handle]⟩
  | .action _, state => ⟨.stopped .refused, state, []⟩

def binders (outer inner : Option Nat) (guard helper : Option Bool) (service : Option Nat) :
    Binders traceModel rootPattern.scope :=
  .cons outer (.cons inner (.cons guard (.cons helper (.cons (some 11)
    (.cons (some (37 : ℚ)) (.cons service .nil))))))

def normalized (outer inner : Option Nat) (guard helper : Option Bool) (service : Option Nat) :=
  rootForm.denoteOn traceModel Occurrence.actions (helpers traceModel) (LawResults.empty traceModel) {}
    (runsAtOn traceModel Occurrence.actions Occurrence.iterations (helpers traceModel) (protocols traceModel) {} 0)
    (noCallees traceModel _) (binders outer inner guard helper service)

theorem source_eq (outer inner : Option Nat) (guard helper : Option Bool) (service : Option Nat) :
    Occurrence.participant traceModel program 0
      (rootPattern.environment traceModel (binders outer inner guard helper service)) =
        normalized outer inner guard helper service :=
  participant_exact traceModel outer inner guard helper (some 11) (some 37) service

set_option maxRecDepth 8000 in
/-- Both calls reach the unequal nonzero pair (outer 1, inner 2), with distinct
call-qualified query sites. Their index is the reached induction coordinate. -/
example :
    .query [⟨"outer", 1⟩, ⟨"inner", 2⟩] "apply_5_first_query" 7 ∈
      ((normalized (some 2) (some 3) (some true) (some true) (some 7)).run handler ([], 0)).events ∧
    .query [⟨"outer", 1⟩, ⟨"inner", 2⟩] "apply_6_second_query" 7 ∈
      ((normalized (some 2) (some 3) (some true) (some true) (some 7)).run handler ([], 0)).events := by
  decide +kernel

set_option maxRecDepth 8000 in
/-- The complete index/field tuple survives, including the provider's last reply. -/
example :
    let result := (normalized (some 2) (some 3) (some true) (some true) (some 7)).run handler ([], 0)
    (result.outcome, result.state) =
      (.returned (.cons (some 11) (.cons (some (11 : ℚ)) .nil)), ([], 12)) := by
  kernel_rfl

/-- Helper abort retains reached enter boundaries and never invents a query or
leave event. Keeping the helper invokes its actual stopping semantics. -/
example :
    (normalized (some 2) (some 3) (some true) (some false) (some 7)).run handler ([], 0) =
      ⟨.stopped .abort, ([⟨"outer", 0⟩, ⟨"inner", 0⟩], 0),
        [.enter ⟨"outer", 0⟩, .enter ⟨"inner", 0⟩]⟩ := by
  kernel_rfl

example :
    (normalized (some 2) (some 3) (some false) (some true) (some 7)).run handler ([], 0) =
      ⟨.stopped .reject, ([⟨"outer", 0⟩, ⟨"inner", 0⟩], 0),
        [.enter ⟨"outer", 0⟩, .enter ⟨"inner", 0⟩]⟩ := by
  kernel_rfl

example :
    (normalized (some 2) (some 3) (some true) none (some 7)).run handler ([], 0) =
      ⟨.stopped .incomplete, ([⟨"outer", 0⟩, ⟨"inner", 0⟩], 0),
        [.enter ⟨"outer", 0⟩, .enter ⟨"inner", 0⟩]⟩ := by
  kernel_rfl

/-- A zero repeat does not demand unused captures or run the stopping helper. -/
example : (normalized (some 0) none none none none).run handler ([], 0) =
    ⟨.returned (.cons (some 11) (.cons (some (37 : ℚ)) .nil)), ([], 0), []⟩ := by
  kernel_rfl

example : (normalized none (some 3) (some true) (some true) (some 7)).run handler ([], 0) =
    ⟨.stopped .incomplete, ([], 0), []⟩ := by kernel_rfl

example : (normalized (some 4) (some 3) (some true) (some true) (some 7)).run handler ([], 0) =
    ⟨.stopped .refused, ([], 0), []⟩ := by kernel_rfl

set_option maxRecDepth 8000 in
/-- The reached trace rejects the transposed repeat coordinates. -/
example : .query [⟨"outer", 2⟩, ⟨"inner", 1⟩] "apply_5_first_query" 7 ∉
    ((normalized (some 2) (some 3) (some true) (some true) (some 7)).run handler ([], 0)).events := by
  decide +kernel

end Trace

end Tests.StructuredOccurrenceNormalForm
