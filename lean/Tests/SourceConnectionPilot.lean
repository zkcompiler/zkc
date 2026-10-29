import Zkc.Source.Structured.NormalForm.Observation
import Zkc.Source.Structured.UnitViews
import Zkc.Source.Structured.DomainLinking
import Zkc.Construction.AuthoredPairProducer
import Zkc.Construction.Compiled
import Zkc.Construction.ConnectionOutputs
import Zkc.Construction.ConnectionRouting
import Zkc.Construction.OriginalFrameRelations
import Zkc.Construction.OriginalLoop
import Zkc.Construction.OriginalHelpers
import ZkcExamples.Structured.RepeatData

/-! A deliberately small composed source/construction pilot. The source has
shared applications inside two symbolic repeats, an owned guard, a stopping
closed helper, and an index-valued message. Its plain validator returns every
source output. This module is an engineering fixture, not a security bridge. -/
set_option autoImplicit false
set_option smartUnfolding true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 16000
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Tests.SourceConnectionPilot
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open NormalForm Original

abbrev stateTypes : List Ty := [.index]
abbrev stepInputs : List Ty := [.boolean, .boolean, .index]
abbrev rootInputs : List Ty := [.index, .index, .boolean, .boolean, .index]
abbrev rootOutputs : List Ty := [.boolean, .index]
def gateHelper : Helper := ⟨"gate", .local, [.boolean, .index], [.index]⟩
def gateBody : Region dialect gateHelper.inputs gateHelper.outputs :=
  .letOp (.mark "branch") .nil .nil <|
  .letOp (.branch [.index] [.index]) (.cons .here (.cons (.there .here) .nil))
    (.cons (.ret (.cons .here .nil))
      (.cons (.letOp (.mark "abort") .nil .nil (.stop .abort)) .nil)) <|
  .ret (.cons .here .nil)
def stepSignature : ProtocolSignature :=
  ⟨"step", ["P", "V"], stepInputs, stateTypes, [[0,1], [0,1], [0,1]], [[0,1]]⟩
def runSignature : ProtocolSignature :=
  ⟨"main", ["P", "V"], rootInputs, rootOutputs,
    [[0,1], [0,1], [0,1], [0,1], [0,1]], [[1], [0,1]]⟩
def stepBody : Region protocolDialect stepInputs stateTypes :=
  .letOp (.mark "guard") .nil .nil <|
  .letOp (.guard 1 "guard") (.cons .here .nil) .nil <|
  .letOp (.mark "helper") .nil .nil <|
  .letOp (.localCall gateHelper rfl 1 "helper") (.cons (.there .here) (.cons (.there (.there .here)) .nil)) .nil <|
  .letOp (.mark "message") .nil .nil <|
  .letOp (.exchange .index 0 1 "message") (.cons (.there (.there (.there .here))) .nil) .nil <|
  .ret (.cons .here .nil)
def innerSpec : RepeatSpec := ⟨stateTypes, [.boolean, .boolean], [0,1], [[0,1]], 4⟩
def outerSpec : RepeatSpec := ⟨stateTypes, [.index, .boolean, .boolean], [0,1], [[0,1]], 3⟩
def innerBody : Region protocolDialect (.index :: (innerSpec.state ++ innerSpec.captures)) stateTypes :=
  .letOp (.mark "first") .nil .nil <|
  .letOp (.protocolApply stepSignature [0,1] "first") (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) (.cons (.there .here) .nil))) .nil <|
  .letOp (.mark "second") .nil .nil <|
  .letOp (.protocolApply stepSignature [0,1] "second") (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there .here)))) (.cons .here .nil))) .nil <|
  .ret (.cons .here .nil)
def outerBody : Region protocolDialect (.index :: (outerSpec.state ++ outerSpec.captures)) stateTypes :=
  .letOp (.mark "inner") .nil .nil <|
  .letOp (.repeat innerSpec "inner") (.cons (.there (.there .here)) (.cons (.there .here) (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there .here)))) .nil)))) (.cons innerBody .nil) <|
  .ret (.cons .here .nil)
def runBody : Region protocolDialect rootInputs rootOutputs :=
  .letOp (.mark "outer") .nil .nil <|
  .letOp (.repeat outerSpec "outer") (.cons .here (.cons (.there (.there (.there (.there .here)))) (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) .nil))))) (.cons outerBody .nil) <|
  .ret (.cons (.there (.there (.there .here))) (.cons .here .nil))
private def protocol (signature : ProtocolSignature) (body : Block) : Definition :=
  .function ⟨signature.name, .protocol, .publicDef, signature.inputs, signature.outputs,
    some ⟨["P", "V"], signature.inputScopes.map (List.map fun i => ["P", "V"].getD i ""),
      signature.outputScopes.map (List.map fun i => ["P", "V"].getD i "")⟩,
    [], some (.protocol ⟨signature.name, []⟩), body⟩
private def rawInner : Block := .block [
  .instruction (.protocolApply "step" ["P", "V"]) [2,3,1] stateTypes [] "first",
  .instruction (.protocolApply "step" ["P", "V"]) [3,4,0] stateTypes [] "second"] (.yield [0])
private def rawOuter : Block := .block [
  .instruction (.protocolRepeat 1 4 ["P", "V"] [["P", "V"]]) [2,1,3,4] stateTypes
    [.region [.index, .index, .boolean, .boolean] stateTypes rawInner] "inner"] (.yield [0])
def snapshot : Snapshot where
  source := "sha256:" ++ String.ofList (List.replicate 64 '0')
  entry := "main"
  domains := []
  relations := []
  bindings := []
  definitions := [
    .function ⟨"gate", .local, .privateDef, [.boolean, .index], [.index], none, [],
      some (.local "gate" []), .block [
        .instruction .branch [0,1] [.index]
          [.region [.index] [.index] (.block [] (.yield [0])),
           .region [.index] [.index] (.block [] (.stop .abort "abort"))] "branch"] (.ret [0])⟩,
    protocol stepSignature (.block [
      .instruction (.guard "V") [0] [] [] "guard",
      .instruction (.localCall "gate" "V") [1,2] [.index] [] "helper",
      .instruction (.exchange "P" "V") [3] [.index] [] "message"] (.ret [0])),
    protocol runSignature (.block [
      .instruction (.protocolRepeat 1 3 ["P", "V"] [["P", "V"]]) [0,4,1,2,3] stateTypes
        [.region [.index, .index, .index, .boolean, .boolean] stateTypes rawOuter] "outer"]
      (.ret [3,0]))]
  contracts := [⟨"step", []⟩, ⟨"main", []⟩]
  catalogue := ZkcExamples.Structured.RepeatData.snapshot.catalogue
structured_views snapshot helpers [gate] protocols [step, run]
example : Structured.check snapshot = .ok program := kernel_admission

-- The plain validator has five data inputs and preserves both source outputs.
def context : Context := .plain "main" ["P", "V"] 0 1
def policy : Policy := ⟨"main", "P", "V", 0, "", [], [0,1,2,3,4], [], "zkc.framed/0", ""⟩
def messageTemplate (site : String) : Template :=
  ⟨"main", [⟨"repeat", "main", "outer"⟩, ⟨"repeat", "main", "inner"⟩,
    ⟨"apply", "main", site⟩], ["message", "step", "message", "message", "P", "V"]⟩
def routing : Routing :=
  ⟨snapshot, context, .validator, 0, [messageTemplate "first", messageTemplate "second"], [], [], []⟩
def stepInstructions (site : String) (guardRef helperRef stateRef : Nat) : List Zkc.Construction.Instruction := [
  ⟨.guard (qualifyProtocolSite (some site) "guard"), [guardRef], [], []⟩,
  ⟨.call "gate", [helperRef,stateRef], [.data .index], []⟩,
  ⟨.receive (qualifyProtocolSite (some site) "message")
    (qualifyProtocolSite (some site) "message") "P" .index, [], [.data .index], []⟩]
def innerInstructions : List Zkc.Construction.Instruction :=
  stepInstructions "first" 2 3 8 ++ stepInstructions "second" 2 3 10
-- outer capture: five inputs; outer index at 5, outer carried state at 6.
-- inner capture: those seven slots; inner index at 7, inner carried state at 8.
def outerInstructions : List Zkc.Construction.Instruction := [
  ⟨.loop "inner" 4 [12], [1,6], [.data .index], innerInstructions⟩]
def instructions : List Zkc.Construction.Instruction := [
  ⟨.loop "outer" 3 [7], [0,4], [.data .index], outerInstructions⟩]
def artifact : Zkc.Construction.Participant :=
  ⟨snapshot.source, snapshot.source, policy, "main.V", rootInputs.map ValueSort.data,
    rootOutputs.map ValueSort.data, instructions, [2,5], []⟩

theorem context_checked : exportContext snapshot artifact = some context := by kernel_rfl
theorem checked : Zkc.Construction.checkCompiled imported artifact = .ok () := by kernel_rfl

variable (model : DomainModel)
abbrev I := Occurrence.signature model.toCarriers

def helpers : Tables model (I model) :=
  program.payload.definitions.foldl (Evaluation.ComponentTablesOn.extend model (.silent _)) ⟨[], []⟩
private def protocols : ProtocolTable model.Value (I model) :=
  extendProtocolTableOn model (.silent _) Occurrence.actions (helpers model) [] stepDefinition Occurrence.iterations


def rootPattern : InputPattern rootInputs :=
  .cons .present (.cons .present (.cons .present (.cons .present (.cons .present .nil))))
def rootForm : Form [] [] rootPattern.scope rootOutputs :=
  (normalize {} runBody 1 2 rootPattern).toOption.getD (.halt .refused)

theorem root_normalized (binders : Binders model rootPattern.scope) :
    runBody.denote (meaningAtOn model Occurrence.actions Occurrence.iterations (helpers model)
        (protocols model) {} 1) (rootPattern.environment model binders).get =
      rootForm.denoteOn model Occurrence.actions (helpers model) (LawResults.empty model) {}
        (runsAtOn model Occurrence.actions Occurrence.iterations (helpers model)
          (protocols model) {} 1) (noCallees model _) binders :=
  normalize_occurrence_sound {} runBody 1 2 rootPattern rootForm (by kernel_rfl) (by kernel_rfl)
    (RosterDistinct.root 1 2) (LawResults.empty model) (noCallees model _) binders
    (LawsHold.empty _ _) (noCallees_hold _ _)


def sourceStep (site : String) (guard helper : Option Bool) (seed : Option Nat) :
    PIR.Process (I model) (Values (Component model.Value) stateTypes) :=
  match guard with
  | none => .halt .incomplete
  | some false => .halt .reject
  | some true =>
    match helper, seed with
    | some helper, some seed =>
      ((invoke (Domain.helperTable model program) gateHelper
        (.cons helper (.cons seed .nil))).interpret (closedLift (I := I model))).bind fun _ =>
        .call (.action (.receive .index (qualifyProtocolSite (some site) "message") 0)) fun reply =>
          .done (.cons (some reply) .nil)
    | _, _ => .halt .incomplete

def sourceInner : RegionFunction (Component model.Value) (I model)
    (.index :: (innerSpec.state ++ innerSpec.captures), innerSpec.state) := fun values =>
  (sourceStep model "first" (values.get (.there (.there .here)))
    (values.get (.there (.there (.there .here)))) (values.get (.there .here))).bind fun first =>
      sourceStep model "second" (values.get (.there (.there .here)))
        (values.get (.there (.there (.there .here)))) (first.get .here)

def sourceOuter : RegionFunction (Component model.Value) (I model)
    (.index :: (outerSpec.state ++ outerSpec.captures), outerSpec.state) := fun values =>
  denoteRepeatOn innerSpec {} 1 (values.get (.there (.there .here)))
    (.cons (values.get (.there .here)) .nil)
    (.cons (values.get (.there (.there (.there .here))))
      (.cons (values.get (.there (.there (.there (.there .here))))) .nil))
    (sourceInner model) Occurrence.iterations "inner"

def source (outer inner : Nat) (guard helper : Bool) (seed : Nat) :
    PIR.Process (I model) (Values (Component model.Value) rootOutputs) :=
  (denoteRepeatOn outerSpec {} 1 (some outer) (.cons (some seed) .nil)
    (.cons (some inner) (.cons (some guard) (.cons (some helper) .nil)))
    (sourceOuter model) Occurrence.iterations "outer").bind fun result =>
      .done (.cons (some guard) result)
def sourceInputs (outer inner : Nat) (guard helper : Bool) (seed : Nat) :
    Values (Component model.Value) program.payload.entry.inputs :=
  .cons (some outer) (.cons (some inner) (.cons (some guard) (.cons (some helper)
    (.cons (some seed) .nil))))


def stepView (site : String) (guardRef helperRef stateRef : Nat)
    (rest : Domain.View.Block model.toCarriers) : Domain.View.Block model.toCarriers :=
  Domain.View.sequence (Domain.View.guard guardRef []) <|
  Domain.View.sequence (Domain.View.helper model program "gate" [helperRef,stateRef] [.data .index]) <|
  Domain.View.sequence (Domain.View.receive (qualifyProtocolSite (some site) "message")
    (qualifyProtocolSite (some site) "message") "P" .index [.data .index]) rest
def innerView : Domain.View.Block model.toCarriers :=
  stepView model "first" 2 3 8 (stepView model "second" 2 3 10 Domain.View.empty)
def outerView : Domain.View.Block model.toCarriers :=
  Domain.View.sequence (Domain.View.loop 4 [12] 1 [6] [.data .index] (innerView model)) Domain.View.empty
def rootView : Domain.View.Block model.toCarriers :=
  Domain.View.sequence (Domain.View.loop 3 [7] 0 [4] [.data .index] (outerView model)) Domain.View.empty

theorem step_view (site : String) (guardRef helperRef stateRef : Nat)
    (rest : List Zkc.Construction.Instruction) (view : Domain.View.Block model.toCarriers)
    (law : Domain.Correspondence.Block (program := program) (context := context) rest view) :
    Domain.Correspondence.Block (program := program) (context := context)
      (stepInstructions site guardRef helperRef stateRef ++ rest)
      (stepView model site guardRef helperRef stateRef view) := by
  apply Domain.Correspondence.sequence (Domain.Correspondence.guard _ _ _)
  apply Domain.Correspondence.sequence (Domain.Correspondence.helper _ _ _)
  exact Domain.Correspondence.sequence (Domain.Correspondence.receive _ _ _ _ _) law

theorem body_view : Domain.Correspondence.Block (program := program) (context := context)
    artifact.instructions (rootView model) := by
  apply Domain.Correspondence.sequence
  · apply Domain.Correspondence.loop
    apply Domain.Correspondence.sequence
    · apply Domain.Correspondence.loop
      exact step_view model _ _ _ _ _ _ (step_view model _ _ _ _ _ _ Domain.Correspondence.empty)
    · exact Domain.Correspondence.empty
  · exact Domain.Correspondence.empty

def inputFrame (outer inner : Nat) (guard helper : Bool) (seed : Nat) : Domain.Environment model.toCarriers :=
  [.data (.index outer), .data (.index inner), .data (.boolean guard), .data (.boolean helper), .data (.index seed)]

def stateRelation (frames : Frames) (history : Domain.History model.toCarriers)
    (source : Values (Component model.Value) stateTypes × State model.toCarriers)
    (carried : Domain.Environment model.toCarriers) : Prop :=
  ∃ value : Nat, source = (.cons (some value) .nil, ⟨frames, history⟩) ∧ carried = [.data (.index value)]

private theorem mask_state (values : Values (Component model.Value) stateTypes) :
    maskValues 1 ([[0,1]] : List (List Nat)) values = values := by
  cases values with | cons value rest => cases rest; rfl

private theorem state_sorts (frames : Frames) (history : Domain.History model.toCarriers)
    (original : Values (Component model.Value) stateTypes × State model.toCarriers)
    (carried : Domain.Environment model.toCarriers)
    (related : stateRelation model frames history original carried) :
    Domain.sortsMatch [.data .index] carried = true := by
  obtain ⟨value, rfl, rfl⟩ := related
  rfl

private def helperEncoding (values : Values model.Value [.index]) : Domain.Environment model.toCarriers :=
  [.data (.index (values.get .here))]
private theorem helper_encoding (values : Values model.Value [.index]) :
    Domain.encodeValues values = some (helperEncoding model values) := by
  cases values with | cons value rest => cases rest; rfl

/-- This is the actual captured helper, not a law about a reference function. -/
def helper_certificate (helper : Bool) (seed : Nat) (state : State model.toCarriers)
    (env : Domain.Environment model.toCarriers) (references : List Nat)
    (read : Domain.read env references = some [.data (.boolean helper), .data (.index seed)]) :=
  Simulation.linkedHelperOn model program routing gateHelper (by change gateHelper ∈ [gateDefinition.helper]; exact List.mem_singleton.mpr rfl)
    (.cons helper (.cons seed .nil)) [.data (.boolean helper), .data (.index seed)] rfl
    (helperEncoding model) (helper_encoding model) (by intro values; cases values with
      | cons value rest => cases rest; rfl) state env references read



private theorem step_denote (site : String) (guard helper : Option Bool) (seed : Option Nat) :
    stepDefinition.denoteWithOn model (.silent _) Occurrence.actions (helpers model) []
      Occurrence.iterations (({} : ProtocolContext).enter site [0,1]) 1 (.cons guard (.cons helper (.cons seed .nil))) =
    sourceStep model site guard helper seed := by
  cases guard with
  | none => kernel_rfl
  | some guard =>
    cases guard with
    | false => kernel_rfl
    | true =>
      cases helper with
      | none => kernel_rfl
      | some helper => cases helper <;> cases seed <;> kernel_rfl

private theorem invoke_step (site : String) (guard helper : Option Bool) (seed : Option Nat) :
    invokeProtocol (protocols model) stepSignature (({} : ProtocolContext).enter site [0,1]) 1
      (.cons guard (.cons helper (.cons seed .nil))) =
    sourceStep model site guard helper seed := by
  unfold protocols extendProtocolTableOn
  erw [invokeProtocol_cons_same]
  exact step_denote model site guard helper seed

private theorem index_eta (values : Values (Component model.Value) [.index]) :
    Values.cons (values.get .here) Values.nil = values := by
  cases values with | cons value rest => cases rest; rfl

private theorem inner_denote
    (values : Values (Component model.Value) (.index :: (innerSpec.state ++ innerSpec.captures))) :
    innerBody.denote (meaningAtOn model Occurrence.actions Occurrence.iterations
      (helpers model) (protocols model) {} 1) values.get = sourceInner model values := by
  cases values with | cons index rest =>
    cases rest with | cons seed rest =>
      cases rest with | cons guard rest =>
        cases rest with | cons helper rest =>
          cases rest
          have raw : innerBody.denote (meaningAtOn model Occurrence.actions Occurrence.iterations
            (helpers model) (protocols model) {} 1)
            (Values.cons index (Values.cons seed (Values.cons guard (Values.cons helper Values.nil)))).get =
            ((invokeProtocol (protocols model) stepSignature (({} : ProtocolContext).enter "first" [0,1]) 1
            (.cons guard (.cons helper (.cons seed .nil)))).bind fun first =>
              (invokeProtocol (protocols model) stepSignature (({} : ProtocolContext).enter "second" [0,1]) 1
                (.cons guard (.cons helper (.cons (first.get .here) .nil)))).bind fun second =>
                  .done (Values.cons (second.get .here) Values.nil : Values (Component model.Value) stateTypes)) := by
            simp only [innerBody, Region.denote, meaningAtOn, participantMeaningWithOn,
              protocolOperationWithOn, Operands.eval, Regions.denote, Values.get,
              Environment.prepend, Environment.push, SiteObservations.silent, PIR.Process.bind]
            have active (site : String) : (({} : ProtocolContext).enter site [0,1]).contains stepSignature 1 = true := by kernel_rfl
            simp only [id_eq, active, ↓reduceIte]
            apply congrArg (PIR.Process.bind _)
            funext first
            cases first with | cons first rest =>
              cases rest
              simp only [Environment.prepend, Environment.push, Values.get]
              apply congrArg (PIR.Process.bind _)
              funext second
              cases second with | cons second rest => cases rest; rfl
          rw [raw]
          simp only [invoke_step]
          simp only [index_eta, PIR.Process.bind_done]
          rfl

private theorem outer_denote
    (values : Values (Component model.Value) (.index :: (outerSpec.state ++ outerSpec.captures))) :
    outerBody.denote (meaningAtOn model Occurrence.actions Occurrence.iterations
      (helpers model) (protocols model) {} 1) values.get = sourceOuter model values := by
  cases values with | cons index rest =>
    cases rest with | cons seed rest =>
      cases rest with | cons inner rest =>
        cases rest with | cons guard rest =>
          cases rest with | cons helper rest =>
            cases rest
            have raw : outerBody.denote (meaningAtOn model Occurrence.actions Occurrence.iterations
              (helpers model) (protocols model) {} 1)
              (Values.cons index (Values.cons seed (Values.cons inner (Values.cons guard (Values.cons helper Values.nil))))).get =
              ((denoteRepeatOn innerSpec {} 1 inner (.cons seed .nil) (.cons guard (.cons helper .nil))
              (fun values => innerBody.denote (meaningAtOn model Occurrence.actions Occurrence.iterations
                (helpers model) (protocols model) {} 1) values.get)
              Occurrence.iterations "inner").bind fun result => .done (Values.cons (result.get .here) Values.nil : Values (Component model.Value) stateTypes)) := by
                simp only [outerBody, Region.denote, meaningAtOn, participantMeaningWithOn,
                  protocolOperationWithOn, Operands.eval, Regions.denote, Values.get,
                  Environment.prepend, Environment.push, SiteObservations.silent, PIR.Process.bind]
                apply congrArg (PIR.Process.bind _)
                funext result
                cases result with | cons result rest => cases rest; rfl
            rw [raw]
            simp only [index_eta, PIR.Process.bind_done, inner_denote]
            rfl

private theorem output_mask (values : Values (Component model.Value) rootOutputs) :
    maskValues 1 [[1],[0,1]] values = values := by
  cases values with | cons value rest => cases rest with | cons index rest => cases rest; rfl

/-- Exact source closure, with masks and both shared applications discharged. -/
theorem source_exact (outer inner : Nat) (guard helper : Bool) (seed : Nat) :
    Occurrence.participant model program 1 (sourceInputs model outer inner guard helper seed) =
      source model outer inner guard helper seed := by
  change invokeProtocol
    (extendProtocolTableOn model (.silent _) Occurrence.actions (helpers model)
      (protocols model) runDefinition Occurrence.iterations)
    runSignature {} 1 (.cons (some outer) (.cons (some inner) (.cons (some guard)
      (.cons (some helper) (.cons (some seed) .nil))))) = _
  unfold extendProtocolTableOn
  erw [invokeProtocol_cons_same]
  change ((runBody.denote (meaningAtOn model Occurrence.actions Occurrence.iterations
    (helpers model) (protocols model) {} 1)
    (sourceInputs model outer inner guard helper seed).get).bind fun result =>
      .done (maskValues 1 [[1],[0,1]] result)) = _
  simp only [output_mask, PIR.Process.bind_done]
  simp only [runBody, Region.denote, meaningAtOn, participantMeaningWithOn,
    protocolOperationWithOn, Operands.eval, Regions.denote, Values.get, sourceInputs,
    Environment.prepend, Environment.push, SiteObservations.silent, PIR.Process.bind]
  change ((denoteRepeatOn outerSpec {} 1 (some outer) (.cons (some seed) .nil)
    (.cons (some inner) (.cons (some guard) (.cons (some helper) .nil)))
    (fun values => outerBody.denote (meaningAtOn model Occurrence.actions Occurrence.iterations
      (helpers model) (protocols model) {} 1) values.get) Occurrence.iterations "outer").bind _) = _
  simp only [outer_denote]
  apply congrArg (PIR.Process.bind _)
  funext result
  cases result with | cons result rest => cases rest; rfl


private theorem message_valid_first : SourceOccurrences.valid snapshot context (messageTemplate "first") = true := by kernel_rfl
private theorem message_valid_second : SourceOccurrences.valid snapshot context (messageTemplate "second") = true := by kernel_rfl

private theorem template_message_origin (site : String) (outer inner : Nat) :
    Domain.templateOrigin context (messageTemplate site) [outer,inner] =
      some (Domain.atCoordinates (context.message (qualifyProtocolSite (some site) "message") 0 1) [outer,inner]) := by
  kernel_rfl
private theorem template_base_origin (site : String) :
    (messageTemplate site).origin context = some (context.message (qualifyProtocolSite (some site) "message") 0 1) := by
  kernel_rfl
private theorem template_repeat_sites (site : String) :
    SourceOccurrences.repeatSites (messageTemplate site) = ["outer","inner"] := by kernel_rfl

theorem message_route (site : String) (present : site ∈ ["first", "second"]) (outer inner : Nat) :
    routing.message [⟨"outer", outer⟩, ⟨"inner", inner⟩]
      (qualifyProtocolSite (some site) "message") 0 1 =
      some (Domain.atCoordinates (context.message (qualifyProtocolSite (some site) "message") 0 1) [outer,inner]) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with rfl | rfl <;>
    simp only [Routing.message, routing, OccurrenceResolution.resolve, List.filter_cons, List.filter_nil,
      OccurrenceResolution.matchesOccurrence, message_valid_first, message_valid_second,
      template_repeat_sites, template_base_origin, template_message_origin,
      List.map_cons, List.map_nil, beq_self_eq_true, Bool.true_and, Bool.and_true]
  all_goals kernel_rfl

def stepReturns (state : State model.toCarriers) (env : Domain.Environment model.toCarriers)
    (original : Values (Component model.Value) stateTypes × State model.toCarriers)
    (final : Domain.Environment model.toCarriers) : Prop :=
  ∃ value temporary : Nat, original = (.cons (some value) .nil, state) ∧
    final = env ++ [.data (.index temporary), .data (.index value)]

private theorem fold_message (site : String) (present : site ∈ ["first", "second"])
    (outer inner : Nat) (history : Domain.History model.toCarriers) :
    fold routing (.call (.action (.receive .index (qualifyProtocolSite (some site) "message") 0))
      (fun reply => .done (Values.cons (some reply) Values.nil : Values (Component model.Value) stateTypes)))
      ⟨[⟨"outer", outer⟩, ⟨"inner", inner⟩], history⟩ =
      .call (.receive .index (qualifyProtocolSite (some site) "message")
        (qualifyProtocolSite (some site) "message") "P") fun reply =>
          .done (.cons (some reply) .nil, ⟨[⟨"outer", outer⟩, ⟨"inner", inner⟩], history⟩) := by
  change (receivePlain routing ⟨[⟨"outer",outer⟩,⟨"inner",inner⟩], history⟩ .index
    (qualifyProtocolSite (some site) "message") 0).bind
      (fun pair => .done ((Values.cons (some pair.1) Values.nil : Values (Component model.Value) stateTypes), pair.2)) = _
  unfold receivePlain
  change ((match routing.message [⟨"outer", outer⟩, ⟨"inner", inner⟩]
    (qualifyProtocolSite (some site) "message") 0 1 with
    | none => PIR.Process.halt .refused
    | some _ => PIR.Process.call (Domain.Effect.receive .index (qualifyProtocolSite (some site) "message")
      (qualifyProtocolSite (some site) "message") "P") (fun value => .done (value,
        (⟨[⟨"outer", outer⟩, ⟨"inner", inner⟩], history⟩ : State model.toCarriers)))) :
      PIR.Process (Domain.effects model.toCarriers) (Nat × State model.toCarriers)).bind
        (fun pair => .done ((Values.cons (some pair.1) Values.nil : Values (Component model.Value) stateTypes), pair.2)) = _
  rw [message_route site present outer inner]
  rfl

/-- Local all-reply alignment: guard, exact captured helper, real message,
and all six instruction checkpoints. Only ordinary SSA reads are premises. -/
def step_certificate (site : String) (present : site ∈ ["first", "second"])
    (outer inner : Nat) (guard helper : Bool) (seed : Nat)
    (history : Domain.History model.toCarriers)
    (env : Domain.Environment model.toCarriers) (guardRef helperRef stateRef : Nat)
    (guardRead : env[guardRef]? = some (.data (.boolean guard)))
    (helperRead : Domain.read env [helperRef,stateRef] =
      some [.data (.boolean helper), .data (.index seed)]) :
    Simulation (stepReturns model ⟨[⟨"outer", outer⟩, ⟨"inner", inner⟩], history⟩ env)
      (fun _ frame => ArtifactBinding.Captures env frame)
      (fold routing (sourceStep model site (some guard) (some helper) (some seed))
        ⟨[⟨"outer", outer⟩, ⟨"inner", inner⟩], history⟩)
      (stepView model site guardRef helperRef stateRef Domain.View.empty env) := by
  cases guard with
  | false =>
    simp only [sourceStep, fold_halt, stepView, Domain.View.sequence, Domain.View.guard,
      guardRead, ↓reduceIte]
    exact .checkpoint env (by simp [ArtifactBinding.Captures]) (.halt .reject)
  | true =>
    simp only [sourceStep, fold_bind, stepView, Domain.View.sequence, Domain.View.guard,
      guardRead, ↓reduceIte, PIR.Process.bind]
    apply Simulation.checkpoint env (by simp [ArtifactBinding.Captures])
    apply Simulation.checkpoint env (by simp [ArtifactBinding.Captures])
    apply Simulation.checkpoint env (by simp [ArtifactBinding.Captures])
    apply (helper_certificate model helper seed ⟨[⟨"outer", outer⟩, ⟨"inner", inner⟩], history⟩
      env [helperRef,stateRef] helperRead).bind
    · intro process frame same
      subst frame
      simp [ArtifactBinding.Captures]
    · intro original final related
      apply Classical.choice
      obtain ⟨result, rfl, rfl⟩ := related
      cases result with | cons temporary rest =>
        cases rest
        refine ⟨?_⟩
        simp only [helperEncoding, Values.get]
        apply Simulation.checkpoint _ (ArtifactBinding.captures_append _ _)
        apply Simulation.checkpoint _ (ArtifactBinding.captures_append _ _)
        rw [fold_message model site present outer inner history]
        simp only [Domain.View.receive, Domain.dataType, Bool.false_eq_true,
          and_self, ↓reduceIte]
        apply Simulation.call
        intro reply
        simp only [Domain.Value.encode, Domain.Payload.ofValue, Option.map,
          Domain.View.append, Domain.sortsMatch, List.map, Domain.Value.sort,
          Domain.Payload.ty, beq_self_eq_true, ↓reduceIte, PIR.Process.bind]
        apply Simulation.checkpoint _
        · simpa [List.append_assoc] using ArtifactBinding.captures_append env
            ([Domain.Value.data (.index temporary), .data (.index reply)])
        · exact .done ⟨reply, temporary, rfl, by simp [Domain.View.empty, List.append_assoc]⟩


private theorem step_view_bind (site : String) (g h n : Nat)
    (rest : Domain.View.Block model.toCarriers) (env : Domain.Environment model.toCarriers) :
    stepView model site g h n rest env =
      (stepView model site g h n Domain.View.empty env).bind rest := by
  simp [stepView, Domain.View.sequence, Domain.View.empty, PIR.Process.bind_assoc, PIR.Process.bind]

/-- Two source applications share the step certificate. Their reply-dependent
states occupy checked, distinct SSA positions in the real inner loop. -/
def inner_callback (outerCount innerCount : Nat) (guard helper : Bool) (rootSeed : Nat)
    (outerIndex outerSeed innerIndex seed : Nat) (history : Domain.History model.toCarriers) :
    let captured := inputFrame model outerCount innerCount guard helper rootSeed ++
      [.data (.index outerIndex), .data (.index outerSeed)]
    Simulation
      (IterationReturns (stateRelation model [⟨"outer", outerIndex⟩] history)
        [⟨"outer", outerIndex⟩] "inner" innerIndex [12] [.data .index])
      (fun _ frame => ArtifactBinding.Captures captured frame)
      (fold routing (sourceInner model (.cons (some innerIndex) (.cons (some seed)
        (.cons (some guard) (.cons (some helper) .nil)))))
        ⟨[⟨"outer", outerIndex⟩, ⟨"inner", innerIndex⟩], history⟩)
      (innerView model (captured ++ [.data (.index innerIndex), .data (.index seed)])) := by
  dsimp only
  dsimp only [sourceInner, Values.get]
  rw [fold_bind]
  unfold innerView
  rw [step_view_bind]
  apply (step_certificate model "first" (by simp) outerIndex innerIndex guard helper seed history
    _ 2 3 8 rfl rfl).bind
  · intro process frame retained
    exact ArtifactBinding.captures_trans (ArtifactBinding.captures_append _ _) retained
  · intro original final related
    apply Classical.choice
    obtain ⟨first, temporary, rfl, rfl⟩ := related
    refine ⟨?_⟩
    have second := step_certificate model "second" (by simp) outerIndex innerIndex guard helper first history
      ((inputFrame model outerCount innerCount guard helper rootSeed ++
        [.data (.index outerIndex), .data (.index outerSeed)] ++
        [.data (.index innerIndex), .data (.index seed)]) ++
        [.data (.index temporary), .data (.index first)]) 2 3 10 rfl rfl
    apply second.mapRelations
    · intro original final related
      obtain ⟨last, temporarySecond, rfl, rfl⟩ := related
      refine ⟨rfl, [.data (.index last)], ?_, rfl, last, rfl, rfl⟩
      rfl
    · intro process frame retained
      apply ArtifactBinding.captures_trans _ retained
      simp [ArtifactBinding.Captures, inputFrame]


/-- The inner runtime count remains symbolic; admission and all yield checks
come from the existing repeat rule. Excessive counts refuse on both sides. -/
def inner_repeat (outerCount innerCount : Nat) (guard helper : Bool) (rootSeed : Nat)
    (outerIndex seed : Nat) (history : Domain.History model.toCarriers) :
    let captured := inputFrame model outerCount innerCount guard helper rootSeed ++
      [.data (.index outerIndex), .data (.index seed)]
    Simulation
      (fun original final => ∃ next,
        stateRelation model [⟨"outer", outerIndex⟩] history original next ∧ final = captured ++ next)
      (fun _ frame => ArtifactBinding.Captures captured frame)
      (fold routing (sourceOuter model (.cons (some outerIndex) (.cons (some seed)
        (.cons (some innerCount) (.cons (some guard) (.cons (some helper) .nil))))))
        ⟨[⟨"outer", outerIndex⟩], history⟩)
      (Domain.View.loop 4 [12] 1 [6] [.data .index] (innerView model) captured) := by
  dsimp only
  apply Simulation.occurrenceRepeat routing innerSpec {} 1 rfl
    (.cons (some guard) (.cons (some helper) .nil)) (sourceInner model) "inner" (innerView model)
    _ [12] [.data .index] (stateRelation model [⟨"outer", outerIndex⟩] history)
  · intro original carried related
    change stateRelation model [⟨"outer",outerIndex⟩] history (maskValues 1 [[0,1]] original.1,original.2) carried
    rw [mask_state]
    simpa only [Prod.eta] using related
  · intro value state carried index related
    apply Classical.choice
    obtain ⟨value, pair, rfl⟩ := related
    cases pair
    refine ⟨?_⟩
    simpa only [innerSpec, ProtocolContext.mapScopes, List.map, id_eq, mask_state, qualifyProtocolSite, Values.append, List.cons_append, List.nil_append] using
      inner_callback model outerCount innerCount guard helper rootSeed outerIndex seed index value history
  · exact state_sorts model _ _
  · rfl
  · rfl
  · rfl
  · exact ⟨seed, rfl, rfl⟩

/-- Nested-loop callback: the inner full result closes its frame, and the
outer yield reads the actual returned SSA slot rather than an acceptance bit. -/
def outer_callback (outerCount innerCount : Nat) (guard helper : Bool) (rootSeed : Nat)
    (outerIndex seed : Nat) (history : Domain.History model.toCarriers) :
    let captured := inputFrame model outerCount innerCount guard helper rootSeed
    Simulation (IterationReturns (stateRelation model [] history) [] "outer" outerIndex [7] [.data .index])
      (fun _ frame => ArtifactBinding.Captures captured frame)
      (fold routing (sourceOuter model (.cons (some outerIndex) (.cons (some seed)
        (.cons (some innerCount) (.cons (some guard) (.cons (some helper) .nil))))))
        ⟨[⟨"outer", outerIndex⟩], history⟩)
      (outerView model (captured ++ [.data (.index outerIndex), .data (.index seed)])) := by
  dsimp only
  unfold outerView Domain.View.sequence
  apply Simulation.checkpoint _ (ArtifactBinding.captures_append _ _)
  have head := inner_repeat model outerCount innerCount guard helper rootSeed outerIndex seed history
  have completed := head.bind
    (sourceNext := fun original => .done original)
    (targetNext := fun final => .call (.checkpoint final) fun _ => Domain.View.empty final)
    (nextLive := fun _ frame => ArtifactBinding.Captures
      (inputFrame model outerCount innerCount guard helper rootSeed) frame)
    (returnRelation := IterationReturns (stateRelation model [] history) [] "outer" outerIndex [7] [.data .index])
    (fun _ _ retained => ArtifactBinding.captures_trans (ArtifactBinding.captures_append _ _) retained)
    (fun original final related => by
      apply Classical.choice
      obtain ⟨next, related, rfl⟩ := related
      obtain ⟨value, rfl, rfl⟩ := related
      refine ⟨?_⟩
      apply Simulation.checkpoint _
      · simp [ArtifactBinding.Captures, inputFrame]
      · exact .done ⟨rfl, [.data (.index value)], rfl, rfl, value, rfl, rfl⟩)
  simpa only [PIR.Process.bind_done] using completed

/-- The outer repeat uses the same symbolic rule as the inner repeat. -/
def root_repeat (outer inner : Nat) (guard helper : Bool) (seed : Nat)
    (history : Domain.History model.toCarriers) :
    Simulation
      (fun original final => ∃ next, stateRelation model [] history original next ∧
        final = inputFrame model outer inner guard helper seed ++ next)
      (fun _ frame => ArtifactBinding.Captures (inputFrame model outer inner guard helper seed) frame)
      (fold routing (denoteRepeatOn outerSpec {} 1 (some outer) (.cons (some seed) .nil)
        (.cons (some inner) (.cons (some guard) (.cons (some helper) .nil)))
        (sourceOuter model) Occurrence.iterations "outer") ⟨[], history⟩)
      (Domain.View.loop 3 [7] 0 [4] [.data .index] (outerView model)
        (inputFrame model outer inner guard helper seed)) := by
  apply Simulation.occurrenceRepeat routing outerSpec {} 1 rfl
    (.cons (some inner) (.cons (some guard) (.cons (some helper) .nil))) (sourceOuter model)
    "outer" (outerView model) _ [7] [.data .index] (stateRelation model [] history)
  · intro original carried related
    change stateRelation model [] history (maskValues 1 [[0,1]] original.1,original.2) carried
    rw [mask_state]
    simpa only [Prod.eta] using related
  · intro value state carried index related
    apply Classical.choice
    obtain ⟨value, pair, rfl⟩ := related
    cases pair
    refine ⟨?_⟩
    simpa only [outerSpec, ProtocolContext.mapScopes, List.map, id_eq, mask_state, qualifyProtocolSite, Values.append, List.cons_append, List.nil_append] using
      outer_callback model outer inner guard helper seed index value history
  · exact state_sorts model _ _
  · rfl
  · rfl
  · rfl
  · exact ⟨seed, rfl, rfl⟩


/-- Complete source/profile-owned outputs, the final physical return map,
closed frames and all immutable input readbacks. No root simulation premise. -/
def composed (outer inner : Nat) (guard helper : Bool) (seed : Nat)
    (history : Domain.History model.toCarriers) :
    Simulation (CompleteReturns runSignature context 1 artifact)
      (fun _ frame => ArtifactBinding.Captures (inputFrame model outer inner guard helper seed) frame)
      (fold routing (Occurrence.participant model program 1
        (sourceInputs model outer inner guard helper seed)) ⟨[], history⟩)
      (Domain.participant model program context artifact (inputFrame model outer inner guard helper seed)) := by
  rw [source_exact]
  rw [Domain.Correspondence.participant artifact (body_view model)]
  simp only [source, fold_bind, fold_done]
  have inputSorts : Domain.sortsMatch artifact.inputs (inputFrame model outer inner guard helper seed) = true := rfl
  simp only [Domain.View.participant, inputSorts, ↓reduceIte]
  unfold rootView
  apply Simulation.checkpoint _ (by simp [ArtifactBinding.Captures])
  simp only [Domain.View.sequence, PIR.Process.bind]
  apply Simulation.checkpoint _ (by simp [ArtifactBinding.Captures])
  try simp only [PIR.Process.bind_assoc]
  apply (root_repeat model outer inner guard helper seed history).bind
  · exact fun _ _ retained => retained
  · intro original final related
    apply Classical.choice
    obtain ⟨next, related, rfl⟩ := related
    obtain ⟨value, rfl, rfl⟩ := related
    refine ⟨?_⟩
    apply Simulation.checkpoint _ (ArtifactBinding.captures_append _ _)
    change Simulation _ _ (.done _) (.done _)
    apply Simulation.done
    exact ⟨⟨[.data .boolean, .data .index], rfl, rfl⟩,
      ⟨[.data (.boolean guard), .data (.index value)], rfl, rfl⟩, rfl, rfl, rfl⟩

def normalized (outer inner : Nat) (guard helper : Bool) (seed : Nat) :=
  rootForm.denoteOn model Occurrence.actions (helpers model) (LawResults.empty model) {}
    (runsAtOn model Occurrence.actions Occurrence.iterations (helpers model)
      (protocols model) {} 1) (noCallees model _)
    (.cons outer (.cons inner (.cons guard (.cons helper (.cons seed .nil)))))

/-- The normalized view has the exact actual root meaning, including reached
iteration boundaries. Applications remain shared table calls in loop regions. -/
theorem source_normalized (outer inner : Nat) (guard helper : Bool) (seed : Nat) :
    Occurrence.participant model program 1 (sourceInputs model outer inner guard helper seed) =
      normalized model outer inner guard helper seed := by
  have body := root_normalized model
    (.cons outer (.cons inner (.cons guard (.cons helper (.cons seed .nil)))))
  have closure : Occurrence.participant model program 1 (sourceInputs model outer inner guard helper seed) =
      runBody.denote (meaningAtOn model Occurrence.actions Occurrence.iterations (helpers model)
        (protocols model) {} 1)
        (sourceInputs model outer inner guard helper seed).get := by
    change invokeProtocol
      (extendProtocolTableOn model (.silent _) Occurrence.actions (helpers model)
        (protocols model) runDefinition Occurrence.iterations)
      runSignature {} 1 (.cons (some outer) (.cons (some inner) (.cons (some guard)
        (.cons (some helper) (.cons (some seed) .nil))))) = _
    unfold extendProtocolTableOn
    erw [invokeProtocol_cons_same]
    change ((runBody.denote (meaningAtOn model Occurrence.actions Occurrence.iterations (helpers model)
      (protocols model) {} 1) (sourceInputs model outer inner guard helper seed).get).bind
        fun result => .done (maskValues 1 [[1],[0,1]] result)) = _
    simp only [output_mask, PIR.Process.bind_done]
  exact closure.trans body

/-- The requested composed normalization/fold/artifact chain, for symbolic
counts and every ABI-related input, with arbitrary typed receive replies. -/
def normalized_composed (outer inner : Nat) (guard helper : Bool) (seed : Nat)
    (history : Domain.History model.toCarriers) :
    Simulation (CompleteReturns runSignature context 1 artifact)
      (fun _ frame => ArtifactBinding.Captures (inputFrame model outer inner guard helper seed) frame)
      (fold routing (normalized model outer inner guard helper seed) ⟨[], history⟩)
      (Domain.participant model program context artifact (inputFrame model outer inner guard helper seed)) := by
  rw [← source_normalized]
  exact composed model outer inner guard helper seed history


private def closed_coverage {types : List Ty} (frames : Frames)
    (process : PIR.Process closedInterface (Values model.Value types)) :
    RouteCoverage routing frames frames (process.interpret (closedLift (I := I model))) := by
  cases process with
  | done value => exact .done _ _
  | halt reason => exact .halt _ _ _
  | call operation _ => exact nomatch operation

private def step_coverage (site : String) (present : site ∈ ["first", "second"])
    (outer inner : Nat) (guard helper : Option Bool) (seed : Option Nat) :
    RouteCoverage routing [⟨"outer",outer⟩, ⟨"inner",inner⟩] [⟨"outer",outer⟩, ⟨"inner",inner⟩]
      (sourceStep model site guard helper seed) := by
  cases guard with
  | none => exact .halt _ _ _
  | some guard =>
    cases guard with
    | false => exact .halt _ _ _
    | true =>
      cases helper with
      | none => exact .halt _ _ _
      | some helper =>
        cases seed with
        | none => exact .halt _ _ _
        | some seed =>
          apply (closed_coverage model _ (invoke (Domain.helperTable model program) gateHelper
            (.cons helper (.cons seed .nil)))).bind
          intro value
          apply RouteCoverage.action
          · exact ⟨rfl, _, message_route site present outer inner⟩
          · exact fun _ => .done _ _

private def repeat_coverage (spec : RepeatSpec) (count : Option Nat)
    (initial : Values (Component model.Value) spec.state)
    (captures : Values (Component model.Value) spec.captures)
    (body : RegionFunction (Component model.Value) (I model)
      (.index :: (spec.state ++ spec.captures), spec.state))
    (site : String) (frames : Frames)
    (callback : ∀ index values, RouteCoverage routing (frames ++ [⟨site,index⟩])
      (frames ++ [⟨site,index⟩]) (body values)) :
    RouteCoverage routing frames frames
      (denoteRepeatOn spec {} 1 count initial captures body Occurrence.iterations site) := by
  unfold denoteRepeatOn
  split
  · cases count with
    | none => exact .halt _ _ _
    | some count =>
      dsimp only
      split
      · apply RouteCoverage.finite
        intro value index
        unfold Repeat.stepOn
        apply RouteCoverage.bind (RouteCoverage.within site index (callback index _))
        exact fun _ => .done _ _
      · exact .halt _ _ _
  · exact .done _ _

private def inner_coverage (outer inner : Nat)
    (values : Values (Component model.Value) (.index :: (innerSpec.state ++ innerSpec.captures))) :
    RouteCoverage routing [⟨"outer",outer⟩, ⟨"inner",inner⟩] [⟨"outer",outer⟩, ⟨"inner",inner⟩]
      (sourceInner model values) := by
  cases values with | cons index rest =>
    cases rest with | cons seed rest =>
      cases rest with | cons guard rest =>
        cases rest with | cons helper rest =>
          cases rest
          apply (step_coverage model "first" (by simp) outer inner guard helper seed).bind
          intro first
          cases first with | cons seed rest =>
            cases rest
            exact step_coverage model "second" (by simp) outer inner guard helper seed

private def outer_coverage (outer : Nat)
    (values : Values (Component model.Value) (.index :: (outerSpec.state ++ outerSpec.captures))) :
    RouteCoverage routing [⟨"outer",outer⟩] [⟨"outer",outer⟩] (sourceOuter model values) := by
  cases values with | cons index rest =>
    cases rest with | cons seed rest =>
      cases rest with | cons inner rest =>
        cases rest with | cons guard rest =>
          cases rest with | cons helper rest =>
            cases rest
            exact repeat_coverage model innerSpec inner (.cons seed .nil) (.cons guard (.cons helper .nil))
              (sourceInner model) "inner" [⟨"outer",outer⟩] (inner_coverage model outer)

/-- Coverage follows the actual source process, not the route proposal list.
Every reached message has a route for every prior receive reply. -/
def route_coverage (outer inner : Nat) (guard helper : Bool) (seed : Nat) :
    RouteCoverage routing [] []
      (Occurrence.participant model program 1 (sourceInputs model outer inner guard helper seed)) := by
  rw [source_exact]
  apply (repeat_coverage model outerSpec (some outer) (.cons (some seed) .nil)
    (.cons (some inner) (.cons (some guard) (.cons (some helper) .nil)))
    (sourceOuter model) "outer" [] (outer_coverage model)).bind
  exact fun _ => .done _ _


/-! The complementary finite fixture exercises the profile-specific boundary:
a private owner draw, producer send / validator receive, public challenge and
its source def-use delivery. Both actual participants preserve the full tuple. -/
/-- The live obligation recovers every immutable input from each actual
checkpoint; it is not a semantic field supplied by the client. -/
theorem checkpoint_readback (outer inner : Nat) (guard helper : Bool) (seed : Nat)
    (frame : Domain.Environment model.toCarriers)
    (retained : ArtifactBinding.Captures (inputFrame model outer inner guard helper seed) frame) :
    Domain.read frame [0,1,2,3,4] = some (inputFrame model outer inner guard helper seed) := by
  have retainedInputs : frame.take 5 = inputFrame model outer inner guard helper seed := retained
  have read : Domain.read (frame.take 5) [0,1,2,3,4] =
      some (inputFrame model outer inner guard helper seed) := by rw [retainedInputs]; rfl
  simpa [Domain.read, List.getElem?_take] using read

/-- Exact non-administrative interaction trees: a mismatched event, stop,
message payload or reply-dependent suffix cannot be inserted by alignment. -/
theorem no_invented_events (outer inner : Nat) (guard helper : Bool) (seed : Nat)
    (history : Domain.History model.toCarriers) :
    ((Domain.participant model program context artifact (inputFrame model outer inner guard helper seed)).bind
      (fun _ => .done ())).interpret forgetCheckpoints =
    ((fold routing (normalized model outer inner guard helper seed) ⟨[],history⟩).bind
      (fun _ => .done ())).interpret forgetCheckpoints :=
  (normalized_composed model outer inner guard helper seed history).shape

/-- Execution includes the actual checkpoint frames, stopped state, ordered
events and all handler state. The paired process retains both complete ABIs. -/
theorem composed_runM (outer inner : Nat) (guard helper : Bool) (seed : Nat)
    (history : Domain.History model.toCarriers)
    {m : Type → Type} [Monad m] [LawfulMonad m] {R E : Type}
    (handler : PIR.MonadHandler m (Domain.effects model.toCarriers) R E) (state : R) :
    (Domain.participant model program context artifact (inputFrame model outer inner guard helper seed)).runM handler state =
      (do let execution ← (normalized_composed model outer inner guard helper seed history).paired.runM handler state
          pure (mapExecution Prod.snd execution)) :=
  (normalized_composed model outer inner guard helper seed history).runM handler state

def omittedRouting : Routing := { routing with messages := [messageTemplate "first"] }
theorem omitted_route (outer inner : Nat) :
    omittedRouting.message [⟨"outer",outer⟩,⟨"inner",inner⟩]
      (qualifyProtocolSite (some "second") "message") 0 1 = none := by kernel_rfl

theorem omitted_route_no_coverage (outer inner seed : Nat) :
    IsEmpty (RouteCoverage omittedRouting [⟨"outer",outer⟩,⟨"inner",inner⟩]
      [⟨"outer",outer⟩,⟨"inner",inner⟩]
      (sourceStep model "second" (some true) (some true) (some seed))) := by
  constructor
  intro covered
  change RouteCoverage _ _ _ (.call (.action (.receive .index
    (qualifyProtocolSite (some "second") "message") 0)) _) at covered
  obtain ⟨_,origin,found⟩ := covered.action_required
  change omittedRouting.message [⟨"outer",outer⟩,⟨"inner",inner⟩]
    (qualifyProtocolSite (some "second") "message") 0 1 = some origin at found
  rw [omitted_route] at found
  cases found

example : routing.message [⟨"inner",2⟩,⟨"outer",1⟩]
    (qualifyProtocolSite (some "first") "message") 0 1 = none := by kernel_rfl
example : routing.message [⟨"outer",1⟩,⟨"inner",2⟩] "wrong_occurrence" 0 1 = none := by kernel_rfl
example : routing.draw [] "q" "bls12-381.fr" 73 = none := by kernel_rfl
example : routing.delivery [] "d" "bls12-381.fr" 0 = none := by kernel_rfl

/-- A changed index cannot be hidden behind the same acceptance Boolean. -/
theorem changed_residual_rejected (history : Domain.History model.toCarriers)
    (environment : Domain.Environment model.toCarriers) :
    ¬ CompleteReturns runSignature context 1 artifact
      (.cons (some true) (.cons (some 19) .nil),⟨[],history⟩)
      ⟨[.data (.boolean true),.data (.index 17)],environment⟩ := by
  intro complete
  obtain ⟨data,encoded,returned⟩ := complete.values
  have exactEncoding : roleOutputValues (carriers := model.toCarriers) 1 runSignature.outputScopes
      (Values.cons (some true) (Values.cons (some 19) Values.nil) : Values (Component model.Value) rootOutputs) =
      some [Domain.Value.data (.boolean true),.data (.index 19)] := rfl
  rw [exactEncoding] at encoded
  cases encoded
  cases returned

/-- Structural admission does not prove the full returned row. The independent
connection obligation owns that equation; `changed_residual_rejected` above
shows why selecting the same acceptance Boolean is insufficient. -/
example : checkCompiled imported {artifact with returned := [2,4]} = .ok () := by decide +kernel

theorem missing_guard_refused (site : String) :
    sourceStep model site none (some true) (some 17) = .halt .incomplete := by kernel_rfl
theorem missing_helper_refused (site : String) :
    sourceStep model site (some true) none (some 17) = .halt .incomplete := by kernel_rfl

namespace Controls
inductive Event where
  | enter (frame : Occurrence.Frame)
  | leave (frame : Occurrence.Frame)
  | receive (frames : Frames) (site : String)
  deriving DecidableEq

def handler : PIR.Handler (I model) (Frames × Nat) Event
  | .enter frame, (frames,count) => ⟨.returned (), (frames ++ [frame],count), [.enter frame]⟩
  | .leave frame, (frames,count) => ⟨.returned (), (frames.dropLast,count), [.leave frame]⟩
  | .action (.receive .index site _), (frames,count) =>
      ⟨.returned count, (frames,count+1), [.receive frames site]⟩
  | .action _, state => ⟨.stopped .refused,state,[]⟩

/-- Unequal nonzero coordinates, in the actual normalized source process. -/
theorem nested_coordinate_witness :
    .receive [⟨"outer",1⟩,⟨"inner",2⟩] (qualifyProtocolSite (some "first") "message") ∈
      ((normalized model 2 3 true true 17).run (handler model) ([],0)).events ∧
    .receive [⟨"outer",1⟩,⟨"inner",2⟩] (qualifyProtocolSite (some "second") "message") ∈
      ((normalized model 2 3 true true 17).run (handler model) ([],0)).events := by
  rw [← source_normalized, source_exact]
  apply of_decide_eq_true
  kernel_rfl

theorem transposed_coordinate_absent :
    .receive [⟨"outer",2⟩,⟨"inner",1⟩] (qualifyProtocolSite (some "first") "message") ∉
      ((normalized model 2 3 true true 17).run (handler model) ([],0)).events := by
  rw [← source_normalized, source_exact]
  apply of_decide_eq_true
  kernel_rfl

theorem reply_return_receipt :
    let run := (normalized model 2 3 true true 17).run (handler model) ([],0)
    (run.outcome,run.state) = (.returned (.cons (some true) (.cons (some 11) .nil)),([],12)) := by
  rw [← source_normalized, source_exact]
  kernel_rfl

theorem helper_abort_receipt : (normalized model 2 3 true false 17).run (handler model) ([],0) =
    ⟨.stopped .abort,([⟨"outer",0⟩,⟨"inner",0⟩],0),
      [.enter ⟨"outer",0⟩,.enter ⟨"inner",0⟩]⟩ := by
  rw [← source_normalized, source_exact]
  kernel_rfl
theorem guard_reject_receipt : (normalized model 2 3 false true 17).run (handler model) ([],0) =
    ⟨.stopped .reject,([⟨"outer",0⟩,⟨"inner",0⟩],0),
      [.enter ⟨"outer",0⟩,.enter ⟨"inner",0⟩]⟩ := by
  rw [← source_normalized, source_exact]
  kernel_rfl
theorem zero_repeat_receipt : (normalized model 0 3 false false 17).run (handler model) ([],0) =
    ⟨.returned (.cons (some false) (.cons (some 17) .nil)),([],0),[]⟩ := by
  rw [← source_normalized, source_exact]
  kernel_rfl
theorem excessive_count_receipt : (normalized model 4 3 true true 17).run (handler model) ([],0) =
    ⟨.stopped .refused,([],0),[]⟩ := by
  rw [← source_normalized, source_exact]
  kernel_rfl
theorem excessive_inner_count_receipt : (normalized model 2 5 true true 17).run (handler model) ([],0) =
    ⟨.stopped .refused,([⟨"outer",0⟩],0),[.enter ⟨"outer",0⟩]⟩ := by
  rw [← source_normalized, source_exact]
  kernel_rfl

end Controls

namespace FiatShamir
abbrev field : String := "bls12-381.fr"
abbrev contract : String := "random.bls12-381.fr/0"
abbrev inputs : List Ty := [.boolean, .service contract, .service contract]
abbrev outputs : List Ty := [.boolean, .field field, .field field]
def runSignature : ProtocolSignature :=
  ⟨"FSRoot", ["P","V"], inputs, outputs, [[1],[1],[0]], [[1],[0,1],[0,1]]⟩
def runBody : Region protocolDialect inputs outputs :=
  .letOp (.mark "private") .nil .nil <|
  .letOp (.draw 0 field "private") (.cons (.there (.there .here)) .nil) .nil <|
  .letOp (.mark "m") .nil .nil <|
  .letOp (.exchange (.field field) 0 1 "m") (.cons .here .nil) .nil <|
  .letOp (.mark "q") .nil .nil <|
  .letOp (.draw 1 field "q") (.cons (.there (.there (.there .here))) .nil) .nil <|
  .letOp (.mark "d") .nil .nil <|
  .letOp (.exchange (.field field) 1 0 "d") (.cons .here .nil) .nil <|
  .ret (.cons (.there (.there (.there (.there .here))))
    (.cons (.there (.there .here)) (.cons .here .nil)))
def snapshot : Snapshot where
  source := "sha256:" ++ String.ofList (List.replicate 64 '1')
  entry := "FSRoot"
  domains := []
  relations := []
  bindings := []
  definitions := [.function ⟨"FSRoot", .protocol, .publicDef, inputs, outputs,
    some ⟨["P","V"], [["V"],["V"],["P"]], [["V"],["P","V"],["P","V"]]⟩,
    [], some (.protocol ⟨"FSRoot", []⟩), .block [
      .instruction (.draw "P" field) [2] [.field field] [] "private",
      .instruction (.exchange "P" "V") [0] [.field field] [] "m",
      .instruction (.draw "V" field) [3] [.field field] [] "q",
      .instruction (.exchange "V" "P") [0] [.field field] [] "d"] (.ret [4,2,0])⟩]
  contracts := [⟨"FSRoot", []⟩]
  catalogue := ZkcExamples.Structured.RepeatData.snapshot.catalogue
structured_views snapshot helpers [] protocols [run]
abbrev signature := runSignature
example : Structured.check snapshot = .ok program := kernel_admission

def context : Context := .fiatShamir "FSRoot" ["P","V"] 0 1 1 contract
  (some (.draw field)) "suite" [("q","d")]
def policy : Policy := ⟨"FSRoot", "P", "V", 0, "suite", [1], [0], [("q","d")], "zkc.framed/0", ""⟩
def privatePort : ServicePort := ⟨"service_0", "P", 2, 0, contract⟩
def privateTemplate : Template :=
  ⟨"FSRoot", [], ["query","FSRoot","private","input_2",contract,"draw","P"]⟩
def messageTemplate : Template := ⟨"FSRoot", [], ["message","FSRoot","m","m","P","V"]⟩
def drawTemplate : Template := ⟨"FSRoot", [], ["query","FSRoot","q","input_1",contract,"draw","V"]⟩
def deliveryTemplate : Template := ⟨"FSRoot", [], ["message","FSRoot","d","d","V","P"]⟩
def routing (mode : Domain.Mode) : Routing :=
  ⟨snapshot, context, mode, 73, [messageTemplate,deliveryTemplate], [drawTemplate],
    [⟨drawTemplate,deliveryTemplate⟩], [⟨91,privatePort,privateTemplate⟩]⟩
def privateOrigin : Origin :=
  (Domain.localOrigin context privatePort (.draw field) privateTemplate []).getD (context.query "private" (.draw field))
def messageOrigin : Origin := context.message "m" 0 1
def drawOrigin : Origin := context.query "q" (.draw field)
def deliveryOrigin : Origin := context.message "d" 1 0

theorem routes (mode : Domain.Mode) :
    (routing mode).message [] "m" 0 1 = some messageOrigin ∧
    (routing mode).message [] "d" 1 0 = some deliveryOrigin ∧
    (routing mode).draw [] "q" field 73 = some drawOrigin ∧
    (routing mode).delivery [] "d" field 1 = some (drawOrigin,deliveryOrigin) ∧
    (routing mode).local [] "private" field 91 = some (privatePort,privateOrigin) := by
  cases mode <;> exact ⟨by kernel_rfl, by kernel_rfl, by kernel_rfl, by kernel_rfl, by kernel_rfl⟩

def producer : Zkc.Construction.Participant :=
  ⟨snapshot.source, snapshot.source, policy, "FSRoot.P", [.transcript "suite"],
    [.data (.field field), .data (.field field), .transcript "suite"], [
      ⟨.indicesEmpty, [], [.indices], []⟩,
      ⟨.localService privatePort (.draw field) privateTemplate [], [], [.data (.field field)], []⟩,
      ⟨.send "m" "m" "V", [2], [], []⟩,
      ⟨.observe "suite" messageTemplate, [0,2,1], [.transcript "suite"], []⟩,
      ⟨.challenge "suite" field drawTemplate, [3,1], [.data (.field field),.transcript "suite"], []⟩,
      ⟨.observe "suite" deliveryTemplate, [5,4,1], [.transcript "suite"], []⟩], [2,4,6], [privatePort]⟩
def validator : Zkc.Construction.Participant :=
  ⟨snapshot.source, snapshot.source, policy, "FSRoot.V", [.data .boolean,.transcript "suite"],
    [.data .boolean,.data (.field field),.data (.field field),.transcript "suite"], [
      ⟨.indicesEmpty, [], [.indices], []⟩,
      ⟨.receive "m" "m" "P" (.field field), [], [.data (.field field)], []⟩,
      ⟨.observe "suite" messageTemplate, [1,3,2], [.transcript "suite"], []⟩,
      ⟨.challenge "suite" field drawTemplate, [4,2], [.data (.field field),.transcript "suite"], []⟩,
      ⟨.observe "suite" deliveryTemplate, [6,5,2], [.transcript "suite"], []⟩], [0,3,5,7], []⟩

theorem context_checked : exportContext snapshot validator = some context := by kernel_rfl
theorem producer_policy_checked : Context.ofPolicy producer.policy ["P","V"] contract
    (some (.draw field)) = some context := by kernel_rfl
theorem validator_checked : checkCompiled imported validator = .ok () := by kernel_rfl
theorem producer_checked : AuthoredPair.checkProducer program context producer = .ok () := by kernel_rfl
theorem producer_occurrences : SourceOccurrences.check snapshot context producer = .ok () := by kernel_rfl
theorem ports_checked : SourceOccurrences.servicePorts snapshot policy "P" = some [privatePort] := by kernel_rfl

def producerView : Domain.View.Block model.toCarriers :=
  Domain.View.sequence (Domain.View.indicesEmpty [.indices]) <|
  Domain.View.sequence (Domain.View.localService context privatePort (.draw field) privateTemplate [] [] [.data (.field field)]) <|
  Domain.View.sequence (Domain.View.send "m" "m" "V" 2 []) <|
  Domain.View.sequence (Domain.View.observe context "suite" messageTemplate 0 2 1 [.transcript "suite"]) <|
  Domain.View.sequence (Domain.View.challenge context "suite" field drawTemplate 3 1 [.data (.field field),.transcript "suite"]) <|
  Domain.View.sequence (Domain.View.observe context "suite" deliveryTemplate 5 4 1 [.transcript "suite"]) Domain.View.empty

def validatorView : Domain.View.Block model.toCarriers :=
  Domain.View.sequence (Domain.View.indicesEmpty [.indices]) <|
  Domain.View.sequence (Domain.View.receive "m" "m" "P" (.field field) [.data (.field field)]) <|
  Domain.View.sequence (Domain.View.observe context "suite" messageTemplate 1 3 2 [.transcript "suite"]) <|
  Domain.View.sequence (Domain.View.challenge context "suite" field drawTemplate 4 2 [.data (.field field),.transcript "suite"]) <|
  Domain.View.sequence (Domain.View.observe context "suite" deliveryTemplate 6 5 2 [.transcript "suite"]) Domain.View.empty

theorem producer_view : Domain.Correspondence.Block (program := program) (context := context)
    producer.instructions (producerView model) := by
  apply Domain.Correspondence.sequence (Domain.Correspondence.indicesEmpty _)
  apply Domain.Correspondence.sequence (Domain.Correspondence.localService _ _ _ _ _ _)
  apply Domain.Correspondence.sequence (Domain.Correspondence.send _ _ _ _ _)
  apply Domain.Correspondence.sequence (Domain.Correspondence.observe _ _ _ _ _ _)
  apply Domain.Correspondence.sequence (Domain.Correspondence.challenge _ _ _ _ _ _)
  exact Domain.Correspondence.sequence (Domain.Correspondence.observe _ _ _ _ _ _) Domain.Correspondence.empty

theorem validator_view : Domain.Correspondence.Block (program := program) (context := context)
    validator.instructions (validatorView model) := by
  apply Domain.Correspondence.sequence (Domain.Correspondence.indicesEmpty _)
  apply Domain.Correspondence.sequence (Domain.Correspondence.receive _ _ _ _ _)
  apply Domain.Correspondence.sequence (Domain.Correspondence.observe _ _ _ _ _ _)
  apply Domain.Correspondence.sequence (Domain.Correspondence.challenge _ _ _ _ _ _)
  exact Domain.Correspondence.sequence (Domain.Correspondence.observe _ _ _ _ _ _) Domain.Correspondence.empty

def sourceInputs (mode : Domain.Mode) (accept : Bool) : Values (Component model.Value) inputs :=
  match mode with
  | .producer => .cons none (.cons none (.cons (some 91) .nil))
  | .validator => .cons (some accept) (.cons (some 73) (.cons none .nil))
def source (mode : Domain.Mode) (accept : Bool) :=
  Occurrence.participant model program (match mode with | .producer => 0 | .validator => 1)
    (sourceInputs model mode accept)

def messageEvent (value : model.Field field) : Domain.Event model.toCarriers := .message messageOrigin (.field field value)
def deliveryEvent (value : model.Field field) : Domain.Event model.toCarriers := .message deliveryOrigin (.field field value)
def afterMessage (history : Domain.History model.toCarriers) (value : model.Field field) := history ++ [messageEvent model value]
def afterQuery (history : Domain.History model.toCarriers) (value : model.Field field) := afterMessage model history value ++ [.challenge drawOrigin]
def finalHistory (history : Domain.History model.toCarriers) (first last : model.Field field) := afterQuery model history first ++ [deliveryEvent model last]

def normal (mode : Domain.Mode) (accept : Bool) (history : Domain.History model.toCarriers) :
    PIR.Process (Domain.effects model.toCarriers) (Values (Component model.Value) outputs × State model.toCarriers) :=
  ((match mode with
  | .producer => PIR.Process.call (.localService privatePort privateOrigin) fun first =>
      .call (.send "m" "m" "V" (.field field first)) fun _ => .done first
  | .validator => PIR.Process.call (.receive (.field field) "m" "m" "P") .done) :
    PIR.Process (Domain.effects model.toCarriers) (model.Field field)).bind fun first =>
  .call (.observe (messageEvent model first)) fun _ =>
  .call (.query (afterMessage model history first) drawOrigin) fun last =>
  .call (.observe (deliveryEvent model last)) fun _ =>
    .done (.cons (match mode with | .producer => none | .validator => some accept)
      (.cons (some first) (.cons (some last) .nil)), ⟨[],finalHistory model history first last⟩)

theorem source_normal (mode : Domain.Mode) (accept : Bool) (history : Domain.History model.toCarriers) :
    fold (routing mode) (source model mode accept) ⟨[],history⟩ = normal model mode accept history := by
  cases mode <;> kernel_rfl

def producerInputs (history : Domain.History model.toCarriers) : Domain.Environment model.toCarriers := [.transcript "suite" history]
def validatorInputs (accept : Bool) (history : Domain.History model.toCarriers) : Domain.Environment model.toCarriers :=
  [.data (.boolean accept),.transcript "suite" history]
private def p1 (history : Domain.History model.toCarriers) := producerInputs model history ++ [.indices []]
private def p2 (history : Domain.History model.toCarriers) (first : model.Field field) := p1 model history ++ [.data (.field field first)]
private def p3 (history : Domain.History model.toCarriers) (first : model.Field field) := p2 model history first ++ [.transcript "suite" (afterMessage model history first)]
private def p4 (history : Domain.History model.toCarriers) (first last : model.Field field) := p3 model history first ++ [.data (.field field last),.transcript "suite" (afterQuery model history first)]
private def p5 (history : Domain.History model.toCarriers) (first last : model.Field field) := p4 model history first last ++ [.transcript "suite" (finalHistory model history first last)]
private def v1 (accept : Bool) (history : Domain.History model.toCarriers) := validatorInputs model accept history ++ [.indices []]
private def v2 (accept : Bool) (history : Domain.History model.toCarriers) (first : model.Field field) := v1 model accept history ++ [.data (.field field first)]
private def v3 (accept : Bool) (history : Domain.History model.toCarriers) (first : model.Field field) := v2 model accept history first ++ [.transcript "suite" (afterMessage model history first)]
private def v4 (accept : Bool) (history : Domain.History model.toCarriers) (first last : model.Field field) := v3 model accept history first ++ [.data (.field field last),.transcript "suite" (afterQuery model history first)]
private def v5 (accept : Bool) (history : Domain.History model.toCarriers) (first last : model.Field field) := v4 model accept history first last ++ [.transcript "suite" (finalHistory model history first last)]

private def producerTarget (history : Domain.History model.toCarriers) : PIR.Process (Domain.effects model.toCarriers) (Domain.Result model.toCarriers) :=
  .call (.checkpoint (producerInputs model history)) fun _ =>
  .call (.checkpoint (producerInputs model history)) fun _ =>
  .call (.checkpoint (p1 model history)) fun _ =>
  .call (.checkpoint (p1 model history)) fun _ =>
  .call (.localService privatePort privateOrigin) fun first =>
  .call (.checkpoint (p2 model history first)) fun _ =>
  .call (.checkpoint (p2 model history first)) fun _ =>
  .call (.send "m" "m" "V" (.field field first)) fun _ =>
  .call (.checkpoint (p2 model history first)) fun _ =>
  .call (.checkpoint (p2 model history first)) fun _ =>
  .call (.observe (messageEvent model first)) fun _ =>
  .call (.checkpoint (p3 model history first)) fun _ =>
  .call (.checkpoint (p3 model history first)) fun _ =>
  .call (.query (afterMessage model history first) drawOrigin) fun last =>
  .call (.checkpoint (p4 model history first last)) fun _ =>
  .call (.checkpoint (p4 model history first last)) fun _ =>
  .call (.observe (deliveryEvent model last)) fun _ =>
  .call (.checkpoint (p5 model history first last)) fun _ =>
    .done ⟨[.data (.field field first),.data (.field field last),.transcript "suite" (finalHistory model history first last)],p5 model history first last⟩
private def validatorTarget (accept : Bool) (history : Domain.History model.toCarriers) : PIR.Process (Domain.effects model.toCarriers) (Domain.Result model.toCarriers) :=
  .call (.checkpoint (validatorInputs model accept history)) fun _ =>
  .call (.checkpoint (validatorInputs model accept history)) fun _ =>
  .call (.checkpoint (v1 model accept history)) fun _ =>
  .call (.checkpoint (v1 model accept history)) fun _ =>
  .call (.receive (.field field) "m" "m" "P") fun first =>
  .call (.checkpoint (v2 model accept history first)) fun _ =>
  .call (.checkpoint (v2 model accept history first)) fun _ =>
  .call (.observe (messageEvent model first)) fun _ =>
  .call (.checkpoint (v3 model accept history first)) fun _ =>
  .call (.checkpoint (v3 model accept history first)) fun _ =>
  .call (.query (afterMessage model history first) drawOrigin) fun last =>
  .call (.checkpoint (v4 model accept history first last)) fun _ =>
  .call (.checkpoint (v4 model accept history first last)) fun _ =>
  .call (.observe (deliveryEvent model last)) fun _ =>
  .call (.checkpoint (v5 model accept history first last)) fun _ =>
    .done ⟨[.data (.boolean accept),.data (.field field first),.data (.field field last),.transcript "suite" (finalHistory model history first last)],v5 model accept history first last⟩

private theorem producer_target (history : Domain.History model.toCarriers) :
    Domain.participant model program context producer (producerInputs model history) = producerTarget model history := by
  rw [Domain.Correspondence.participant producer (producer_view model)]
  kernel_rfl
private theorem validator_target (accept : Bool) (history : Domain.History model.toCarriers) :
    Domain.participant model program context validator (validatorInputs model accept history) = validatorTarget model accept history := by
  rw [Domain.Correspondence.participant validator (validator_view model)]
  kernel_rfl

/-- Both source roles, all private-service/receive/query replies, and the full
profile-owned return. No reference evaluator or root equality is a premise. -/
def producer_composed (accept : Bool) (history : Domain.History model.toCarriers) :
    Simulation (CompleteReturns signature context 0 producer)
      (fun _ frame => ArtifactBinding.Captures (producerInputs model history) frame)
      (fold (routing .producer) (source model .producer accept) ⟨[],history⟩)
      (Domain.participant model program context producer (producerInputs model history)) := by
  rw [source_normal, producer_target]
  unfold normal producerTarget
  simp only [PIR.Process.bind]
  repeat' apply Simulation.checkpoint _ (by simp [ArtifactBinding.Captures,producerInputs,p1])
  apply Simulation.call
  intro first
  repeat' apply Simulation.checkpoint _ (by simp [ArtifactBinding.Captures,producerInputs,p1,p2])
  apply Simulation.call
  intro sent
  repeat' apply Simulation.checkpoint _ (by simp [ArtifactBinding.Captures,producerInputs,p1,p2])
  apply Simulation.call
  intro observed
  repeat' apply Simulation.checkpoint _ (by simp [ArtifactBinding.Captures,producerInputs,p1,p2,p3])
  apply Simulation.call
  intro last
  repeat' apply Simulation.checkpoint _ (by simp [ArtifactBinding.Captures,producerInputs,p1,p2,p3,p4])
  apply Simulation.call
  intro observed
  apply Simulation.checkpoint _ (by simp [ArtifactBinding.Captures,producerInputs,p1,p2,p3,p4,p5])
  exact .done ⟨⟨[.data (.field field),.data (.field field)],rfl,rfl⟩,
    ⟨[.data (.field field first),.data (.field field last)],rfl,rfl⟩,rfl,rfl,rfl⟩

def validator_composed (accept : Bool) (history : Domain.History model.toCarriers) :
    Simulation (CompleteReturns signature context 1 validator)
      (fun _ frame => ArtifactBinding.Captures (validatorInputs model accept history) frame)
      (fold (routing .validator) (source model .validator accept) ⟨[],history⟩)
      (Domain.participant model program context validator (validatorInputs model accept history)) := by
  rw [source_normal, validator_target]
  unfold normal validatorTarget
  simp only [PIR.Process.bind]
  repeat' apply Simulation.checkpoint _ (by simp [ArtifactBinding.Captures,validatorInputs,v1])
  apply Simulation.call
  intro first
  repeat' apply Simulation.checkpoint _ (by simp [ArtifactBinding.Captures,validatorInputs,v1,v2])
  apply Simulation.call
  intro observed
  repeat' apply Simulation.checkpoint _ (by simp [ArtifactBinding.Captures,validatorInputs,v1,v2,v3])
  apply Simulation.call
  intro last
  repeat' apply Simulation.checkpoint _ (by simp [ArtifactBinding.Captures,validatorInputs,v1,v2,v3,v4])
  apply Simulation.call
  intro observed
  apply Simulation.checkpoint _ (by simp [ArtifactBinding.Captures,validatorInputs,v1,v2,v3,v4,v5])
  exact .done ⟨⟨[.data .boolean,.data (.field field),.data (.field field)],rfl,rfl⟩,
    ⟨[.data (.boolean accept),.data (.field field first),.data (.field field last)],rfl,rfl⟩,rfl,rfl,rfl⟩


def occurrenceView (mode : Domain.Mode) (accept : Bool) :
    PIR.Process (Occurrence.signature model.toCarriers) (Values (Component model.Value) outputs) :=
  match mode with
  | .producer =>
    .call (.action (.query "private" field (.cons 91 .nil))) fun first =>
    .call (.action (.send "m" 1 first)) fun _ =>
    .call (.action (.receive (.field field) "d" 1)) fun last =>
      .done (.cons none (.cons (some first) (.cons (some last) .nil)))
  | .validator =>
    .call (.action (.receive (.field field) "m" 0)) fun first =>
    .call (.action (.query "q" field (.cons 73 .nil))) fun last =>
    .call (.action (.send "d" 0 last)) fun _ =>
      .done (.cons (some accept) (.cons (some first) (.cons (some last) .nil)))

theorem source_occurrences (mode : Domain.Mode) (accept : Bool) :
    source model mode accept = occurrenceView model mode accept := by
  cases mode <;> kernel_rfl

/-- Coverage is indexed by both actual source roles, independently of the
list of proposed routes and for every private/query/message reply. -/
def route_coverage (mode : Domain.Mode) (accept : Bool) :
    RouteCoverage (routing mode) [] [] (source model mode accept) := by
  rw [source_occurrences]
  cases mode with
  | producer =>
    apply RouteCoverage.action
    · exact .inr ⟨privatePort,privateOrigin,(routes .producer).2.2.2.2,rfl⟩
    · intro first
      apply RouteCoverage.action
      · exact ⟨rfl,messageOrigin,(routes .producer).1⟩
      · intro sent
        apply RouteCoverage.action
        · exact ⟨drawOrigin,deliveryOrigin,(routes .producer).2.2.2.1,rfl⟩
        · exact fun last => .done _ _
  | validator =>
    apply RouteCoverage.action
    · exact ⟨rfl,messageOrigin,(routes .validator).1⟩
    · intro first
      apply RouteCoverage.action
      · exact .inl ⟨rfl,drawOrigin,(routes .validator).2.2.1,rfl⟩
      · intro last
        apply RouteCoverage.action
        · exact ⟨rfl,deliveryOrigin,(routes .validator).2.1⟩
        · exact fun sent => .done _ _

/-- These are the transcript readbacks at actual observation checkpoints.
The private reply and both public replies also occupy their exact SSA slots. -/
theorem checkpoint_readbacks (accept : Bool) (history : Domain.History model.toCarriers)
    (first last : model.Field field) :
    (p2 model history first)[2]? = some (.data (.field field first)) ∧
    (p3 model history first)[3]? = some (.transcript "suite" (afterMessage model history first)) ∧
    (p4 model history first last)[5]? = some (.transcript "suite" (afterQuery model history first)) ∧
    (p5 model history first last)[6]? = some (.transcript "suite" (finalHistory model history first last)) ∧
    (v3 model accept history first)[4]? = some (.transcript "suite" (afterMessage model history first)) ∧
    (v4 model accept history first last)[6]? = some (.transcript "suite" (afterQuery model history first)) ∧
    (v5 model accept history first last)[7]? = some (.transcript "suite" (finalHistory model history first last)) := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem producer_no_invented_events (accept : Bool) (history : Domain.History model.toCarriers) :
    ((Domain.participant model program context producer (producerInputs model history)).bind
      (fun _ => .done ())).interpret forgetCheckpoints =
    ((fold (routing .producer) (source model .producer accept) ⟨[],history⟩).bind
      (fun _ => .done ())).interpret forgetCheckpoints :=
  (producer_composed model accept history).shape

theorem validator_no_invented_events (accept : Bool) (history : Domain.History model.toCarriers) :
    ((Domain.participant model program context validator (validatorInputs model accept history)).bind
      (fun _ => .done ())).interpret forgetCheckpoints =
    ((fold (routing .validator) (source model .validator accept) ⟨[],history⟩).bind
      (fun _ => .done ())).interpret forgetCheckpoints :=
  (validator_composed model accept history).shape

example : (routing .validator).draw [] "q" field 1 = none := by kernel_rfl
example : (routing .producer).delivery [⟨"unreached",0⟩] "d" field 1 = none := by kernel_rfl
example : (routing .producer).delivery [] "d" "wrong-field" 1 = none := by kernel_rfl
example : (routing .producer).local [] "private" field 73 = none := by kernel_rfl
example : (routing .validator).draw [] "private" field 91 = none := by kernel_rfl
example : (routing .producer).local [] "q" field 73 = none := by kernel_rfl

/-- Keep the message but associate it with the private draw: the admitted
source def-use relation forbids this proposed public delivery. -/
example : ({routing .producer with deliveries := [⟨privateTemplate,deliveryTemplate⟩]} : Routing).delivery
    [] "d" field 1 = none := by kernel_rfl

end FiatShamir

end Tests.SourceConnectionPilot
