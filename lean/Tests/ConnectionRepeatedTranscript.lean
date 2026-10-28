import Zkc.Construction.ConnectionApplications
import Zkc.Construction.ConnectionOrigins
import Zkc.Construction.ConnectionLayout
import ZkcTools.ConstructionBindings.Inputs
import Zkc.Construction.ConnectionLoopFrames
import Zkc.Construction.DomainViewLaws
import Zkc.Construction.OriginalEffects
import Zkc.Construction.Compiled
import Zkc.Construction.AuthoredPair
import Zkc.Source.Structured.UnitViews
import ZkcExamples.Structured.RepeatData

/-! A shared public Fiat--Shamir round invoked twice inside two retained symbolic repeats.
Every receive/query reply is arbitrary. Counts and callback indices are symbolic;
compiled indicesAppend supplies the exact ordered coordinate readback. -/
set_option autoImplicit false
set_option Elab.async false
set_option smartUnfolding true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 16000
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Tests.ConnectionRepeatedTranscript
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open NormalForm Original

abbrev field : String := "bls12-381.fr"
abbrev contract : String := "random.bls12-381.fr/0"
abbrev stateTypes : List Ty := [.field field, .field field]
abbrev stepInputs : List Ty := [.boolean, .service contract, .field field]
abbrev rootInputs : List Ty := [.index, .index, .boolean, .service contract, .field field, .field field]
abbrev rootOutputs : List Ty := [.boolean, .field field, .field field]
def stepSignature : ProtocolSignature :=
  ⟨"round", ["P","V"], stepInputs, stateTypes, [[1],[1],[0,1]], [[0,1],[0,1]]⟩
def runSignature : ProtocolSignature :=
  ⟨"main", ["P","V"], rootInputs, rootOutputs, [[0,1],[0,1],[1],[1],[0,1],[0,1]], [[1],[0,1],[0,1]]⟩
def stepBody : Region protocolDialect stepInputs stateTypes :=
  .letOp (.mark "g") .nil .nil <|
  .letOp (.guard 1 "g") (.cons .here .nil) .nil <|
  .letOp (.mark "m") .nil .nil <|
  .letOp (.exchange (.field field) 0 1 "m") (.cons (.there (.there .here)) .nil) .nil <|
  .letOp (.mark "q") .nil .nil <|
  .letOp (.draw 1 field "q") (.cons (.there (.there .here)) .nil) .nil <|
  .letOp (.mark "d") .nil .nil <|
  .letOp (.exchange (.field field) 1 0 "d") (.cons .here .nil) .nil <|
  .ret (.cons (.there (.there .here)) (.cons .here .nil))
def spec : RepeatSpec := ⟨stateTypes, [.boolean,.service contract], [0,1], [[0,1],[0,1]], 5⟩
def callbackBody : Region protocolDialect (.index :: (spec.state ++ spec.captures)) stateTypes :=
  .letOp (.mark "first") .nil .nil <|
  .letOp (.protocolApply stepSignature [0,1] "first")
    (.cons (.there (.there (.there .here)))
      (.cons (.there (.there (.there (.there .here)))) (.cons (.there .here) .nil))) .nil <|
  .letOp (.mark "second") .nil .nil <|
  .letOp (.protocolApply stepSignature [0,1] "second")
    (.cons (.there (.there (.there (.there (.there .here)))))
      (.cons (.there (.there (.there (.there (.there (.there .here)))))) (.cons .here .nil))) .nil <|
  .ret (.cons .here (.cons (.there .here) .nil))
def outerSpec : RepeatSpec := ⟨stateTypes, [.index,.boolean,.service contract], [0,1], [[0,1],[0,1]], 3⟩
def outerBody : Region protocolDialect (.index :: (outerSpec.state ++ outerSpec.captures)) stateTypes :=
  .letOp (.mark "inner") .nil .nil <|
  .letOp (.repeat spec "inner")
    (.cons (.there (.there (.there .here))) (.cons (.there .here)
      (.cons (.there (.there .here)) (.cons (.there (.there (.there (.there .here))))
        (.cons (.there (.there (.there (.there (.there .here))))) .nil)))))
    (.cons callbackBody .nil) <|
  .ret (.cons .here (.cons (.there .here) .nil))
def runBody : Region protocolDialect rootInputs rootOutputs :=
  .letOp (.mark "outer") .nil .nil <|
  .letOp (.repeat outerSpec "outer")
    (.cons .here (.cons (.there (.there (.there (.there .here))))
      (.cons (.there (.there (.there (.there (.there .here)))))
        (.cons (.there .here) (.cons (.there (.there .here))
          (.cons (.there (.there (.there .here))) .nil))))))
    (.cons outerBody .nil) <|
  .ret (.cons (.there (.there (.there (.there .here)))) (.cons .here (.cons (.there .here) .nil)))
private def protocol (signature : ProtocolSignature) (body : Block) : Definition :=
  .function ⟨signature.name, .protocol, .publicDef, signature.inputs, signature.outputs,
    some ⟨["P","V"], signature.inputScopes.map (List.map fun i => ["P","V"].getD i ""),
      signature.outputScopes.map (List.map fun i => ["P","V"].getD i "")⟩,
    [], some (.protocol ⟨signature.name, []⟩), body⟩
def snapshot : Snapshot where
  source := "sha256:" ++ String.ofList (List.replicate 64 '2')
  entry := "main"
  domains := []
  relations := []
  bindings := []
  definitions := [
    protocol stepSignature (.block [
      .instruction (.guard "V") [0] [] [] "g",
      .instruction (.exchange "P" "V") [2] [.field field] [] "m",
      .instruction (.draw "V" field) [2] [.field field] [] "q",
      .instruction (.exchange "V" "P") [0] [.field field] [] "d"] (.ret [2,0])),
    protocol runSignature (.block [
      .instruction (.protocolRepeat 2 3 ["P","V"] [["P","V"],["P","V"]]) [0,4,5,1,2,3] stateTypes
        [.region [.index,.field field,.field field,.index,.boolean,.service contract] stateTypes
          (.block [
            .instruction (.protocolRepeat 2 5 ["P","V"] [["P","V"],["P","V"]]) [3,1,2,4,5] stateTypes
              [.region [.index,.field field,.field field,.boolean,.service contract] stateTypes
                (.block [
                  .instruction (.protocolApply "round" ["P","V"]) [3,4,1] stateTypes [] "first",
                  .instruction (.protocolApply "round" ["P","V"]) [5,6,0] stateTypes [] "second"] (.yield [0,1]))]
              "inner"] (.yield [0,1]))]
        "outer"] (.ret [4,0,1]))]
  contracts := [⟨"round",[]⟩,⟨"main",[]⟩]
  catalogue := ZkcExamples.Structured.RepeatData.snapshot.catalogue
structured_views snapshot helpers [] protocols [step, run]
theorem step_body_exact : stepDefinition.body = stepBody := rfl
theorem root_body : runDefinition.body = runBody := rfl
example : Structured.check snapshot = .ok program := kernel_admission

def qualified (site leaf : String) := qualifyProtocolSite (some site) leaf
def context : Context := .fiatShamir "main" ["P","V"] 0 1 3 contract
  (some (.draw field)) "suite" [(qualified "first" "q",qualified "first" "d"),
    (qualified "second" "q",qualified "second" "d")]
theorem suite_eq : context.suite = "suite" := rfl

def policy : Policy := ⟨"main","P","V",0,"suite",[3],[0,1,2,4,5],
  [(qualified "first" "q",qualified "first" "d"),(qualified "second" "q",qualified "second" "d")],
  "zkc.framed/0",""⟩
def template (site leaf : String) : Template :=
  ⟨"main",[⟨"repeat","main","outer"⟩,⟨"repeat","main","inner"⟩,⟨"apply","main",site⟩],
    if leaf = "q" then ["query","round","q","input_1",contract,"draw","V"]
    else ["message","round",leaf,leaf,if leaf = "m" then "P" else "V",if leaf = "m" then "V" else "P"]⟩
def routing : Routing := ⟨snapshot,context,.validator,73,
  [template "first" "m",template "first" "d",template "second" "m",template "second" "d"],
  [template "first" "q",template "second" "q"],
  [⟨template "first" "q",template "first" "d"⟩,⟨template "second" "q",template "second" "d"⟩],[]⟩
def stepInstructions (site : String) (historyReference first : Nat) : List Zkc.Construction.Instruction := [
  ⟨.guard (qualified site "g"),[2],[],[]⟩,
  ⟨.receive (qualified site "m") (qualified site "m") "P" (.field field),[],[.data (.field field)],[]⟩,
  ⟨.observe "suite" (template site "m"),[historyReference,first,16],[.transcript "suite"],[]⟩,
  ⟨.challenge "suite" field (template site "q"),[first+1,16],[.data (.field field),.transcript "suite"],[]⟩,
  ⟨.observe "suite" (template site "d"),[first+3,first+2,16],[.transcript "suite"],[]⟩]
def bodyInstructions : List Zkc.Construction.Instruction :=
  [⟨.indicesAppend,[11,12],[.indices],[]⟩] ++
  stepInstructions "first" 15 17 ++ stepInstructions "second" 21 22
def outerInstructions : List Zkc.Construction.Instruction := [
  ⟨.indicesAppend,[6,7],[.indices],[]⟩,
  ⟨.loop "inner" 5 [22,24,26],[1,8,9,10],
    [.data (.field field),.data (.field field),.transcript "suite"],bodyInstructions⟩]
def artifact : Zkc.Construction.Participant :=
  ⟨snapshot.source,snapshot.source,policy,"main.V",
    [.data .index,.data .index,.data .boolean,.data (.field field),.data (.field field),.transcript "suite"],
    [.data .boolean,.data (.field field),.data (.field field),.transcript "suite"],
    [⟨.indicesEmpty,[],[.indices],[]⟩,
      ⟨.loop "outer" 3 [12,13,14],[0,3,4,5],
        [.data (.field field),.data (.field field),.transcript "suite"],outerInstructions⟩],
    [2,7,8,9],[]⟩

theorem context_checked : exportContext snapshot artifact = some context := by kernel_rfl
theorem checked : checkCompiled imported artifact = .ok () := by kernel_rfl

variable (model : DomainModel)
abbrev I := Occurrence.signature model.toCarriers
abbrev helpers := Occurrence.helpers model program.payload
abbrev protocols := Occurrence.table model program.payload

def sourceInputs (count innerCount : Nat) (guard : Bool) (first last : model.Field field) :
    Values (Component model.Value) rootInputs :=
  .cons (some count) (.cons (some innerCount) (.cons (some guard) (.cons (some 73) (.cons (some first) (.cons (some last) .nil)))))
def inputFrame (count innerCount : Nat) (guard : Bool) (first last : model.Field field)
    (history : Domain.History model.toCarriers) : Domain.Environment model.toCarriers :=
  [.data (.index count),.data (.index innerCount),.data (.boolean guard),.data (.field field first),.data (.field field last),.transcript "suite" history]
def rootPattern : InputPattern rootInputs :=
  .cons .present (.cons .present (.cons .present (.cons (.capability contract 73) (.cons .present (.cons .present .nil)))))
def inputABI : InputABI :=
  ⟨artifact.inputs,[.data 0,.data 1,.data 2,.capability 73,.data 3,.data 4]⟩
def inputShape : ConnectionInputs.Shape rootPattern inputABI.locations := by
  derive_connection_inputs
def rootForm : Form [] [] rootPattern.scope rootOutputs :=
  (normalize {} runBody 1 2 rootPattern).toOption.getD (.halt .refused)
def normalized (count innerCount : Nat) (guard : Bool) (first last : model.Field field) :=
  (rootForm.denoteOn model Occurrence.actions (helpers model) (LawResults.empty model) {}
    (runsAtOn model Occurrence.actions Occurrence.iterations (helpers model) (protocols model) {} 1)
    (noCallees model _) (.cons count (.cons innerCount (.cons guard (.cons first (.cons last .nil)))))).bind
      fun values => .done (maskValues 1 runSignature.outputScopes values)

theorem source_normalized (count innerCount : Nat) (guard : Bool) (first last : model.Field field) :
    Occurrence.participant model program 1 (sourceInputs model count innerCount guard first last) =
      normalized model count innerCount guard first last := by
  exact normalize_program_occurrence program {} 1 rootPattern rootForm
    (by kernel_rfl) (by rfl) (by intro other bound different; exact different)
    (LawResults.empty model) (noCallees model _) (sourceInputs model count innerCount guard first last)
    (.cons count (.cons innerCount (.cons guard (.cons first (.cons last .nil)))))
    (by kernel_rfl) (LawsHold.empty _ _) (by intro callee; exact callee.elim0)


def sourceStep (site : String) (guard : Bool) : PIR.Process (I model)
    (Values (Component model.Value) stateTypes) :=
  if guard then
    .call (.action (.receive (.field field) (qualified site "m") 0)) fun first =>
    .call (.action (.query (qualified site "q") field (.cons 73 .nil))) fun last =>
    .call (.action (.send (qualified site "d") 0 last)) fun _ =>
      .done (.cons (some first) (.cons (some last) .nil))
  else .halt .reject

/-- The child retains its actual captured context and payload tables. -/
theorem invoke_step (site : String) (guard : Bool) (seed : Option (model.Field field)) :
    invokeProtocol (protocols model) stepSignature (({} : ProtocolContext).enter site [0,1]) 1
      (.cons (some guard) (.cons (some 73) (.cons seed .nil))) = sourceStep model site guard := by
  change invokeProtocol _ stepDefinition.signature _ _ _ = _
  rw [Occurrence.invoke_body model program.payload stepDefinition step_member]
  cases guard <;> kernel_rfl

private theorem state_eta (values : Values (Component model.Value) stateTypes) :
    Values.cons (values.get .here) (Values.cons (values.get (.there .here)) Values.nil) = values := by
  cases values with | cons first rest => cases rest with | cons last rest => cases rest; rfl

theorem callback_denote (index : Option Nat) (first last : Option (model.Field field)) (guard : Bool) :
    callbackBody.denote (meaningAtOn model Occurrence.actions Occurrence.iterations
      (helpers model) (protocols model) {} 1)
      (Values.cons index (.cons first (.cons last (.cons (some guard) (.cons (some 73) .nil))))).get =
    (sourceStep model "first" guard).bind fun _ => sourceStep model "second" guard := by
  have active (site : String) : (({} : ProtocolContext).enter site [0,1]).contains stepSignature 1 = true := by kernel_rfl
  have raw : callbackBody.denote (meaningAtOn model Occurrence.actions Occurrence.iterations
      (helpers model) (protocols model) {} 1)
      (Values.cons index (.cons first (.cons last (.cons (some guard) (.cons (some 73) .nil))))).get =
    (invokeProtocol (protocols model) stepSignature (({} : ProtocolContext).enter "first" [0,1]) 1
      (.cons (some guard) (.cons (some 73) (.cons first .nil)))).bind fun values =>
    (invokeProtocol (protocols model) stepSignature (({} : ProtocolContext).enter "second" [0,1]) 1
      (.cons (some guard) (.cons (some 73) (.cons (values.get .here) .nil)))).bind fun results =>
      .done (Values.cons (results.get .here) (.cons (results.get (.there .here)) .nil)) := by
    simp only [callbackBody, Region.denote, meaningAtOn, participantMeaningWithOn,
      protocolOperationWithOn, Operands.eval, Regions.denote, Values.get,
      Environment.prepend, Environment.push, SiteObservations.silent, PIR.Process.bind, id_eq, active, ↓reduceIte]
    apply congrArg (PIR.Process.bind _)
    funext values
    cases values with
    | cons first rest =>
      cases rest with
      | cons last rest =>
        cases rest
        simp only [Environment.prepend, Environment.push, Values.get]
        apply congrArg (PIR.Process.bind _)
        funext results
        cases results with
        | cons first rest =>
          cases rest with
          | cons last rest => cases rest; rfl

  rw [raw, invoke_step]
  apply congrArg (PIR.Process.bind _)
  funext values
  rw [invoke_step]
  simp only [state_eta, PIR.Process.bind_done]

abbrev callback : RegionFunction (Component model.Value) (I model)
    (.index :: (spec.state ++ spec.captures),spec.state) := fun values => callbackBody.denote
  (meaningAtOn model Occurrence.actions Occurrence.iterations (helpers model) (protocols model) {} 1) values.get

abbrev outerCallback : RegionFunction (Component model.Value) (I model)
    (.index :: (outerSpec.state ++ outerSpec.captures),outerSpec.state) := fun values => outerBody.denote
  (meaningAtOn model Occurrence.actions Occurrence.iterations (helpers model) (protocols model) {} 1) values.get

theorem outer_denote (index : Option Nat) (first last : Option (model.Field field))
    (innerCount : Option Nat) (guard : Bool) :
    outerCallback model (.cons index (.cons first (.cons last
      (.cons innerCount (.cons (some guard) (.cons (some 73) .nil)))))) =
    denoteRepeatOn spec {} 1 innerCount (.cons first (.cons last .nil))
      (.cons (some guard) (.cons (some 73) .nil)) (callback model) Occurrence.iterations "inner" := by
  simp only [outerCallback, outerBody, Region.denote, meaningAtOn, participantMeaningWithOn,
    protocolOperationWithOn, Regions.denote, Operands.eval, Values.get, Environment.prepend,
    Environment.push, SiteObservations.silent, PIR.Process.bind, id_eq]
  change (denoteRepeatOn spec {} 1 innerCount (.cons first (.cons last .nil))
    (.cons (some guard) (.cons (some 73) .nil)) (callback model) Occurrence.iterations "inner").bind _ = _
  conv_rhs => rw [← PIR.Process.bind_done (denoteRepeatOn spec {} 1 innerCount
    (.cons first (.cons last .nil)) (.cons (some guard) (.cons (some 73) .nil))
    (callback model) Occurrence.iterations "inner")]
  apply congrArg (PIR.Process.bind _)
  funext values
  cases values with
  | cons first rest =>
    cases rest with
    | cons last rest => cases rest; rfl

theorem source_exact (count innerCount : Nat) (guard : Bool) (first last : model.Field field) :
    Occurrence.participant model program 1 (sourceInputs model count innerCount guard first last) =
    (denoteRepeatOn outerSpec {} 1 (some count) (.cons (some first) (.cons (some last) .nil))
      (.cons (some innerCount) (.cons (some guard) (.cons (some 73) .nil)))
      (outerCallback model) Occurrence.iterations "outer").bind
        fun values => .done (.cons (some guard) values) := by
  rw [Occurrence.participant, Occurrence.invoke_body model program.payload _ program.payload.entry_mem]
  change ((runBody.denote (meaningAtOn model Occurrence.actions Occurrence.iterations
    (helpers model) (protocols model) {} 1) (sourceInputs model count innerCount guard first last).get).bind
      fun values => .done (maskValues 1 runSignature.outputScopes values)) = _
  have outputMask (values : Values (Component model.Value) rootOutputs) :
      maskValues 1 runSignature.outputScopes values = values := by
    cases values with
    | cons accept rest =>
      cases rest with
      | cons first rest =>
        cases rest with
        | cons last rest => cases rest; rfl
  simp only [outputMask, PIR.Process.bind_done]
  simp only [runBody, Region.denote, meaningAtOn, participantMeaningWithOn,
    protocolOperationWithOn, Regions.denote, Operands.eval, Values.get,
    Environment.prepend, Environment.push, SiteObservations.silent, PIR.Process.bind, id_eq]
  simp only [sourceInputs, outerSpec, stateTypes, Values.split, Values.get,
    Environment.prepend, Environment.push]
  change ((denoteRepeatOn outerSpec {} 1 (some count) (.cons (some first) (.cons (some last) .nil))
    (.cons (some innerCount) (.cons (some guard) (.cons (some 73) .nil)))
    (outerCallback model) Occurrence.iterations "outer").bind _) = _
  apply congrArg (PIR.Process.bind _)
  funext values
  cases values with
  | cons first rest =>
    cases rest with
    | cons last rest => cases rest; rfl

def origin (site leaf : String) (outerIndex index : Nat) : Origin :=
  Domain.atCoordinates (if leaf = "q" then context.query (qualified site leaf) (.draw field)
    else context.message (qualified site leaf) (if leaf = "m" then 0 else 1) (if leaf = "m" then 1 else 0)) [outerIndex,index]

theorem message_static (site : String) (present : site ∈ ["first","second"])
    (leaf : String) (message : leaf ∈ ["m","d"]) :
    OccurrenceResolution.resolveStatic snapshot context
      (context.message (qualified site leaf) (if leaf = "m" then 0 else 1) (if leaf = "m" then 1 else 0))
      ["outer","inner"] routing.messages = some (template site leaf) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at present message
  rcases present with rfl | rfl <;> rcases message with rfl | rfl <;> kernel_rfl

theorem draw_static (site : String) (present : site ∈ ["first","second"]) :
    OccurrenceResolution.resolveStatic snapshot context (context.query (qualified site "q") (.draw field))
      ["outer","inner"] routing.draws = some (template site "q") := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with rfl | rfl <;> kernel_rfl

theorem message_route (site : String) (present : site ∈ ["first","second"])
    (leaf : String) (message : leaf ∈ ["m","d"]) (outerIndex index : Nat) :
    routing.message [⟨"outer",outerIndex⟩,⟨"inner",index⟩] (qualified site leaf)
      (if leaf = "m" then 0 else 1) (if leaf = "m" then 1 else 0) = some (origin site leaf outerIndex index) := by
  have found := Routing.message_of_static (routing := routing) (message_static site present leaf message)
    [⟨"outer",outerIndex⟩,⟨"inner",index⟩] rfl
  have notQuery : leaf ≠ "q" := by
    rcases List.mem_cons.mp message with rfl | tail
    · decide
    · have same := List.mem_singleton.mp tail; subst leaf; decide
  change routing.message _ _ _ _ = some (Domain.atCoordinates
    (context.message (qualified site leaf) (if leaf = "m" then 0 else 1) (if leaf = "m" then 1 else 0)) [outerIndex,index]) at found
  simpa only [origin, notQuery, ↓reduceIte, List.map_cons, List.map_nil] using found

theorem draw_route (site : String) (present : site ∈ ["first","second"]) (outerIndex index : Nat) :
    routing.draw [⟨"outer",outerIndex⟩,⟨"inner",index⟩] (qualified site "q") field 73 = some (origin site "q" outerIndex index) := by
  exact Routing.draw_of_static (routing := routing) rfl (draw_static site present) [⟨"outer",outerIndex⟩,⟨"inner",index⟩] rfl

theorem template_message (site : String) (leaf : String) (outerIndex index : Nat)
    (message : leaf ∈ ["m","d"]) :
    Domain.templateOrigin context (template site leaf) [outerIndex,index] = some (origin site leaf outerIndex index) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at message
  rcases message with rfl | rfl <;> kernel_rfl

def messageEvent (site : String) (outerIndex index : Nat) (value : model.Field field) : Domain.Event model.toCarriers :=
  .message (origin site "m" outerIndex index) (.field field value)
def deliveryEvent (site : String) (outerIndex index : Nat) (value : model.Field field) : Domain.Event model.toCarriers :=
  .message (origin site "d" outerIndex index) (.field field value)
def afterMessage (site : String) (outerIndex index : Nat) (history : Domain.History model.toCarriers) (value : model.Field field) :=
  history ++ [messageEvent model site outerIndex index value]
def afterQuery (site : String) (outerIndex index : Nat) (history : Domain.History model.toCarriers) (value : model.Field field) :=
  afterMessage model site outerIndex index history value ++ [.challenge (origin site "q" outerIndex index)]
def afterStep (site : String) (outerIndex index : Nat) (history : Domain.History model.toCarriers) (first last : model.Field field) :=
  afterQuery model site outerIndex index history first ++ [deliveryEvent model site outerIndex index last]

def foldedStep (site : String) (outerIndex index : Nat) (guard : Bool) (history : Domain.History model.toCarriers) :
    PIR.Process (Domain.effects model.toCarriers) (Values (Component model.Value) stateTypes × State model.toCarriers) :=
  if guard then
    .call (.receive (.field field) (qualified site "m") (qualified site "m") "P") fun first =>
    .call (.observe (messageEvent model site outerIndex index first)) fun _ =>
    .call (.query (afterMessage model site outerIndex index history first) (origin site "q" outerIndex index)) fun last =>
    .call (.observe (deliveryEvent model site outerIndex index last)) fun _ =>
      .done (.cons (some first) (.cons (some last) .nil),⟨[⟨"outer",outerIndex⟩,⟨"inner",index⟩],afterStep model site outerIndex index history first last⟩)
  else .halt .reject

theorem fold_step (site : String) (present : site ∈ ["first","second"])
    (outerIndex index : Nat) (guard : Bool) (history : Domain.History model.toCarriers) :
    fold routing (sourceStep model site guard) ⟨[⟨"outer",outerIndex⟩,⟨"inner",index⟩],history⟩ =
      foldedStep model site outerIndex index guard history := by
  cases guard
  · rfl
  · change (Original.receive routing ⟨[⟨"outer",outerIndex⟩,⟨"inner",index⟩],history⟩ (.field field) (qualified site "m") 0).bind _ = _
    rw [validator_receive (carriers := model.toCarriers) routing ⟨[⟨"outer",outerIndex⟩,⟨"inner",index⟩],history⟩ (qualified site "m") field 0 (origin site "m" outerIndex index) rfl (message_route site present "m" (by simp) outerIndex index)]
    simp only [PIR.Process.bind]
    congr 1
    funext first
    congr 1
    funext observed
    change (query routing ⟨[⟨"outer",outerIndex⟩,⟨"inner",index⟩],afterMessage model site outerIndex index history first⟩
      (qualified site "q") field 73).bind _ = _
    rw [public_query (carriers := model.toCarriers) routing ⟨[⟨"outer",outerIndex⟩,⟨"inner",index⟩],afterMessage model site outerIndex index history first⟩ (qualified site "q") field 73 (origin site "q" outerIndex index) rfl (draw_route site present outerIndex index)]
    simp only [PIR.Process.bind]
    congr 1
    funext last
    change (send routing ⟨[⟨"outer",outerIndex⟩,⟨"inner",index⟩],afterQuery model site outerIndex index history first⟩
      (.field field) (qualified site "d") 0 last).bind _ = _
    have deliveryRoute : routing.message [⟨"outer",outerIndex⟩,⟨"inner",index⟩] (qualified site "d") 1 0 =
        some (origin site "d" outerIndex index) := message_route site present "d" (by simp) outerIndex index
    simp only [send, show routing.mode = .validator from rfl, show routing.context.validator = 1 from rfl, Ty.isService, ↓reduceDIte, deliveryRoute, Domain.Payload.ofValue]
    rfl

private theorem read_append {env : Domain.Environment model.toCarriers} {reference : Nat}
    {value : Domain.Value model.toCarriers} (read : env[reference]? = some value)
    (tail : Domain.Environment model.toCarriers) : (env ++ tail)[reference]? = some value := by
  have bound : reference < env.length := by
    by_contra outside
    rw [List.getElem?_eq_none (by omega)] at read
    cases read
  rw [List.getElem?_append_left bound, read]

def stepView (site : String) (historyReference first : Nat) : Domain.View.Block model.toCarriers :=
  Domain.View.sequence (Domain.View.guard 2 []) <|
  Domain.View.sequence (Domain.View.receive (qualified site "m") (qualified site "m") "P" (.field field) [.data (.field field)]) <|
  Domain.View.sequence (Domain.View.observe context "suite" (template site "m") historyReference first 16 [.transcript "suite"]) <|
  Domain.View.sequence (Domain.View.challenge context "suite" field (template site "q") (first+1) 16 [.data (.field field),.transcript "suite"]) <|
  Domain.View.sequence (Domain.View.observe context "suite" (template site "d") (first+3) (first+2) 16 [.transcript "suite"]) Domain.View.empty

def stepExtras (site : String) (outerIndex index : Nat) (history : Domain.History model.toCarriers)
    (first last : model.Field field) : Domain.Environment model.toCarriers :=
  [.data (.field field first),.transcript "suite" (afterMessage model site outerIndex index history first),
    .data (.field field last),.transcript "suite" (afterQuery model site outerIndex index history first),
    .transcript "suite" (afterStep model site outerIndex index history first last)]
def StepReturns (site : String) (outerIndex index : Nat) (history : Domain.History model.toCarriers)
    (env : Domain.Environment model.toCarriers)
    (source : Values (Component model.Value) stateTypes × State model.toCarriers)
    (target : Domain.Environment model.toCarriers) : Prop :=
  ∃ first last, source = (.cons (some first) (.cons (some last) .nil),
      ⟨[⟨"outer",outerIndex⟩,⟨"inner",index⟩],afterStep model site outerIndex index history first last⟩) ∧
    target = env ++ stepExtras model site outerIndex index history first last

/-- One shared callee derivation: every reached index, history, and typed reply.
The physical arguments are read equations, discharged at each call site. -/
def step_certificate (site : String) (present : site ∈ ["first","second"]) (outerIndex index : Nat)
    (guard : Bool) (history : Domain.History model.toCarriers)
    (env : Domain.Environment model.toCarriers) (historyReference : Nat)
    (readGuard : env[2]? = some (.data (.boolean guard)))
    (readHistory : env[historyReference]? = some (.transcript "suite" history))
    (readCoordinates : env[16]? = some (.indices [outerIndex,index])) :
    Simulation (StepReturns model site outerIndex index history env)
      (fun _ frame => ArtifactBinding.Captures env frame)
      (fold routing (sourceStep model site guard) ⟨[⟨"outer",outerIndex⟩,⟨"inner",index⟩],history⟩)
      (stepView model site historyReference env.length env) := by
  rw [fold_step model site present]
  unfold stepView Domain.View.sequence
  rw [Domain.View.guard_eq _ _ guard readGuard]
  cases guard
  · apply Simulation.checkpoint _ (by simp [ArtifactBinding.Captures])
    exact .halt .reject
  · simp only [foldedStep, Bool.true_eq, ↓reduceIte, PIR.Process.bind]
    repeat' apply Simulation.checkpoint _ (by simp [ArtifactBinding.Captures])
    rw [Domain.View.receive_eq _ _ _ _ rfl]
    apply Simulation.call
    intro first
    simp only [Domain.Value.encode, Domain.Payload.ofValue, Domain.View.append,
      Domain.sortsMatch, Domain.Value.sort, List.map_cons, List.map_nil, beq_self_eq_true,
      ↓reduceIte, PIR.Process.bind, List.append_assoc]
    repeat' apply Simulation.checkpoint _ (by simp [ArtifactBinding.Captures])
    erw [Domain.View.observe_eq context (template site "m") _ _ _ _ history
      (.field field first) [outerIndex,index] (origin site "m" outerIndex index)
      (read_append model readHistory _) (by simp) (read_append model readCoordinates _)
      (template_message site "m" outerIndex index (by simp)) (by kernel_rfl)]
    apply Simulation.call
    intro observed
    simp only [Domain.View.append, Domain.sortsMatch, Domain.Value.sort, List.map_cons,
      List.map_nil, beq_self_eq_true, ↓reduceIte, PIR.Process.bind, List.append_assoc]
    repeat' apply Simulation.checkpoint _ (by simp [ArtifactBinding.Captures])
    erw [Domain.View.challenge_eq context "suite" field (template site "q") _ _ _
      (afterMessage model site outerIndex index history first) [outerIndex,index] (origin site "q" outerIndex index)
      (by simp [suite_eq, afterMessage, messageEvent]) (read_append model readCoordinates _)
      (by kernel_rfl) (by kernel_rfl)]
    apply Simulation.call
    intro last
    simp only [Domain.View.append, Domain.sortsMatch, Domain.Value.sort, List.map_cons,
      List.map_nil, beq_self_eq_true, ↓reduceIte, PIR.Process.bind, List.append_assoc]
    repeat' apply Simulation.checkpoint _ (by simp [ArtifactBinding.Captures])
    erw [Domain.View.observe_eq context (template site "d") _ _ _ _
      (afterQuery model site outerIndex index history first) (.field field last) [outerIndex,index] (origin site "d" outerIndex index)
      (by simp [suite_eq, afterQuery]) (by simp) (read_append model readCoordinates _)
      (template_message site "d" outerIndex index (by simp)) (by kernel_rfl)]
    apply Simulation.call
    intro observed
    simp only [Domain.View.append, Domain.sortsMatch, Domain.Value.sort, List.map_cons,
      List.map_nil, beq_self_eq_true, ↓reduceIte, PIR.Process.bind, List.append_assoc, Domain.View.empty]
    apply Simulation.checkpoint _ (by simp [ArtifactBinding.Captures])
    exact .done ⟨first,last,rfl,rfl⟩

/-- The shared body derivation transports to the actual declaration, with its
captured child context and the program's actual helper/protocol closures. -/
def application_certificate (site : String) (present : site ∈ ["first","second"])
    (outerIndex index : Nat) (guard : Bool) (seed : Option (model.Field field))
    (history : Domain.History model.toCarriers) (env : Domain.Environment model.toCarriers)
    (historyReference : Nat)
    (readGuard : env[2]? = some (.data (.boolean guard)))
    (readHistory : env[historyReference]? = some (.transcript "suite" history))
    (readCoordinates : env[16]? = some (.indices [outerIndex,index])) :
    Simulation (StepReturns model site outerIndex index history env)
      (fun _ frame => ArtifactBinding.Captures env frame)
      (fold routing (invokeProtocol (protocols model) stepSignature
        (({} : ProtocolContext).enter site [0,1]) 1
        (.cons (some guard) (.cons (some 73) (.cons seed .nil)))) ⟨[⟨"outer",outerIndex⟩,⟨"inner",index⟩],history⟩)
      (stepView model site historyReference env.length env) := by
  have body := invoke_step model site guard seed
  change invokeProtocol (Occurrence.table model program.payload) stepDefinition.signature
    (({} : ProtocolContext).enter site [0,1]) 1
    (.cons (some guard) (.cons (some 73) (.cons seed .nil))) = _ at body
  rw [Occurrence.invoke_body model program.payload stepDefinition step_member] at body
  apply Simulation.linkedApplication model program.payload routing stepDefinition step_member
    (({} : ProtocolContext).enter site [0,1]) 1
    (.cons (some guard) (.cons (some 73) (.cons seed .nil))) ⟨[⟨"outer",outerIndex⟩,⟨"inner",index⟩],history⟩
  rw [body]
  exact step_certificate model site present outerIndex index guard history env historyReference readGuard readHistory readCoordinates


def bodyView : Domain.View.Block model.toCarriers :=
  Domain.View.sequence (Domain.View.indicesAppend 11 12 [.indices]) fun env =>
    (stepView model "first" 15 17 env).bind fun next => stepView model "second" 21 22 next

theorem step_view (site : String) (historyReference first : Nat) :
    Domain.Correspondence.Block (program := program) (context := context)
      (stepInstructions site historyReference first) (stepView model site historyReference first) := by
  apply Domain.Correspondence.sequence (Domain.Correspondence.guard _ _ _)
  apply Domain.Correspondence.sequence (Domain.Correspondence.receive _ _ _ _ _)
  apply Domain.Correspondence.sequence (Domain.Correspondence.observe _ _ _ _ _ _)
  apply Domain.Correspondence.sequence (Domain.Correspondence.challenge _ _ _ _ _ _)
  exact Domain.Correspondence.sequence (Domain.Correspondence.observe _ _ _ _ _ _) Domain.Correspondence.empty

theorem body_view : Domain.Correspondence.Block (program := program) (context := context)
    bodyInstructions (bodyView model) := by
  apply Domain.Correspondence.sequence (Domain.Correspondence.indicesAppend _ _ _)
  intro env
  change Domain.evaluate model program context (stepInstructions "first" 15 17 ++ stepInstructions "second" 21 22) env = _
  rw [Domain.evaluate_append]
  erw [step_view model]
  apply congrArg (PIR.Process.bind _)
  funext next
  exact step_view model "second" 21 22 next

-- Root capture has 7 cells. The outer callback adds 4; its coordinate is
-- cell 11. The inner callback adds 4 more; its exact coordinate is cell 16.
def captured (count innerCount : Nat) (guard : Bool) (first last : model.Field field)
    (history : Domain.History model.toCarriers) := inputFrame model count innerCount guard first last history ++ [.indices []]
def outerInput (count innerCount : Nat) (guard : Bool) (first last : model.Field field)
    (initial : Domain.History model.toCarriers) (outerIndex : Nat)
    (a b : model.Field field) (history : Domain.History model.toCarriers) :=
  captured model count innerCount guard first last initial ++
    [.data (.index outerIndex),.data (.field field a),.data (.field field b),.transcript "suite" history]
def innerCaptured (count innerCount : Nat) (guard : Bool) (first last : model.Field field)
    (initial : Domain.History model.toCarriers) (outerIndex : Nat)
    (a b : model.Field field) (history : Domain.History model.toCarriers) :=
  outerInput model count innerCount guard first last initial outerIndex a b history ++ [.indices [outerIndex]]
def bodyInput (count innerCount : Nat) (guard : Bool) (first last : model.Field field)
    (initial : Domain.History model.toCarriers) (outerIndex : Nat)
    (outerA outerB : model.Field field) (outerHistory : Domain.History model.toCarriers) (index : Nat)
    (a b : model.Field field) (history : Domain.History model.toCarriers) :=
  innerCaptured model count innerCount guard first last initial outerIndex outerA outerB outerHistory ++
    [.data (.index index),.data (.field field a),.data (.field field b),.transcript "suite" history]

private theorem carried_eq (value : Values (Component model.Value) stateTypes)
    (state : State model.toCarriers) (carried : Domain.Environment model.toCarriers)
    (related : CarriedValues context 1 [[0,1],[0,1]] (value,state) carried) :
    ∃ a b, value = .cons (some a) (.cons (some b) .nil) ∧
      carried = [.data (.field field a),.data (.field field b),.transcript "suite" state.history] := by
  cases value with
  | cons a rest =>
    cases rest with
    | cons b rest =>
      cases rest
      obtain ⟨data,encoded,frame⟩ := related
      cases a with
      | none => simp [roleOutputValues] at encoded
      | some a =>
        cases b with
        | none => simp [roleOutputValues] at encoded
        | some b =>
          have exactEncoding : roleOutputValues 1 [[0,1],[0,1]]
              (Values.cons (some a) (.cons (some b) .nil) : Values (Component model.Value) stateTypes) =
              some [.data (.field field a),.data (.field field b)] := rfl
          rw [exactEncoding] at encoded
          cases encoded
          exact ⟨a,b,rfl,frame⟩

abbrev LoopRelation (frames : Frames) :=
  FramedCarriedValues (carriers := model.toCarriers) context 1 [[0,1],[0,1]] frames (types := stateTypes)

/-- The compiled callback shares one callee proof at its two physical call sites.
It starts from the actual carried row and returns the entire row and history. -/
def callback_certificate (count innerCount : Nat) (guard : Bool) (first last : model.Field field)
    (initial : Domain.History model.toCarriers) (outerIndex : Nat)
    (outerA outerB : model.Field field) (outerHistory : Domain.History model.toCarriers) (index : Nat)
    (a b : model.Field field) (history : Domain.History model.toCarriers) :
    Simulation (IterationReturns (LoopRelation model [⟨"outer",outerIndex⟩]) [⟨"outer",outerIndex⟩] "inner" index
        [22,24,26] [.data (.field field),.data (.field field),.transcript "suite"])
      (fun _ frame => ArtifactBinding.Captures (innerCaptured model count innerCount guard first last initial outerIndex outerA outerB outerHistory) frame)
      (fold routing ((callback model) (.cons (some index)
          (.cons (some a) (.cons (some b) (.cons (some guard) (.cons (some 73) .nil))))))
        ⟨[⟨"outer",outerIndex⟩,⟨"inner",index⟩],history⟩)
      (bodyView model (bodyInput model count innerCount guard first last initial outerIndex outerA outerB outerHistory index a b history)) := by
  change Simulation _ _ (fold routing (callbackBody.denote
    (meaningAtOn model Occurrence.actions Occurrence.iterations (helpers model) (protocols model) {} 1)
    (Values.cons (some index) (.cons (some a) (.cons (some b)
      (.cons (some guard) (.cons (some 73) .nil))))).get) _) _
  rw [callback_denote, fold_bind]
  unfold bodyView
  rw [Domain.View.sequence_return _ _ _ _
    (Domain.View.indicesAppend_eq 11 12 _ [outerIndex] index (by rfl) (by rfl))]
  apply Simulation.checkpoint _ (by simp [ArtifactBinding.Captures, innerCaptured, outerInput, captured, inputFrame, bodyInput])
  apply Simulation.checkpoint _ (by simp [ArtifactBinding.Captures, innerCaptured, outerInput, captured, inputFrame, bodyInput])
  have firstCertificate := step_certificate model "first" (by simp) outerIndex index guard history
    (bodyInput model count innerCount guard first last initial outerIndex outerA outerB outerHistory index a b history ++ [.indices [outerIndex,index]]) 15 rfl rfl rfl
  have both := firstCertificate.bind
    (sourceNext := fun original => fold routing (sourceStep model "second" guard) original.2)
    (targetNext := stepView model "second" 21 22)
    (nextLive := fun _ frame => ArtifactBinding.Captures
      (bodyInput model count innerCount guard first last initial outerIndex outerA outerB outerHistory index a b history ++ [.indices [outerIndex,index]]) frame)
    (returnRelation := IterationReturns (LoopRelation model [⟨"outer",outerIndex⟩]) [⟨"outer",outerIndex⟩] "inner" index
      [22,24,26] [.data (.field field),.data (.field field),.transcript "suite"])
    (fun _ _ retained => retained)
    (fun source env returned => by
      apply Classical.choice
      obtain ⟨received,reply,rfl,rfl⟩ := returned
      refine ⟨?_⟩
      have secondCertificate := step_certificate model "second" (by simp) outerIndex index guard
        (afterStep model "first" outerIndex index history received reply)
        ((bodyInput model count innerCount guard first last initial outerIndex outerA outerB outerHistory index a b history ++ [.indices [outerIndex,index]]) ++
          stepExtras model "first" outerIndex index history received reply) 21 rfl rfl rfl
      exact secondCertificate.mapRelations
        (fun source final returned => by
          obtain ⟨received2,reply2,rfl,rfl⟩ := returned
          refine ⟨rfl, [.data (.field field received2),.data (.field field reply2),
            .transcript "suite" (afterStep model "second" outerIndex index
              (afterStep model "first" outerIndex index history received reply) received2 reply2)],
            rfl,rfl,rfl,[.data (.field field received2),.data (.field field reply2)],rfl,rfl⟩)
        (fun _ _ retained => ArtifactBinding.captures_trans
          (ArtifactBinding.captures_append _ _) retained))
  apply both.mapRelations (fun _ _ returned => returned)
  intro process frame retained
  have capturedPrefix : ArtifactBinding.Captures (innerCaptured model count innerCount guard first last initial outerIndex outerA outerB outerHistory)
      (bodyInput model count innerCount guard first last initial outerIndex outerA outerB outerHistory index a b history ++ [.indices [outerIndex,index]]) := by rfl
  exact ArtifactBinding.captures_trans capturedPrefix retained

private theorem mask_state (value : Values (Component model.Value) stateTypes) :
    maskValues 1 [[0,1],[0,1]] value = value := by
  cases value with
  | cons first rest =>
    cases rest with
    | cons last rest => cases rest; rfl

def inner_repeat (count innerCount : Nat) (guard : Bool) (first last : model.Field field)
    (initial : Domain.History model.toCarriers) (outerIndex : Nat)
    (firstState lastState : model.Field field) (history : Domain.History model.toCarriers) :
    Simulation (fun original final => ∃ next, LoopRelation model [⟨"outer",outerIndex⟩] original next ∧
      final = innerCaptured model count innerCount guard first last initial outerIndex firstState lastState history ++ next)
      (fun _ frame => ArtifactBinding.Captures (innerCaptured model count innerCount guard first last initial outerIndex firstState lastState history) frame)
      (fold routing (denoteRepeatOn spec {} 1 (some innerCount) (.cons (some firstState) (.cons (some lastState) .nil))
        (.cons (some guard) (.cons (some 73) .nil)) (callback model) Occurrence.iterations "inner") ⟨[⟨"outer",outerIndex⟩],history⟩)
      (Domain.View.loop 5 [22,24,26] 1 [8,9,10]
        [.data (.field field),.data (.field field),.transcript "suite"]
        (bodyView model) (innerCaptured model count innerCount guard first last initial outerIndex firstState lastState history)) := by
  apply Simulation.framedRepeat routing spec {} 1 rfl
    (.cons (some guard) (.cons (some 73) .nil)) (callback model) "inner" (bodyView model)
    _ [22,24,26] [.data (.field field),.data (.field field)] rfl [⟨"outer",outerIndex⟩]
  · intro value state carried index related
    apply Classical.choice
    obtain ⟨frameEq, related⟩ := related
    obtain ⟨a,b,rfl,rfl⟩ := carried_eq model value state carried related
    cases state with
    | mk outer reached =>
      cases frameEq
      refine ⟨?_⟩
      simpa only [spec, ProtocolContext.mapScopes_root, mask_state, Values.append,
        List.nil_append, List.cons_append, qualifyProtocolSite, bodyInput, LoopRelation,
        routing, context, Context.fiatShamir, profileOutputSorts] using
        callback_certificate model count innerCount guard first last initial outerIndex firstState lastState history index a b reached
  · rfl
  · rfl
  · exact ⟨rfl,[.data (.field field firstState),.data (.field field lastState)],rfl,rfl⟩

def outerView : Domain.View.Block model.toCarriers :=
  Domain.View.sequence (Domain.View.indicesAppend 6 7 [.indices]) <|
  Domain.View.sequence (Domain.View.loop 5 [22,24,26] 1 [8,9,10]
    [.data (.field field),.data (.field field),.transcript "suite"] (bodyView model)) Domain.View.empty

theorem outer_view : Domain.Correspondence.Block (program := program) (context := context)
    outerInstructions (outerView model) := by
  apply Domain.Correspondence.sequence (Domain.Correspondence.indicesAppend _ _ _)
  apply Domain.Correspondence.sequence
    (Domain.Correspondence.loop _ _ _ _ _ _ (body_view model))
  exact Domain.Correspondence.empty

/-- A nested repeat returns the exact outer frame, entire carried row and
reached history. Only its physical output map is transported to the caller. -/
def outer_callback (count innerCount : Nat) (guard : Bool) (first last : model.Field field)
    (initial : Domain.History model.toCarriers) (outerIndex : Nat)
    (a b : model.Field field) (history : Domain.History model.toCarriers) :
    Simulation (IterationReturns (LoopRelation model []) [] "outer" outerIndex
        [12,13,14] [.data (.field field),.data (.field field),.transcript "suite"])
      (fun _ frame => ArtifactBinding.Captures (captured model count innerCount guard first last initial) frame)
      (fold routing (outerCallback model (.cons (some outerIndex) (.cons (some a) (.cons (some b)
        (.cons (some innerCount) (.cons (some guard) (.cons (some 73) .nil)))))))
        ⟨[⟨"outer",outerIndex⟩],history⟩)
      (outerView model (outerInput model count innerCount guard first last initial outerIndex a b history)) := by
  rw [outer_denote]
  unfold outerView
  rw [Domain.View.sequence_return _ _ _ _
    (Domain.View.indicesAppend_eq 6 7 _ [] outerIndex rfl rfl)]
  apply Simulation.checkpoint _ (by rfl)
  apply Simulation.checkpoint _ (by rfl)
  unfold Domain.View.sequence
  apply Simulation.checkpoint _ (by rfl)
  have head := inner_repeat model count innerCount guard first last initial outerIndex a b history
  have tail : ∀ original final, (∃ next, LoopRelation model [⟨"outer",outerIndex⟩] original next ∧
      final = innerCaptured model count innerCount guard first last initial outerIndex a b history ++ next) →
      Simulation (IterationReturns (LoopRelation model []) [] "outer" outerIndex
          [12,13,14] [.data (.field field),.data (.field field),.transcript "suite"])
        (fun _ frame => ArtifactBinding.Captures (captured model count innerCount guard first last initial) frame)
        (.done original) (.call (.checkpoint final) fun _ => Domain.View.empty final) := by
    intro original final returned
    apply Classical.choice
    obtain ⟨next,framed,rfl⟩ := returned
    obtain ⟨frames,related⟩ := framed
    obtain ⟨x,y,values,row⟩ := carried_eq model original.1 original.2 next related
    rcases original with ⟨value,outer,reached⟩
    cases frames
    cases values
    cases row
    refine ⟨?_⟩
    apply Simulation.checkpoint _ (by rfl)
    exact .done ⟨rfl,[.data (.field field x),.data (.field field y),.transcript "suite" reached],
      rfl,rfl,rfl,[.data (.field field x),.data (.field field y)],rfl,rfl⟩
  simpa only [PIR.Process.bind_done, innerCaptured, List.nil_append] using head.bind
    (fun _ _ retained => ArtifactBinding.captures_trans (by rfl) retained) tail

def root_repeat (count innerCount : Nat) (guard : Bool) (first last : model.Field field)
    (history : Domain.History model.toCarriers) :
    Simulation (fun original final => ∃ next, LoopRelation model [] original next ∧
      final = captured model count innerCount guard first last history ++ next)
      (fun _ frame => ArtifactBinding.Captures (captured model count innerCount guard first last history) frame)
      (fold routing (denoteRepeatOn outerSpec {} 1 (some count) (.cons (some first) (.cons (some last) .nil))
        (.cons (some innerCount) (.cons (some guard) (.cons (some 73) .nil)))
        (outerCallback model) Occurrence.iterations "outer") ⟨[],history⟩)
      (Domain.View.loop 3 [12,13,14] 0 [3,4,5]
        [.data (.field field),.data (.field field),.transcript "suite"]
        (outerView model) (captured model count innerCount guard first last history)) := by
  apply Simulation.framedRepeat routing outerSpec {} 1 rfl
    (.cons (some innerCount) (.cons (some guard) (.cons (some 73) .nil))) (outerCallback model)
    "outer" (outerView model) _ [12,13,14] [.data (.field field),.data (.field field)] rfl []
  · intro value state carried index related
    apply Classical.choice
    obtain ⟨frameEq, related⟩ := related
    obtain ⟨a,b,rfl,rfl⟩ := carried_eq model value state carried related
    cases state with
    | mk outer reached =>
      cases frameEq
      refine ⟨?_⟩
      simpa only [outerSpec, ProtocolContext.mapScopes_root, mask_state, Values.append,
        List.nil_append, List.cons_append, qualifyProtocolSite, outerInput, LoopRelation,
        routing, context, Context.fiatShamir, profileOutputSorts] using
        outer_callback model count innerCount guard first last history index a b reached
  · rfl
  · rfl
  · exact ⟨rfl,[.data (.field field first),.data (.field field last)],rfl,rfl⟩

def rootView : Domain.View.Block model.toCarriers :=
  Domain.View.sequence (Domain.View.indicesEmpty [.indices]) <|
  Domain.View.sequence (Domain.View.loop 3 [12,13,14] 0 [3,4,5]
    [.data (.field field),.data (.field field),.transcript "suite"] (outerView model)) Domain.View.empty

theorem root_view : Domain.Correspondence.Block (program := program) (context := context)
    artifact.instructions (rootView model) := by
  apply Domain.Correspondence.sequence (Domain.Correspondence.indicesEmpty _)
  apply Domain.Correspondence.sequence
    (Domain.Correspondence.loop _ _ _ _ _ _ (outer_view model))
  exact Domain.Correspondence.empty

/-- Complete root outputs, reached transcript, closed frames and immutable
source inputs, for every count, guard, history and receive/query reply. -/
def composed (count innerCount : Nat) (guard : Bool) (first last : model.Field field)
    (history : Domain.History model.toCarriers) :
    Simulation (CompleteReturns runSignature context 1 artifact)
      (fun _ frame => ArtifactBinding.Captures (inputFrame model count innerCount guard first last history) frame)
      (fold routing (Occurrence.participant model program 1 (sourceInputs model count innerCount guard first last)) ⟨[],history⟩)
      (Domain.participant model program context artifact (inputFrame model count innerCount guard first last history)) := by
  rw [source_exact, Domain.Correspondence.participant artifact (root_view model)]
  simp only [fold_bind, fold_done]
  have inputSorts : Domain.sortsMatch artifact.inputs (inputFrame model count innerCount guard first last history) = true := rfl
  simp only [Domain.View.participant, inputSorts, ↓reduceIte]
  unfold rootView
  apply Simulation.checkpoint _ (by simp [ArtifactBinding.Captures])
  rw [Domain.View.sequence_return _ _ _ _ (show Domain.View.indicesEmpty [.indices]
    (inputFrame model count innerCount guard first last history) = .done (captured model count innerCount guard first last history) from rfl)]
  apply Simulation.checkpoint _ (by simp [ArtifactBinding.Captures])
  apply Simulation.checkpoint _ (ArtifactBinding.captures_append _ _)
  simp only [Domain.View.sequence, PIR.Process.bind_assoc]
  apply Simulation.checkpoint _ (ArtifactBinding.captures_append _ _)
  simp only [PIR.Process.bind_assoc]
  apply (root_repeat model count innerCount guard first last history).bind
  · intro source frame retained
    exact ArtifactBinding.captures_trans (ArtifactBinding.captures_append _ _) retained
  · intro original final returned
    apply Classical.choice
    obtain ⟨next,related,rfl⟩ := returned
    obtain ⟨frames,related⟩ := related
    obtain ⟨a,b,values,carried⟩ := carried_eq model original.1 original.2 next related
    rcases original with ⟨value,outer,reached⟩
    cases frames
    cases values
    cases carried
    refine ⟨?_⟩
    apply Simulation.checkpoint _ (by simp [ArtifactBinding.Captures, inputFrame, captured])
    change Simulation _ _ (.done _) (.done _)
    apply Simulation.done
    apply CompleteReturns.of_layout
      (locations := [.data 2,.data 7,.data 8]) (dataReferences := [2,7,8])
      (historyReference := some 9) (dataSorts := [.data .boolean,.data (.field field),.data (.field field)])
      rfl rfl rfl rfl
    · exact ⟨⟨guard,rfl,rfl⟩,⟨a,rfl,rfl⟩,⟨b,rfl,rfl⟩,trivial⟩
    · rfl
    · rfl
    · rfl

/-- The same certificate begins at the occurrence-aware normalized actual root. -/
def normalized_composed (count innerCount : Nat) (guard : Bool) (first last : model.Field field)
    (history : Domain.History model.toCarriers) :
    Simulation (CompleteReturns runSignature context 1 artifact)
      (fun _ frame => ArtifactBinding.Captures (inputFrame model count innerCount guard first last history) frame)
      (fold routing (normalized model count innerCount guard first last) ⟨[],history⟩)
      (Domain.participant model program context artifact (inputFrame model count innerCount guard first last history)) := by
  rw [← source_normalized]
  exact composed model count innerCount guard first last history

/-- All root checkpoints also retain the complete decoded source input tuple,
including its ABI-pinned capability, under the same source-owned input schema. -/
def normalized_inputs (count innerCount : Nat) (guard : Bool) (first last : model.Field field)
    (history : Domain.History model.toCarriers) :
    Simulation (CompleteReturns runSignature context 1 artifact)
      (InputLive inputABI (sourceInputs model count innerCount guard first last)
        (inputFrame model count innerCount guard first last history))
      (fold routing (normalized model count innerCount guard first last) ⟨[],history⟩)
      (Domain.participant model program context artifact (inputFrame model count innerCount guard first last history)) := by
  apply (normalized_composed model count innerCount guard first last history).mapRelations
    (fun _ _ returned => returned)
  intro process frame retained
  apply inputLive_of_captures inputABI _ _ _ process rfl _ _ retained
  · intro reference present
    simp only [inputABI, List.mem_cons, List.not_mem_nil, or_false, Location.data.injEq,
      reduceCtorEq, false_or, or_false] at present
    rcases present with rfl | rfl | rfl | rfl | rfl <;> simp [inputFrame]
  · exact (readComponents_iff _ _ _ _).mp rfl

private def step_coverage (site : String) (present : site ∈ ["first","second"])
    (outerIndex index : Nat) (guard : Bool) :
    RouteCoverage routing [⟨"outer",outerIndex⟩,⟨"inner",index⟩]
      [⟨"outer",outerIndex⟩,⟨"inner",index⟩] (sourceStep model site guard) := by
  cases guard
  · exact .halt _ _ _
  · apply RouteCoverage.action
    · exact ⟨rfl,origin site "m" outerIndex index,message_route site present "m" (by simp) outerIndex index⟩
    · intro first
      apply RouteCoverage.action
      · exact Or.inl ⟨rfl,origin site "q" outerIndex index,draw_route site present outerIndex index,rfl⟩
      · intro last
        apply RouteCoverage.action
        · exact ⟨rfl,origin site "d" outerIndex index,message_route site present "d" (by simp) outerIndex index⟩
        · exact fun _ => .done _ _

private def repeat_coverage (spec : RepeatSpec) (count : Option Nat)
    (initial : Values (Component model.Value) spec.state)
    (captures : Values (Component model.Value) spec.captures)
    (body : RegionFunction (Component model.Value) (I model)
      (.index :: (spec.state ++ spec.captures), spec.state)) (site : String) (frames : Frames)
    (callback : ∀ (index : Nat) (value : Values (Component model.Value) spec.state), RouteCoverage routing (frames ++ [⟨site,index⟩])
      (frames ++ [⟨site,index⟩]) (body (.cons (some index) (value.append captures)))) :
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

private def inner_coverage (outerIndex : Nat) (count : Option Nat) (guard : Bool)
    (value : Values (Component model.Value) stateTypes) :
    RouteCoverage routing [⟨"outer",outerIndex⟩] [⟨"outer",outerIndex⟩]
      (denoteRepeatOn spec {} 1 count value (.cons (some guard) (.cons (some 73) .nil))
        (callback model) Occurrence.iterations "inner") := by
  apply repeat_coverage
  intro index value
  cases value with
  | cons a rest =>
    cases rest with
    | cons b rest =>
      cases rest
      change RouteCoverage _ _ _ (callbackBody.denote
        (meaningAtOn model Occurrence.actions Occurrence.iterations (helpers model) (protocols model) {} 1)
        (Values.cons (some index) (.cons a (.cons b (.cons (some guard) (.cons (some 73) .nil))))).get)
      rw [callback_denote]
      exact (step_coverage model "first" (by simp) outerIndex index guard).bind
        (fun _ => step_coverage model "second" (by simp) outerIndex index guard)

/-- Coverage is derived from the actual nested source, for every optional
carried component, index and independent typed reply, including stopped paths. -/
def route_coverage (count innerCount : Nat) (guard : Bool) (first last : model.Field field) :
    RouteCoverage routing [] []
      (Occurrence.participant model program 1 (sourceInputs model count innerCount guard first last)) := by
  rw [source_exact]
  apply RouteCoverage.bind _ (fun _ => .done _ _)
  apply repeat_coverage
  intro outerIndex value
  cases value with
  | cons a rest =>
    cases rest with
    | cons b rest =>
      cases rest
      change RouteCoverage _ _ _ (outerCallback model (.cons (some outerIndex)
        (.cons a (.cons b (.cons (some innerCount) (.cons (some guard) (.cons (some 73) .nil)))))))
      rw [outer_denote]
      exact inner_coverage model outerIndex (some innerCount) guard _

/-- A public round appends the message, challenge and delivered message in order. -/
theorem history_advances (site : String) (outerIndex index : Nat)
    (history : Domain.History model.toCarriers) (first last : model.Field field) :
    (afterStep model site outerIndex index history first last).length = history.length + 3 := by
  simp [afterStep,afterQuery,afterMessage,List.length_append]

theorem two_calls_advance (outerIndex index : Nat) (history : Domain.History model.toCarriers)
    (first reply second reply2 : model.Field field) :
    (afterStep model "second" outerIndex index (afterStep model "first" outerIndex index history first reply) second reply2).length =
      history.length + 6 := by
  simp [history_advances, Nat.add_assoc]

/-- Every root checkpoint recovers the entire physical input frame. -/
theorem checkpoint_readback (count innerCount : Nat) (guard : Bool) (first last : model.Field field)
    (history : Domain.History model.toCarriers) (frame : Domain.Environment model.toCarriers)
    (retained : ArtifactBinding.Captures (inputFrame model count innerCount guard first last history) frame) :
    Domain.read frame [0,1,2,3,4,5] = some (inputFrame model count innerCount guard first last history) := by
  have split : frame = inputFrame model count innerCount guard first last history ++ frame.drop 6 := by
    calc
      frame = frame.take 6 ++ frame.drop 6 := (List.take_append_drop 6 frame).symm
      _ = _ := by rw [show frame.take 6 = inputFrame model count innerCount guard first last history from retained]
  rw [split]
  simp [Domain.read,inputFrame]

def omittedRouting : Routing := {routing with messages :=
  [template "first" "m",template "first" "d",template "second" "d"]}

theorem omitted_route (outerIndex index : Nat) :
    omittedRouting.message [⟨"outer",outerIndex⟩,⟨"inner",index⟩] (qualified "second" "m") 0 1 = none := by kernel_rfl

theorem omitted_route_no_coverage (outerIndex index : Nat) :
    IsEmpty (RouteCoverage omittedRouting [⟨"outer",outerIndex⟩,⟨"inner",index⟩] [⟨"outer",outerIndex⟩,⟨"inner",index⟩]
      (sourceStep model "second" true)) := by
  constructor
  intro covered
  change RouteCoverage _ _ _ (.call (.action (.receive (.field field) (qualified "second" "m") 0)) _) at covered
  obtain ⟨_,origin,found⟩ := covered.action_required
  change omittedRouting.message [⟨"outer",outerIndex⟩,⟨"inner",index⟩] (qualified "second" "m") 0 1 = some origin at found
  rw [omitted_route] at found
  cases found

/-- Full returns detect a changed field even when acceptance is identical. -/
theorem changed_field_rejected (a b : model.Field field) (different : a ≠ b)
    (history : Domain.History model.toCarriers) (environment : Domain.Environment model.toCarriers) :
    ¬ CompleteReturns runSignature context 1 artifact
      (.cons (some true) (.cons (some a) (.cons (some b) .nil)),⟨[],history⟩)
      ⟨[.data (.boolean true),.data (.field field a),.data (.field field a),.transcript "suite" history],environment⟩ := by
  intro complete
  obtain ⟨data,encoded,returned⟩ := complete.values
  have exactEncoding : roleOutputValues (carriers := model.toCarriers) 1 runSignature.outputScopes
      (Values.cons (some true) (.cons (some a) (.cons (some b) .nil)) : Values (Component model.Value) rootOutputs) =
      some [.data (.boolean true),.data (.field field a),.data (.field field b)] := rfl
  rw [exactEncoding] at encoded
  cases encoded
  have same : a = b := by simpa [Domain.inputFrame,context,Context.fiatShamir] using returned
  exact different same

/-- The existing consumer theorem retains stopped handler state, all effects
and checkpoints; no successful-handler premise is required. -/
theorem composed_runM (count innerCount : Nat) (guard : Bool) (first last : model.Field field)
    (history : Domain.History model.toCarriers)
    {m : Type → Type} [Monad m] [LawfulMonad m] {R E : Type}
    (handler : PIR.MonadHandler m (Domain.effects model.toCarriers) R E) (state : R) :
    (Domain.participant model program context artifact (inputFrame model count innerCount guard first last history)).runM handler state =
      (do let execution ← (normalized_composed model count innerCount guard first last history).paired.runM handler state
          pure (mapExecution Prod.snd execution)) :=
  (normalized_composed model count innerCount guard first last history).runM handler state

theorem zero_iterations (innerCount : Nat) (guard : Bool) (first last : model.Field field) :
    Occurrence.participant model program 1 (sourceInputs model 0 innerCount guard first last) =
      .done (.cons (some guard) (.cons (some first) (.cons (some last) .nil))) := by
  rw [source_exact]
  rfl

theorem excessive_count (count innerCount : Nat) (excessive : ¬ count ≤ 3)
    (guard : Bool) (first last : model.Field field) :
    Occurrence.participant model program 1 (sourceInputs model count innerCount guard first last) = .halt .refused := by
  rw [source_exact]
  change ((if count ≤ 3 then _ else PIR.Process.halt .refused).bind _) = _
  rw [ite_eq_right excessive]
  rfl

theorem failed_guard (site : String) : sourceStep model site false = .halt .reject := rfl

theorem zero_inner_callback (outerIndex : Option Nat) (guard : Bool)
    (a b : Option (model.Field field)) :
    outerCallback model (.cons outerIndex (.cons a (.cons b
      (.cons (some 0) (.cons (some guard) (.cons (some 73) .nil)))))) =
      .done (.cons a (.cons b .nil)) := by
  rw [outer_denote]
  rfl

/-- The inner bound is checked when reached, independently of the outer bound.
An empty outer repeat therefore need not inspect an excessive inner count. -/
theorem excessive_inner_callback (outerIndex : Option Nat) (innerCount : Nat)
    (excessive : ¬ innerCount ≤ 5) (guard : Bool) (a b : Option (model.Field field)) :
    outerCallback model (.cons outerIndex (.cons a (.cons b
      (.cons (some innerCount) (.cons (some guard) (.cons (some 73) .nil)))))) = .halt .refused := by
  rw [outer_denote]
  change (if innerCount ≤ 5 then _ else PIR.Process.halt .refused) = _
  exact ite_eq_right excessive

theorem swapped_frame_order (outerIndex index : Nat) :
    routing.message [⟨"inner",index⟩,⟨"outer",outerIndex⟩] (qualified "first" "m") 0 1 = none := by
  kernel_rfl

theorem missing_coordinate (outerIndex : Nat) :
    Domain.templateOrigin context (template "first" "m") [outerIndex] = none := by kernel_rfl

-- Same frame names with swapped numeric coordinates resolve to a different
-- origin as well; a template's arity check alone cannot enforce their order.
example : Domain.templateOrigin context (template "first" "m") [2,1] ≠
    some (origin "first" "m" 1 2) := by decide +kernel

theorem stale_history_rejected (outerIndex index : Nat) (a reply b reply2 : model.Field field)
    (history : Domain.History model.toCarriers) (environment : Domain.Environment model.toCarriers) :
    ¬ CompleteReturns runSignature context 1 artifact
      (.cons (some true) (.cons (some b) (.cons (some reply2) .nil)),
        ⟨[],afterStep model "second" outerIndex index
          (afterStep model "first" outerIndex index history a reply) b reply2⟩)
      ⟨[.data (.boolean true),.data (.field field b),.data (.field field reply2),
        .transcript "suite" history],environment⟩ := by
  intro complete
  obtain ⟨data,encoded,returned⟩ := complete.values
  change some [.data (.boolean true),.data (.field field b),.data (.field field reply2)] = some data at encoded
  cases encoded
  have same : history = afterStep model "second" outerIndex index
      (afterStep model "first" outerIndex index history a reply) b reply2 := by
    simpa [Domain.inputFrame,context,Context.fiatShamir] using returned
  have lengths := congrArg List.length same
  rw [two_calls_advance] at lengths
  omega

/-- Keep the real authored-pair association: a fixed request pins whole
artifacts, even if a mutated validator retains every metadata label. This
fixture proves validator correspondence, not admission of a producer pair. -/
theorem authored_pair_identity (selected : AuthoredPair.Selection snapshot)
    (producer mutated : Zkc.Construction.Participant)
    (pinned : selected.artifacts.validator = artifact) (different : mutated ≠ artifact) :
    AuthoredPair.check imported selected ⟨producer,mutated⟩ = .error "authored-pair-artifacts" := by
  have mismatch : AuthoredPair.associated selected ⟨producer,mutated⟩ = false := by
    apply Bool.eq_false_iff.mpr
    intro same
    have exactPair := (AuthoredPair.associated_iff selected ⟨producer,mutated⟩).mp same
    exact different ((congrArg AuthoredPair.Artifacts.validator exactPair).trans pinned)
  simp only [AuthoredPair.check, mismatch, Bool.false_eq_true, ↓reduceIte]

/-- No extra non-administrative event, stop, or reply-dependent suffix is hidden
by the checkpoint relation. -/
theorem no_invented_events (count innerCount : Nat) (guard : Bool) (first last : model.Field field)
    (history : Domain.History model.toCarriers) :
    ((Domain.participant model program context artifact (inputFrame model count innerCount guard first last history)).bind
      (fun _ => .done ())).interpret forgetCheckpoints =
    ((fold routing (normalized model count innerCount guard first last) ⟨[],history⟩).bind
      (fun _ => .done ())).interpret forgetCheckpoints :=
  (normalized_composed model count innerCount guard first last history).shape

end Tests.ConnectionRepeatedTranscript
