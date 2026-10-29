module

public import Zkc.Construction.ConnectionRouteCoverageLoops
public import Zkc.Construction.ConnectionApplicationCoverageFrame

@[expose] public section

/-! Reached-source coverage from the same finite typed alignment used for
simulation. Frame-relatedness establishes presence, including splitPresent.
The successful-leaf invariant retains the complete source-owned nominal row. -/
set_option autoImplicit false
namespace Zkc.Construction.ConnectionCertificate
open Zkc.Source Zkc.Source.Structured NormalForm ConnectionFrame ConnectionComputation
open ConnectionRouteCoverage

set_option hygiene false in
macro "retain_connection_frame" : tactic => `(tactic|
  first
  | assumption
  | exact ArtifactBinding.captures_trans retained (ArtifactBinding.captures_append _ _)
  | exact ArtifactBinding.captures_trans retained preparedKept
  | exact ArtifactBinding.captures_trans retained
      (ArtifactBinding.captures_trans preparedKept (ArtifactBinding.captures_append _ _))
  | exact ArtifactBinding.captures_trans retained
      (ArtifactBinding.captures_trans (ArtifactBinding.captures_append _ _) preparedKept)
  | exact ArtifactBinding.captures_trans retained
      (ArtifactBinding.captures_trans (ArtifactBinding.captures_append _ _)
        (ArtifactBinding.captures_trans preparedKept (ArtifactBinding.captures_append _ _))))

@[no_expose] noncomputable def Alignment.coveredRetained
    {routing : Original.Routing} {context : ProtocolContext} {definitions : List CheckedDefinition}
    {callees : List CalleeKey} {selection : ConnectionLibrary.Selection definitions callees} {out : List Ty} {role : Nat} {scopes : List (List Nat)}
    {outputs : List Original.Location} {history : Option Nat}
    {scope : Scope} {frames : ScopedFrames scope} {layout : Layout scope}
    {form : Form [] callees scope out} {target : Block}
    (derivation : Derivation routing context definitions callees (selection := selection) out role scopes outputs history frames layout form target)
    (model : DomainModel) (tables : Tables model (Occurrence.signature model.toCarriers))
    (bindings : ConnectionHelpers.TablesMatch model definitions tables)
    (protocols : ProtocolTable model.Value (Occurrence.signature model.toCarriers))
    (processes : CalleeProcesses model callees (Occurrence.signature model.toCarriers))
    (calleesHold : ∀ {types : List Ty} (inputs : Values (Component model.Value) types),
      CalleesHold protocols processes inputs)
    (selectionMeaning : selection.Meaning model tables protocols processes)
    (captured : Domain.Environment model.toCarriers)
    (binders : Binders model scope) (reachedHistory : Domain.History model.toCarriers)
    (environment : Domain.Environment model.toCarriers)
    (related : Holds model binders reachedHistory layout environment)
    (retained : ArtifactBinding.Captures captured environment) :
    Covered routing (fun values => ∃ frame, Original.ValuesHolds frame outputs
      (maskValues role scopes values) ∧ ArtifactBinding.Captures captured frame)
      (frames.eval model binders) (frames.eval model binders)
      (form.denoteOn model Occurrence.actions tables (LawResults.empty model) context
        (runsAtOn model Occurrence.actions Occurrence.iterations tables protocols context role) processes binders) := by
  induction derivation generalizing model tables protocols captured environment reachedHistory with
  | done readback historyRead => exact .done _ _ ⟨environment, readback.masked related, retained⟩
  | halt reason => exact .halt _ _ reason
  | split subject absentBranch presentBranch absentIH presentIH =>
    cases evaluated : subject.comp.eval (LawResults.empty model) binders with
    | none =>
      simpa only [Form.denoteOn, Form.denoteWithOn, evaluated] using
        absentIH model tables bindings protocols processes calleesHold selectionMeaning captured binders reachedHistory environment (related.absentAt subject evaluated) (by retain_connection_frame)
    | some value =>
      simpa only [Form.denoteOn, Form.denoteWithOn, evaluated, frames_cons] using
        presentIH model tables bindings protocols processes calleesHold selectionMeaning captured (.cons value binders) reachedHistory environment (related.presentAt subject value evaluated) (by retain_connection_frame)
  | splitAbsent presentMatched tail ih =>
    simpa only [Form.denoteOn, Form.denoteWithOn, Comp.eval] using
      ih model tables bindings protocols processes calleesHold selectionMeaning captured binders reachedHistory environment related (by retain_connection_frame)
  | @splitValue context definitions callees selection out role scopes outputs history scope frames layout ty value absent present target absentMatched tail ih =>
    have aligned := ih model tables bindings protocols processes calleesHold selectionMeaning captured binders reachedHistory environment related (by retain_connection_frame)
    rw [ConnectionSubstitution.valueHead_denote] at aligned
    simpa only [Form.denoteOn, Form.denoteWithOn, Comp.eval] using aligned
  | splitPresent subject reference checked absentMatch tail ih =>
    cases evaluated : subject.comp.eval (LawResults.empty model) binders with
    | none => exact False.elim (related.not_absent checked evaluated)
    | some value =>
      simpa only [Form.denoteOn, Form.denoteWithOn, evaluated, frames_cons] using
        ih model tables bindings protocols processes calleesHold selectionMeaning captured (.cons value binders) reachedHistory environment (related.presentAt subject value evaluated) (by retain_connection_frame)
  | @compute context definitions callees selection out role scopes outputs history scope frames layout operation terms next rest references inputsData outputsData readback tail ih =>
    rw [ConnectionCalculations.form_compute_closed model Occurrence.actions (LawResults.empty model)
      context _ processes tables operation terms next binders]
    apply Covered.closedBind
    intro values
    simpa only [frames_cons, Form.denoteOn, PIR.Process.bind] using
      ih model tables bindings protocols processes calleesHold selectionMeaning captured (.cons values binders) reachedHistory _ (results_frame model outputsData values binders related) (by retain_connection_frame)
  | @strictHelper context definitions callees selection out role scopes outputs history scope frames layout program helper binding arguments next rest references inputsData outputsData readback tail ih =>
    change Covered _ _ _ _ ((invoke tables.closed helper (Terms.eval (LawResults.empty model) arguments binders)).bind _)
    have invoked : invoke tables.closed helper (Terms.eval (LawResults.empty model) arguments binders) =
        (invoke (Domain.helperTable model program) helper
          (Terms.eval (LawResults.empty model) arguments binders)).interpret
            (closedLift (I := Occurrence.signature model.toCarriers)) := by
      rw [binding.tables bindings, Evaluation.closed_invoke_componentTablesOn]
      rfl
    rw [invoked]
    apply Covered.closedBind
    intro values
    simpa only [frames_cons, Form.denoteOn, PIR.Process.bind] using
      ih model tables bindings protocols processes calleesHold selectionMeaning captured (.cons values binders) reachedHistory _ (results_frame model outputsData values binders related) (by retain_connection_frame)
  | @ownedHelper context definitions callees selection out role scopes outputs history scope frames layout owner program helper binding arguments next rest references inputsData outputsData readback tail ih =>
    apply Classical.choice
    obtain ⟨values, present, read⟩ := read_components readback binders related
    have sourceEq := ConnectionCalculations.form_owned_present_closed model Occurrence.actions
      (LawResults.empty model) context
      (runsAtOn model Occurrence.actions Occurrence.iterations tables protocols context role)
      processes program.payload.definitions owner helper arguments values next binders present
    rw [← binding.tables bindings] at sourceEq
    rw [sourceEq]
    refine ⟨Covered.closedBind _ _ ?_⟩
    intro values
    simpa only [frames_cons, Form.denoteOn, PIR.Process.bind] using
      ih model tables bindings protocols processes calleesHold selectionMeaning captured (.cons values.present binders) reachedHistory _ (tuple_frame model outputsData values binders related) (by retain_connection_frame)
  | @mathHelper context definitions callees selection out role scopes outputs history scope frames layout program helper math binding arguments next rest references inputsData outputsData readback tail ih =>
    apply Classical.choice
    obtain ⟨values, present, read⟩ := read_components readback binders related
    have sourceEq := ConnectionCalculations.form_math_present_closed model Occurrence.actions
      (LawResults.empty model) context
      (runsAtOn model Occurrence.actions Occurrence.iterations tables protocols context role)
      processes program.payload.definitions helper arguments values next binders present
    rw [← binding.tables bindings] at sourceEq
    rw [sourceEq]
    refine ⟨Covered.closedBind _ _ ?_⟩
    intro values
    simpa only [frames_cons, Form.denoteOn, PIR.Process.bind] using
      ih model tables bindings protocols processes calleesHold selectionMeaning captured (.cons values.present binders) reachedHistory _ (tuple_frame model outputsData values binders related) (by retain_connection_frame)
  | @projectionHelper context definitions callees selection out role scopes outputs history scope frames layout definition projection arguments next target nextMatched tail ih =>
    have tableEquality := bindings ⟨projection.before.length, by
      have length := congrArg List.length projection.declarations
      simp only [List.length_append, List.length_cons] at length
      omega⟩
    have invoked : invoke tables.components definition.helper (Comps.eval (LawResults.empty model) arguments binders) =
        .done (Comps.eval (LawResults.empty model) (lookup arguments projection.positions) binders) := by
      rw [tableEquality]
      exact (projection.invoke model (I := Occurrence.signature model.toCarriers)
        (Comps.eval (LawResults.empty model) arguments binders)).trans
          (congrArg PIR.Process.done
            ((congrArg (fun values => Comps.eval (LawResults.empty model) values binders)
              (lookup_eq_eval arguments projection.positions)).trans
                (comps_eval_operands (LawResults.empty model) arguments binders projection.positions)).symm)
    change Covered _ _ _ _ ((invoke tables.components definition.helper
      (Comps.eval (LawResults.empty model) arguments binders)).bind _)
    rw [invoked, PIR.Process.bind]
    change Covered _ _ _ _ (next.denoteOn model Occurrence.actions tables (LawResults.empty model) context
      (runsAtOn model Occurrence.actions Occurrence.iterations tables protocols context role) processes
      (.cons (Comps.eval (LawResults.empty model) (lookup arguments projection.positions) binders) binders))
    rw [← ConnectionSubstitution.tupleHead_denote (lookup arguments projection.positions)
      Occurrence.actions tables context _ processes next binders]
    exact ih model tables bindings protocols processes calleesHold selectionMeaning captured binders reachedHistory environment related (by retain_connection_frame)
  | @inlineCalculation context definitions callees selection out role scopes outputs history scope frames layout
      definition calculation arguments next target nextMatched tail ih =>
    have tableEquality := bindings ⟨calculation.before.length, by
      have length := congrArg List.length calculation.declarations
      simp only [List.length_append, List.length_cons] at length
      omega⟩
    have invoked : invoke tables.components definition.helper
        (Comps.eval (LawResults.empty model) (components arguments) binders) =
        .done (Comps.eval (LawResults.empty model) (calculation.result arguments) binders) := by
      rw [tableEquality]
      exact calculation.invoke model arguments binders
    change Covered _ _ _ _ ((invoke tables.components definition.helper
      (Comps.eval (LawResults.empty model) (components arguments) binders)).bind _)
    rw [invoked, PIR.Process.bind]
    change Covered _ _ _ _ (next.denoteOn model Occurrence.actions tables (LawResults.empty model) context
      (runsAtOn model Occurrence.actions Occurrence.iterations tables protocols context role) processes
      (.cons (Comps.eval (LawResults.empty model) (calculation.result arguments) binders) binders))
    rw [← ConnectionSubstitution.tupleHead_denote (calculation.result arguments)
      Occurrence.actions tables context _ processes next binders]
    exact ih model tables bindings protocols processes calleesHold selectionMeaning captured binders
      reachedHistory environment related (by retain_connection_frame)
  | @inlineMissingCalculation context definitions callees selection out role scopes outputs history scope frames layout
      definition calculation arguments missing next target nextMatched tail ih =>
    have tableEquality := bindings ⟨calculation.before.length, by
      have length := congrArg List.length calculation.declarations
      simp only [List.length_append, List.length_cons] at length
      omega⟩
    have invoked : invoke tables.components definition.helper
        (Comps.eval (LawResults.empty model) arguments binders) =
        .done (Comps.eval (LawResults.empty model) (calculation.missingResult arguments) binders) := by
      rw [tableEquality]
      exact calculation.invokeMissing model arguments missing binders
    change Covered _ _ _ _ ((invoke tables.components definition.helper
      (Comps.eval (LawResults.empty model) arguments binders)).bind _)
    rw [invoked, PIR.Process.bind]
    change Covered _ _ _ _ (next.denoteOn model Occurrence.actions tables (LawResults.empty model) context
      (runsAtOn model Occurrence.actions Occurrence.iterations tables protocols context role) processes
      (.cons (Comps.eval (LawResults.empty model) (calculation.missingResult arguments) binders) binders))
    rw [← ConnectionSubstitution.tupleHead_denote (calculation.missingResult arguments)
      Occurrence.actions tables context _ processes next binders]
    exact ih model tables bindings protocols processes calleesHold selectionMeaning captured binders
      reachedHistory environment related (by retain_connection_frame)
  | calculation operation total terms references inputsData outputsData readback tail ih =>
    exact ih model tables bindings protocols processes calleesHold selectionMeaning captured binders reachedHistory _ (calculation_frame model operation total terms outputsData binders related) (by retain_connection_frame)
  | @receive context definitions callees selection out role scopes outputs history scope frames layout ty site peer next rest plain template route data tail ih =>
    apply Covered.action
    · exact ConnectionActionCoverage.receivePlain ty (context.roles peer) plain data (frames.sites_eval model binders) route
    · intro value
      apply Classical.choice
      obtain ⟨physical, encoded⟩ := Domain.Value.encode_exists (carriers := model.toCarriers)
        (by simpa [Domain.dataType] using data) value
      refine ⟨?_⟩
      simpa only [frames_cons, Form.denoteOn, PIR.Process.bind] using
        ih model tables bindings protocols processes calleesHold selectionMeaning captured (.cons value binders) reachedHistory _ (related.bindData value encoded) (by retain_connection_frame)
  | @send context definitions callees selection out role scopes outputs history scope frames layout ty site peer value next rest reference readback plain template route tail ih =>
    apply Covered.action
    · obtain ⟨actual, physical, present, encoded, read⟩ := readback.component related
      exact ConnectionActionCoverage.send ty (context.roles peer) _ (data_of_encode encoded)
        (frames.sites_eval model binders) route
    · intro reply
      exact ih model tables bindings protocols processes calleesHold selectionMeaning captured binders reachedHistory environment related (by retain_connection_frame)
  | @observedSend context definitions callees selection out role scopes outputs history scope frames layout ty site peer value next rest replacement profile prepared preparation preparationProof reference stateRef pathRef readback preparedReadback stateRead pathRead template route tail ih =>
    apply Covered.action
    · obtain ⟨actual, physical, present, encoded, read⟩ := readback.component related
      exact ConnectionActionCoverage.send ty (context.roles peer) _ (data_of_encode encoded)
        (frames.sites_eval model binders) route
    · intro reply
      apply Classical.choice
      obtain ⟨preparedEnvironment, preparedRelated, preparedKept⟩ := CoordinatePrefix.realizeRetained preparationProof related
      exact ⟨ih model tables bindings protocols processes calleesHold selectionMeaning captured binders reachedHistory _ (observed_frame preparedRelated routing.context.suite) (by retain_connection_frame)⟩
  | @observedReceive context definitions callees selection out role scopes outputs history scope frames layout ty site peer next rest replacement profile mode data prepared preparation preparationProof stateRef pathRef valueRead stateRead pathRead template route tail ih =>
    apply Covered.action
    · apply ConnectionActionCoverage.receiveValidator ty (context.roles peer) mode data (frames.sites_eval model binders)
      simpa only [Original.Routing.self, mode] using route
    · intro value
      apply Classical.choice
      obtain ⟨physical, encoded⟩ := Domain.Value.encode_exists (carriers := model.toCarriers)
        (by simpa [Domain.dataType] using data) value
      obtain ⟨preparedEnvironment, preparedRelated, preparedKept⟩ := CoordinatePrefix.realizeRetained preparationProof (related.bindData value encoded)
      refine ⟨?_⟩
      simpa only [frames_cons, Form.denoteOn, PIR.Process.bind] using
        ih model tables bindings protocols processes calleesHold selectionMeaning captured (.cons value binders) reachedHistory _ (observed_frame preparedRelated routing.context.suite) (by retain_connection_frame)
  | @delivery context definitions callees selection out role scopes outputs history scope frames layout site field peer next rest replacement profile mode draw message binding contract request stateRef pathRef stateRead pathRead prepared preparation preparationProof observeStateRef observePathRef valueRead observeStateRead observePathRead tail ih =>
    apply Covered.action
    · exact ConnectionActionCoverage.delivery (context.roles peer) draw message replacement profile mode binding (frames.sites_eval model binders)
    · intro value
      apply Classical.choice
      obtain ⟨preparedEnvironment, preparedRelated, preparedKept⟩ := CoordinatePrefix.realizeRetained preparationProof
        (query_frame related field routing.context.suite value)
      refine ⟨?_⟩
      simpa only [frames_cons, Form.denoteOn, PIR.Process.bind] using
        ih model tables bindings protocols processes calleesHold selectionMeaning captured (.cons value binders) reachedHistory _ (observed_frame preparedRelated routing.context.suite) (by retain_connection_frame)
  | indicesEmpty tail ih => exact ih model tables bindings protocols processes calleesHold selectionMeaning captured binders reachedHistory _ related.indicesEmpty (by retain_connection_frame)
  | indicesAppend terms term coordinateRef indexRef coordinates index tail ih =>
    exact ih model tables bindings protocols processes calleesHold selectionMeaning captured binders reachedHistory _ (related.indicesAppend coordinates index).2 (by retain_connection_frame)
  | @publicQuery context definitions callees selection out role scopes outputs history scope frames layout site field handle selected next rest mode publicService contract request template route stateRef pathRef stateRead pathRead tail ih =>
    apply Covered.action
    · exact ConnectionActionCoverage.publicQuery handle selected mode publicService (frames.sites_eval model binders) route
    · intro value
      have checked := ih model tables bindings protocols processes calleesHold selectionMeaning captured (.cons value binders) reachedHistory _ (query_frame related field routing.context.suite value) (by retain_connection_frame)
      rw [frames_cons (slot := .value (.field field)) frames binders value] at checked
      change Covered _ _ _ _ (next.denoteOn model Occurrence.actions tables (LawResults.empty model) context
        (runsAtOn model Occurrence.actions Occurrence.iterations tables protocols context role) processes (.cons value binders))
      exact checked
  | @localQuery context definitions callees selection out role scopes outputs history scope frames layout site field handle next rest port template mode binding contract coordinates readback tail ih =>
    apply Covered.action
    · exact ConnectionActionCoverage.localQuery handle port binding (frames.sites_eval model binders)
    · intro value
      have checked := ih model tables bindings protocols processes calleesHold selectionMeaning captured (.cons value binders) reachedHistory _ (related.bindData (ty := .field field) value rfl) (by retain_connection_frame)
      rw [frames_cons (slot := .value (.field field)) frames binders value] at checked
      change Covered _ _ _ _ (next.denoteOn model Occurrence.actions tables (LawResults.empty model) context
        (runsAtOn model Occurrence.actions Occurrence.iterations tables protocols context role) processes (.cons value binders))
      exact checked
  | @«repeat» context definitions callees selection out role scopes outputs history scope frames layout spec site callback count initial captures next body rest roster distinct active visible mappedVisible countReference countRead stateReferences initialReferences yieldData yielded initialHistory bodyHistory initialRead historyRead initialProfile bodyProfile yieldLocations bodyForm normalized bodyCertificate tail bodyIH tailIH =>
    apply Classical.choice
    obtain ⟨initialValues, initialPresent, initialReading⟩ := read_components initialRead binders related
    let complete : Values (Component model.Value) spec.state → Prop :=
      fun value => ∃ actual : Values model.Value spec.state, value = actual.present
    let sourceBody := (runsAtOn model Occurrence.actions Occurrence.iterations tables protocols context role).callback spec callback
    have bodyLaw : ∀ value, complete value → ∀ index,
        Covered routing complete
          (frames.eval model binders ++ [⟨qualifyProtocolSite context.applicationPrefix site,index⟩])
          (frames.eval model binders ++ [⟨qualifyProtocolSite context.applicationPrefix site,index⟩])
          (sourceBody (.cons (some index)
            ((maskValues (context.roles role) (context.mapScopes spec.stateScopes) value).append
              (Comps.eval (LawResults.empty model) captures binders)))) := by
      intro value valid index
      apply Classical.choice
      obtain ⟨actual, rfl⟩ := valid
      let nextBinders : Binders model (RepeatScope spec.state scope) := .cons index (.cons actual.present binders)
      have entered := related.repeatEnter routing.context binders actual index reachedHistory
        (Original.encodeHelperResult_eq (visibleState_data visible) actual)
      have bodyMeaning := normalizeRegion_soundOn (model := model) (actions := Occurrence.actions)
        (iterations := Occurrence.iterations) (tables := tables) (protocols := protocols) (context := context)
        {strict := true, callees := callees} (LawResults.empty model) processes role roster distinct
        (Comps.eval (LawResults.empty model) (repeatInputs captures) nextBinders)
        (LawsHold.empty _ _) (calleesHold _) callback
        ⟨repeatInputs captures, repeatInputs captures⟩ bodyForm normalized
        (bodyForm.lawsMatch_of_callsMatch bodyCertificate.callsMatch) nextBinders rfl
      have bodySource : sourceBody (.cons (some index)
          ((maskValues (context.roles role) (context.mapScopes spec.stateScopes) actual.present).append
            (Comps.eval (LawResults.empty model) captures binders))) =
          bodyForm.denoteOn model Occurrence.actions tables (LawResults.empty model) context
            (runsAtOn model Occurrence.actions Occurrence.iterations tables protocols context role) processes nextBinders := by
        rw [visibleState_mask mappedVisible]
        exact (congrArg (fun inputs => callback.denote (meaningAtOn model Occurrence.actions
          Occurrence.iterations tables protocols context role) inputs.get)
          (repeatInputs_eval binders actual.present index captures).symm).trans bodyMeaning
      rw [bodySource]
      have checked := bodyIH model tables bindings protocols processes calleesHold selectionMeaning captured nextBinders reachedHistory _ entered (by retain_connection_frame)
      have converted := checked.mapPost (fun value returned => by
        obtain ⟨frame, read, _⟩ := returned
        rw [visibleState_mask visible] at read
        obtain ⟨data, encoded, reading⟩ := Original.outputReferences_read value yieldLocations read
        obtain ⟨actual, present, encoding⟩ := visibleState_values visible model value encoded
        exact (show complete value from ⟨actual,present⟩))
      exact ⟨by simpa only [nextBinders, repeatFrames_eval] using converted⟩
    have loopProof := repeatCovered routing (frames.eval model binders) spec context (context.roles role)
      active (Comps.eval (LawResults.empty model) captures binders) sourceBody site complete
      (fun value valid => by simpa only [visibleState_mask mappedVisible] using valid)
      bodyLaw (count.eval (LawResults.empty model) binders) initialValues.present ⟨initialValues,rfl⟩
    change Nonempty (Covered _ _ _ _ ((denoteRepeatOn spec context (context.roles role)
      (some (count.eval (LawResults.empty model) binders))
      (Comps.eval (LawResults.empty model) initial binders)
      (Comps.eval (LawResults.empty model) captures binders) sourceBody Occurrence.iterations site).bind _))
    rw [initialPresent]
    refine ⟨loopProof.bind ?_⟩
    intro value valid
    apply Classical.choice
    obtain ⟨actual, rfl⟩ := valid
    refine ⟨?_⟩
    simpa only [frames_cons, Form.denoteOn, PIR.Process.bind] using
      tailIH model tables bindings protocols processes calleesHold selectionMeaning captured (.cons actual.present binders) reachedHistory _
        (related.repeatExit routing.context binders actual reachedHistory
          (Original.encodeHelperResult_eq (visibleState_data visible) actual)) (by retain_connection_frame)
  | @projectedRepeat context definitions callees selection out role scopes outputs history scope frames layout spec site callback count initial captures next body rest
      roster distinct active visibility stateSorts schema countReference countRead initialLocations yieldLocations
      stateReferences initialReferences yieldData yielded initialHistory bodyHistory initialRead initialProjection yieldProjection
      historyRead initialProfile bodyProfile bodyForm normalized bodyCertificate nextMatched tail bodyIH tailIH =>
    apply Classical.choice
    let projected : Values (Component model.Value) spec.state → Prop := fun value =>
      ∃ physical, Original.roleOutputValues role spec.stateScopes
        (maskValues role spec.stateScopes value) = some physical
    let initialValues := Comps.eval (LawResults.empty model) initial binders
    obtain ⟨data, encoded, initialReading⟩ := Original.outputReferences_read initialValues initialProjection (initialRead.sound related)
    have initialValid : projected initialValues := by
      refine ⟨data, ?_⟩
      rw [Original.roleOutputValues_mask role initialValues encoded]
      exact encoded
    let sourceBody := (runsAtOn model Occurrence.actions Occurrence.iterations tables protocols context role).callback spec callback
    have bodyLaw : ∀ value, projected value → ∀ index,
        Covered routing projected
          (frames.eval model binders ++ [⟨qualifyProtocolSite context.applicationPrefix site,index⟩])
          (frames.eval model binders ++ [⟨qualifyProtocolSite context.applicationPrefix site,index⟩])
          (sourceBody (.cons (some index)
            ((maskValues (context.roles role) (context.mapScopes spec.stateScopes) value).append
              (Comps.eval (LawResults.empty model) captures binders)))) := by
      intro value valid index
      apply Classical.choice
      obtain ⟨physical, encodedValues⟩ := valid
      let nextBinders : Binders model (RepeatScope spec.state scope) := .cons index (.cons value binders)
      have entered := related.projectedEnter routing.context role spec.stateScopes binders value index reachedHistory encodedValues
      have bodyMeaning := normalizeRegion_soundOn (model := model) (actions := Occurrence.actions)
        (iterations := Occurrence.iterations) (tables := tables) (protocols := protocols) (context := context)
        {strict := true, callees := callees} (LawResults.empty model) processes role roster distinct
        (Comps.eval (LawResults.empty model) (projectedInputs role captures) nextBinders)
        (LawsHold.empty _ _) (calleesHold _) callback
        ⟨projectedInputs role captures, projectedInputs role captures⟩ bodyForm normalized
        (bodyForm.lawsMatch_of_callsMatch bodyCertificate.callsMatch) nextBinders rfl
      have bodySource : sourceBody (.cons (some index)
          ((maskValues (context.roles role) (context.mapScopes spec.stateScopes) value).append
            (Comps.eval (LawResults.empty model) captures binders))) =
          bodyForm.denoteOn model Occurrence.actions tables (LawResults.empty model) context
            (runsAtOn model Occurrence.actions Occurrence.iterations tables protocols context role) processes nextBinders := by
        rw [← mask_visibility visibility]
        exact (congrArg (fun inputs => callback.denote (meaningAtOn model Occurrence.actions
          Occurrence.iterations tables protocols context role) inputs.get)
          (projectedInputs_eval role binders value index captures).symm).trans bodyMeaning
      rw [bodySource]
      have checked := bodyIH model tables bindings protocols processes calleesHold selectionMeaning captured nextBinders reachedHistory _ entered (by retain_connection_frame)
      have converted := checked.mapPost (fun value returned => by
        obtain ⟨frame, read, _⟩ := returned
        obtain ⟨physical, encoded, reading⟩ := Original.outputReferences_read
          (maskValues role spec.stateScopes value) yieldProjection read
        exact (show projected value from ⟨physical, encoded⟩))
      exact ⟨by simpa only [nextBinders, repeatFrames_eval] using converted⟩
    have loopProof := repeatCovered routing (frames.eval model binders) spec context (context.roles role)
      active (Comps.eval (LawResults.empty model) captures binders) sourceBody site projected
      (fun value valid => by simpa only [projected, ← mask_visibility visibility, maskValues_idempotent] using valid)
      bodyLaw (count.eval (LawResults.empty model) binders) initialValues initialValid
    change Nonempty (Covered _ _ _ _ ((denoteRepeatOn spec context (context.roles role)
      (some (count.eval (LawResults.empty model) binders)) initialValues
      (Comps.eval (LawResults.empty model) captures binders) sourceBody Occurrence.iterations site).bind _))
    rw [Original.repeat_bind_mask]
    refine ⟨loopProof.bind ?_⟩
    intro value valid
    apply Classical.choice
    obtain ⟨physical, encodedValues⟩ := valid
    change Nonempty (Covered _ _ _ _ (next.denoteOn model Occurrence.actions tables (LawResults.empty model) context
      (runsAtOn model Occurrence.actions Occurrence.iterations tables protocols context role) processes
      (.cons (maskValues (context.roles role) (context.mapScopes spec.stateScopes) value) binders)))
    rw [← mask_visibility visibility, ← ConnectionSubstitution.maskNext_denote role spec.stateScopes
      Occurrence.actions tables context _ processes next binders value]
    refine ⟨?_⟩
    simpa only [frames_cons] using
      tailIH model tables bindings protocols processes calleesHold selectionMeaning captured (.cons value binders) reachedHistory _
        (related.projectedExit routing.context role spec.stateScopes binders value reachedHistory encodedValues) (by retain_connection_frame)
  | @application context definitions callees out role scopes outputs history scope frames layout
      payload same library callee signature signatureMatch roles site arguments calleeOutputs calleeHistory
      spine extent physicalExtent admission returnSelection bodyCertificate next continuationChecked rest tail bodyIH tailIH =>
    rcases selectionMeaning with ⟨rfl, rfl, rfl⟩
    subst definitions
    let selected := library.entry callee
    have instantiated := ConnectionSubstitution.form_denote
      (Arguments.eval (LawResults.empty model) arguments binders) binders
      (fun binder => entryAt arguments binder) (ConnectionSubstitution.arguments_related arguments binders)
      Occurrence.actions (Occurrence.helpers model payload) (context.enter site roles)
      (runsAtOn model Occurrence.actions Occurrence.iterations (Occurrence.helpers model payload)
        (Occurrence.table model payload) (context.enter site roles) (calleeAt callees callee).role)
      (selected.earlier.processes model) selected.form
    have checked := bodyIH model (Occurrence.helpers model payload) (fun _ => rfl)
      (Occurrence.table model payload) (selected.earlier.processes model) (selected.earlier.holds model)
      ⟨rfl,rfl,rfl⟩ environment binders reachedHistory environment related
      (by simp [ArtifactBinding.Captures])
    change Covered _ _ _ _ ((library.processes model callee (context.enter site roles)
      (Arguments.eval (LawResults.empty model) arguments binders)).bind fun values =>
        next.denoteOn model Occurrence.actions (Occurrence.helpers model payload) (LawResults.empty model)
          context (runsAtOn model Occurrence.actions Occurrence.iterations (Occurrence.helpers model payload)
            (Occurrence.table model payload) context role) (library.processes model) (.cons values binders))
    rw [library.processes_entry, ConnectionLibrary.Entry.process_form, ← instantiated,
      ConnectionReturnProjection.bind_continuation returnSelection _ next continuationChecked]
    apply checked.bind
    intro values returned
    apply Classical.choice
    obtain ⟨frame, read, kept⟩ := returned
    obtain ⟨result, resultKept, nextRelated⟩ := applicationWitness binders related kept extent values
      (calleeAt callees callee).role (calleeAt callees callee).signature.outputScopes
      calleeOutputs read calleeHistory routing.context.suite admission
    refine ⟨?_⟩
    simpa only [frames_cons, Form.denoteOn, PIR.Process.bind] using
      tailIH model (Occurrence.helpers model payload) (fun _ => rfl) (Occurrence.table model payload)
        (library.processes model) (library.holds model) ⟨rfl,rfl,rfl⟩ captured (.cons values binders)
        reachedHistory result nextRelated (ArtifactBinding.captures_trans retained resultKept)
  | @applicationRetainedHistory context definitions callees out role scopes outputs history scope frames layout
      payload same library callee signature signatureMatch roles site arguments calleeOutputs calleeHistory
      spine extent physicalExtent admission inputHistory separate returnSelection bodyCertificate next continuationChecked rest tail bodyIH tailIH =>
    rcases selectionMeaning with ⟨rfl, rfl, rfl⟩
    subst definitions
    let selected := library.entry callee
    have instantiated := ConnectionSubstitution.form_denote
      (Arguments.eval (LawResults.empty model) arguments binders) binders
      (fun binder => entryAt arguments binder) (ConnectionSubstitution.arguments_related arguments binders)
      Occurrence.actions (Occurrence.helpers model payload) (context.enter site roles)
      (runsAtOn model Occurrence.actions Occurrence.iterations (Occurrence.helpers model payload)
        (Occurrence.table model payload) (context.enter site roles) (calleeAt callees callee).role)
      (selected.earlier.processes model) selected.form
    have checked := bodyIH model (Occurrence.helpers model payload) (fun _ => rfl)
      (Occurrence.table model payload) (selected.earlier.processes model) (selected.earlier.holds model)
      ⟨rfl,rfl,rfl⟩ environment binders reachedHistory environment related
      (by simp [ArtifactBinding.Captures])
    change Covered _ _ _ _ ((library.processes model callee (context.enter site roles)
      (Arguments.eval (LawResults.empty model) arguments binders)).bind fun values =>
        next.denoteOn model Occurrence.actions (Occurrence.helpers model payload) (LawResults.empty model)
          context (runsAtOn model Occurrence.actions Occurrence.iterations (Occurrence.helpers model payload)
            (Occurrence.table model payload) context role) (library.processes model) (.cons values binders))
    rw [library.processes_entry, ConnectionLibrary.Entry.process_form, ← instantiated,
      ConnectionReturnProjection.bind_continuation returnSelection _ next continuationChecked]
    apply checked.bind
    intro values returned
    apply Classical.choice
    obtain ⟨frame, read, kept⟩ := returned
    obtain ⟨result, resultKept, nextRelated⟩ := retainedApplicationWitness binders related kept extent values
      (calleeAt callees callee).role (calleeAt callees callee).signature.outputScopes
      calleeOutputs read calleeHistory routing.context.suite admission inputHistory.inputCell
    refine ⟨?_⟩
    simpa only [frames_cons, Form.denoteOn, PIR.Process.bind] using
      tailIH model (Occurrence.helpers model payload) (fun _ => rfl) (Occurrence.table model payload)
        (library.processes model) (library.holds model) ⟨rfl,rfl,rfl⟩ captured (.cons values binders)
        reachedHistory result nextRelated (ArtifactBinding.captures_trans retained resultKept)
  | guard equality left right reference readback tail ih =>
    letI := equality.decide model (left.eval (LawResults.empty model) binders) (right.eval (LawResults.empty model) binders)
    by_cases success : left.eval (LawResults.empty model) binders = right.eval (LawResults.empty model) binders
    · simpa only [Form.denoteOn, Form.denoteWithOn, success, ↓reduceIte] using
        ih model tables bindings protocols processes calleesHold selectionMeaning captured binders reachedHistory environment (readback.refined related success) (by retain_connection_frame)
    · simp only [Form.denoteOn, Form.denoteWithOn, success, ↓reduceIte]
      exact .halt _ _ .reject
  | trueGuard reference readback tail ih => exact ih model tables bindings protocols processes calleesHold selectionMeaning captured binders reachedHistory environment related (by retain_connection_frame)
  | falseGuard reference readback rest => exact .halt _ _ .reject

/-- Existing open-library interface for placements that contain no applications. -/
@[no_expose] noncomputable def Alignment.covered
    {routing : Original.Routing} {context : ProtocolContext} {definitions : List CheckedDefinition}
    {callees : List CalleeKey} {out : List Ty} {role : Nat} {scopes : List (List Nat)}
    {outputs : List Original.Location} {history : Option Nat}
    {scope : Scope} {frames : ScopedFrames scope} {layout : Layout scope}
    {form : Form [] callees scope out} {target : Block}
    (derivation : Derivation routing context definitions callees out role scopes outputs history frames layout form target)
    (model : DomainModel) (tables : Tables model (Occurrence.signature model.toCarriers))
    (bindings : ConnectionHelpers.TablesMatch model definitions tables)
    (protocols : ProtocolTable model.Value (Occurrence.signature model.toCarriers))
    (processes : CalleeProcesses model callees (Occurrence.signature model.toCarriers))
    (calleesHold : ∀ {types : List Ty} (inputs : Values (Component model.Value) types),
      CalleesHold protocols processes inputs)
    (binders : Binders model scope) (reachedHistory : Domain.History model.toCarriers)
    (environment : Domain.Environment model.toCarriers)
    (related : Holds model binders reachedHistory layout environment) :
    Covered routing (ReadReturns model role scopes outputs)
      (frames.eval model binders) (frames.eval model binders)
      (form.denoteOn model Occurrence.actions tables (LawResults.empty model) context
        (runsAtOn model Occurrence.actions Occurrence.iterations tables protocols context role) processes binders) :=
  (derivation.coveredRetained model tables bindings protocols processes calleesHold trivial [] binders
    reachedHistory environment related (by simp [ArtifactBinding.Captures])).mapPost
      (fun _ returned => by
        obtain ⟨frame, read, _⟩ := returned
        exact ⟨frame, read⟩)

noncomputable abbrev Derivation.covered := @Alignment.covered

/-- Every reached action and every typed reply in the actual source body is
covered. The finite related-frame premise rules out only physically impossible
presence branches; no success premise or restriction of responses is added. -/
@[no_expose] noncomputable def Certificate.routeCoverage
    {routing : Original.Routing} {context : ProtocolContext} {definitions : List CheckedDefinition}
    {role roster : Nat} {source : CheckedProtocol} {pattern : InputPattern source.inputs}
    {outputs : List Original.Location} {history : Option Nat} {frames : ScopedFrames pattern.scope}
    {layout : Layout pattern.scope} {target : Block}
    (certificate : Certificate routing context definitions role roster source pattern outputs history frames layout target)
    (distinct : RosterDistinct context role roster)
    (model : DomainModel) (tables : Tables model (Occurrence.signature model.toCarriers))
    (bindings : ConnectionHelpers.TablesMatch model definitions tables)
    (protocols : ProtocolTable model.Value (Occurrence.signature model.toCarriers))
    (binders : Binders model pattern.scope) (reachedHistory : Domain.History model.toCarriers)
    (environment : Domain.Environment model.toCarriers)
    (related : Holds model binders reachedHistory layout environment) :
    Original.RouteCoverage routing (frames.eval model binders) (frames.eval model binders)
      (source.body.denote (participantMeaningWithOn model (.silent _) Occurrence.actions tables
        (context.roles role) protocols context Occurrence.iterations) (pattern.environment model binders).get) := by
  rw [normalize_occurrence_sound {strict := true} source.body role roster pattern certificate.form
    certificate.normalized certificate.alignment.callsMatch distinct (LawResults.empty model)
    (fun (entry : Fin 0) => entry.elim0) binders (LawsHold.empty _ _) (fun (entry : Fin 0) => entry.elim0)]
  exact (certificate.alignment.covered model tables bindings protocols
    (fun (entry : Fin 0) => entry.elim0) (fun inputs => noCallees_hold _ inputs)
    binders reachedHistory environment related).coverage

/-- Full selected-library source coverage, proved by structural action induction. -/
@[no_expose] noncomputable def Certificate.selectedRouteCoverage
    {routing : Original.Routing} {context : ProtocolContext} {payload : UnitPayload}
    {callees : List CalleeKey} {library : ConnectionLibrary.Library payload callees}
    {role roster : Nat} {source : CheckedProtocol} {pattern : InputPattern source.inputs}
    {outputs : List Original.Location} {history : Option Nat} {frames : ScopedFrames pattern.scope}
    {layout : Layout pattern.scope} {target : Block}
    (certificate : Certificate routing context payload.definitions role roster source pattern outputs history
      frames layout target callees (.selected payload rfl library))
    (distinct : RosterDistinct context role roster) (model : DomainModel)
    (binders : Binders model pattern.scope) (reachedHistory : Domain.History model.toCarriers)
    (environment : Domain.Environment model.toCarriers)
    (related : Holds model binders reachedHistory layout environment) :
    Original.RouteCoverage routing (frames.eval model binders) (frames.eval model binders)
      (source.body.denote (participantMeaningWithOn model (.silent _) Occurrence.actions
        (Occurrence.helpers model payload) (context.roles role) (Occurrence.table model payload)
        context Occurrence.iterations) (pattern.environment model binders).get) := by
  rw [normalize_occurrence_sound {strict := true, callees := callees} source.body role roster pattern certificate.form
    certificate.normalized certificate.alignment.callsMatch distinct (LawResults.empty model)
    (library.processes model) binders (LawsHold.empty _ _) (library.holds model _)]
  exact (certificate.alignment.coveredRetained model (Occurrence.helpers model payload) (fun _ => rfl)
    (Occurrence.table model payload) (library.processes model) (library.holds model) ⟨rfl,rfl,rfl⟩ []
    binders reachedHistory environment related (by simp [ArtifactBinding.Captures])).coverage

end Zkc.Construction.ConnectionCertificate
