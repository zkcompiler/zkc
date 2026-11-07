module

public import Zkc.Construction.ConnectionMathRegion
public import Zkc.Construction.ConnectionMathSimulation
public import Zkc.Construction.ConnectionFiniteFold
public import Zkc.Source.Structured.DomainLinking

@[expose] public section

/-! Soundness of finite inlined-region connection evidence. The source is the
existing typed region under its actual lexical helper prefix. Neither a chosen
mathematical reference nor a source-specific evaluator participates. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Zkc.Construction.ConnectionMathRegion
open Zkc.Source Zkc.Source.Structured ConnectionMathFrames

/-- The exact source meaning captured at this helper declaration. -/
abbrev meaning (model : DomainModel) (definitions : List CheckedDefinition) :=
  Evaluation.meaningOn model SiteObservations.closed
    (definitions.foldl (Evaluation.extendMeaningsOn model SiteObservations.closed) [])

theorem calculation_meaning (model : DomainModel) (definitions : List CheckedDefinition)
    (operation : Calculation) (values : Values model.Value operation.op.arguments) :
    Evaluation.operationOn model SiteObservations.closed
        (definitions.foldl (Evaluation.extendMeaningsOn model SiteObservations.closed) [])
        operation.op values ((sourceRegions operation).denote (meaning model definitions)) =
      ConnectionCalculations.closedCalculation model operation values := by
  rw [ConnectionCalculations.calculationRegions_unique operation
    ((sourceRegions operation).denote (meaning model definitions))]
  rw [ConnectionCalculations.operation_closed]
  cases computed : ConnectionCalculations.closedCalculation model operation values with
  | done => rfl
  | halt => rfl
  | call operation _ => exact nomatch operation

theorem branch_meaning (model : DomainModel) (definitions : List CheckedDefinition)
    {captures results : List Ty} (condition : Bool) (values : Values model.Value captures)
    (yes no : Region dialect captures results) :
    Evaluation.operationOn model SiteObservations.closed
      (definitions.foldl (Evaluation.extendMeaningsOn model SiteObservations.closed) [])
      (.branch captures results)
      (.cons condition values)
      ((Regions.cons yes (.cons no .nil)).denote (meaning model definitions)) =
      (if condition then yes.denote (meaning model definitions) values.get
        else no.denote (meaning model definitions) values.get) := by
  cases condition <;> rfl

theorem invocation_meaning (model : DomainModel) (definitions : List CheckedDefinition)
    (helper : Helper) (values : Values model.Value helper.inputs) :
    Evaluation.operationOn model SiteObservations.closed
      (definitions.foldl (Evaluation.extendMeaningsOn model SiteObservations.closed) [])
      (.invoke helper) values (Regions.nil.denote (meaning model definitions)) =
      invoke (definitions.foldl (Evaluation.extendMeaningsOn model SiteObservations.closed) [])
        helper values := rfl

theorem fold_meaning (model : DomainModel) (definitions : List CheckedDefinition)
    (spec : FoldSpec) (values : Values model.Value spec.arguments) :
    Evaluation.operationOn model SiteObservations.closed
      (definitions.foldl (Evaluation.extendMeaningsOn model SiteObservations.closed) [])
      (.fold spec) values (Regions.nil.denote (meaning model definitions)) =
      Evaluation.denoteFoldOn
        (definitions.foldl (Evaluation.extendMeaningsOn model SiteObservations.closed) []) spec values := rfl

/-- All returned coordinates, final extent and original caller capture are
retained. Stopped executions remain stops and satisfy no success premise. -/
def Returns {carriers : Carriers} {outputs : List Ty}
    (captured : Domain.Environment carriers) (references : List Nat) (size : Nat)
    (values : Values carriers.Value outputs) (frame : Domain.Environment carriers) : Prop :=
  Original.MathReturns references values frame ∧ frame.length = size ∧
    ArtifactBinding.Captures captured frame

/-- Each operation and each closed callback has to be derived from its exact
source tree. This theorem supplies the complete semantic connection. -/
noncomputable def Alignment.sound {definitions : List CheckedDefinition}
    {inputs outputs : List Ty} {body : Region dialect inputs outputs}
    {locations : List Original.Location} {size : Nat} {target : TargetBlock}
    {references : List Nat} {finalSize : Nat}
    (certificate : Alignment definitions body locations size target references finalSize)
    (model : DomainModel) (values : Values model.Value inputs)
    (environment : Domain.Environment model.toCarriers)
    (data : outputs.all Domain.localType = true)
    (sizeEq : environment.length = size)
    (bound : Original.LocationsBound size locations)
    (related : Original.ValuesHolds environment locations values.present) :
    Original.Simulation (Returns environment references finalSize)
      (fun _ frame => ArtifactBinding.Captures environment frame)
      ((body.denote (meaning model definitions) values.get).interpret
        (closedLift (I := Domain.effects model.toCarriers)))
      (target model environment) := by
  induction certificate generalizing environment with
  | returned positions locations size references selected =>
      exact .done ⟨(read_present values positions selected related).trans
        (Original.encodeHelperResult_eq data _), sizeEq,
        by simp [ArtifactBinding.Captures]⟩
  | stopped reason locations size references finalSize => exact .halt reason
  | calculation operation operands locations size references selected inputData outputData tail ih =>
      simp only [Region.denote, PIR.Process.interpret_bind, calculation_meaning]
      apply Original.Simulation.checkpoint environment (by simp [ArtifactBinding.Captures])
      apply (Original.Simulation.mathCalculation model operation (operands.eval values.get)
        inputData outputData environment references (read_present values operands selected related)).bind
      · intro _ frame retained
        exact retained
      · intro results final returned
        subst final
        let encoded := Original.encodeHelperResult results
        have encoding : Domain.encodeValues results = some encoded := Original.encodeHelperResult_eq outputData results
        have kept := ArtifactBinding.captures_append environment encoded
        apply Original.Simulation.checkpoint (environment ++ encoded) kept
        have extended := extend values.present results (by simpa only [sizeEq] using bound) related encoding
        have extent : (environment ++ encoded).length = size + operation.op.results.length := by
          rw [List.length_append, sizeEq, encoded_length results encoding]
        have bounds := append_bound (allocated_bound size operation.op.results.length)
          (bound_mono bound (Nat.le_add_right _ _))
        have connected := ih (results.append values) (environment ++ encoded) data extent bounds
          (by simpa only [sizeEq, present_append] using extended)
        rw [← append_get]
        exact connected.mapRelations
          (fun _ _ returned => ⟨returned.1, returned.2.1,
            ArtifactBinding.captures_trans kept returned.2.2⟩)
          (fun _ _ retained => ArtifactBinding.captures_trans kept retained)
  | selected program condition captured yes no locations size selector references selected captureData resultData
      yesRegion noRegion yesInputs noInputs formed yesConnected noConnected tail yesIH noIH tailIH =>
      rename_i inputs captures resultTypes outputs next yesBody noBody rest yesSize noSize finalSize yielded
      let capturedValues := captured.eval values.get
      let encodedCaptures := Original.encodeHelperResult capturedValues
      have captureEncoding := Original.encodeHelperResult_eq captureData capturedValues
      have capturedExtent := encoded_length capturedValues captureEncoding
      have capturedBound : Original.LocationsBound captures.length (arguments captures.length) := by
        simpa only [Nat.zero_add, arguments] using allocated_bound 0 captures.length
      have capturedRelation : Original.ValuesHolds encodedCaptures (arguments captures.length) capturedValues.present := by
        simpa only [List.nil_append, List.append_nil, List.length_nil, arguments] using
          valuesHolds_encoded capturedValues [] [] captureEncoding
      have sourceYes := yesIH capturedValues encodedCaptures resultData
        capturedExtent capturedBound capturedRelation
      have sourceNo := noIH capturedValues encodedCaptures resultData
        capturedExtent capturedBound capturedRelation
      obtain ⟨selectorRead, capturesRead⟩ := selection_read values condition captured selected captureData related
      have branch := Original.Simulation.mathBranch program capturedValues (values.get condition)
        (yes.denote (meaning model definitions) capturedValues.get)
        (no.denote (meaning model definitions) capturedValues.get)
        (yesBody model) (noBody model) yesRegion noRegion yesInputs noInputs formed captureData resultData
        environment selector references selectorRead capturesRead
        (sourceYes.mapRelations (fun _ _ returned => returned.1) (fun _ _ retained => retained))
        (sourceNo.mapRelations (fun _ _ returned => returned.1) (fun _ _ retained => retained))
      simp only [Region.denote, Operands.eval, branch_meaning, PIR.Process.interpret_bind]
      apply Original.Simulation.checkpoint environment (by simp [ArtifactBinding.Captures])
      apply branch.bind
      · intro _ frame retained
        exact retained
      · intro results final returned
        subst final
        let encoded := Original.encodeHelperResult results
        have encoding := Original.encodeHelperResult_eq resultData results
        have kept := ArtifactBinding.captures_append environment encoded
        apply Original.Simulation.checkpoint (environment ++ encoded) kept
        have extended := extend values.present results (by simpa only [sizeEq] using bound) related encoding
        have extent : (environment ++ encoded).length = size + resultTypes.length := by
          rw [List.length_append, sizeEq, encoded_length results encoding]
        have bounds := append_bound (allocated_bound size resultTypes.length)
          (bound_mono bound (Nat.le_add_right _ _))
        have connected := tailIH (results.append values) (environment ++ encoded) data extent bounds
          (by simpa only [sizeEq, present_append] using extended)
        rw [← append_get]
        exact connected.mapRelations
          (fun _ _ returned => ⟨returned.1, returned.2.1,
            ArtifactBinding.captures_trans kept returned.2.2⟩)
          (fun _ _ retained => ArtifactBinding.captures_trans kept retained)
  | invoke linked definition member operands locations size references selected inputData outputData
      head tail headIH tailIH =>
      rename_i inputs outputs next spine rest returned yielded middleSize finalSize
      let args := operands.eval values.get
      have encoding := Original.encodeHelperResult_eq inputData args
      have inputRead := read_present values operands selected related
      rw [encoding] at inputRead
      obtain ⟨inputRelated, inputBound⟩ := read_encoded args environment references encoding inputRead
      have invocation := Evaluation.definitions_invoke_bodyOn model SiteObservations.closed
        definitions linked definition member args
      simp only [Region.denote, invocation_meaning]
      rw [invocation, PIR.Process.interpret_bind, ConnectionTargetPrefix.Prefix.plug_eq_bind]
      apply (headIH args environment outputData sizeEq
        (by simpa only [sizeEq] using inputBound) inputRelated).bind
      · intro _ _ retained
        exact retained
      · intro results frame returned
        have encoding := Original.encodeHelperResult_eq outputData results
        obtain ⟨resultRelation, resultBound⟩ := read_encoded results frame _ encoding returned.1
        have oldBound : Original.LocationsBound environment.length locations := by simpa only [sizeEq] using bound
        have oldRelation := Original.valuesHolds_of_captures values.present oldBound related returned.2.2
        have larger : environment.length ≤ frame.length := by
          have lengths := congrArg List.length returned.2.2
          simp only [List.length_take] at lengths
          omega
        have extended := valuesHolds_append results.present values.present resultRelation oldRelation
        have bounds := append_bound resultBound (bound_mono oldBound larger)
        have connected := tailIH (results.append values) frame data returned.2.1
          (by simpa only [returned.2.1] using bounds)
          (by simpa only [present_append] using extended)
        rw [← append_get]
        exact connected.mapRelations
          (fun _ _ final => ⟨final.1, final.2.1,
            ArtifactBinding.captures_trans returned.2.2 final.2.2⟩)
          (fun _ _ retained => ArtifactBinding.captures_trans returned.2.2 retained)
  | finiteFold program after split domain step predicate spec fresh resolved operands locations size references
      selected inputData outputData tail ih =>
      simp only [Region.denote, fold_meaning, PIR.Process.interpret_bind]
      rw [ConnectionFiniteFold.lexical model program definitions after spec split fresh]
      apply Original.Simulation.checkpoint environment (by simp [ArtifactBinding.Captures])
      apply (ConnectionFiniteFold.simulation model program domain step predicate spec resolved
        (operands.eval values.get) inputData outputData environment references
        (read_present values operands selected related)).bind
      · intro _ frame retained
        exact retained
      · intro results final returned
        subst final
        let encoded := Original.encodeHelperResult results
        have encoding : Domain.encodeValues results = some encoded := Original.encodeHelperResult_eq outputData results
        have kept := ArtifactBinding.captures_append environment encoded
        apply Original.Simulation.checkpoint (environment ++ encoded) kept
        have extended := extend values.present results (by simpa only [sizeEq] using bound) related encoding
        have extent : (environment ++ encoded).length = size + spec.state.length := by
          rw [List.length_append, sizeEq, encoded_length results encoding]
        have bounds := append_bound (allocated_bound size spec.state.length)
          (bound_mono bound (Nat.le_add_right _ _))
        have connected := ih (results.append values) (environment ++ encoded) data extent bounds
          (by simpa only [sizeEq, present_append] using extended)
        rw [← append_get]
        exact connected.mapRelations
          (fun _ _ final => ⟨final.1, final.2.1,
            ArtifactBinding.captures_trans kept final.2.2⟩)
          (fun _ _ retained => ArtifactBinding.captures_trans kept retained)
  | bind intermediateData head tail headIH tailIH =>
      rename_i inputs intermediate outputs body next locations size middleSize finalSize spine rest intermediateReferences yielded
      rw [ConnectionTargetPrefix.Prefix.plug_eq_bind]
      simp only [Region.denote, PIR.Process.interpret_bind]
      apply (headIH values environment intermediateData sizeEq bound related).bind
      · intro _ _ retained
        exact retained
      · intro results frame returned
        have encoding := Original.encodeHelperResult_eq intermediateData results
        obtain ⟨resultRelation, resultBound⟩ := read_encoded results frame _ encoding returned.1
        have oldBound : Original.LocationsBound environment.length locations := by simpa only [sizeEq] using bound
        have oldRelation := Original.valuesHolds_of_captures values.present oldBound related returned.2.2
        have larger : environment.length ≤ frame.length := by
          have lengths := congrArg List.length returned.2.2
          simp only [List.length_take] at lengths
          omega
        have extended := valuesHolds_append results.present values.present resultRelation oldRelation
        have bounds := append_bound resultBound (bound_mono oldBound larger)
        have connected := tailIH (results.append values) frame data returned.2.1
          (by simpa only [returned.2.1] using bounds)
          (by simpa only [present_append] using extended)
        rw [← append_get]
        exact connected.mapRelations
          (fun _ _ final => ⟨final.1, final.2.1,
            ArtifactBinding.captures_trans returned.2.2 final.2.2⟩)
          (fun _ _ retained => ArtifactBinding.captures_trans returned.2.2 retained)

/-- Install a structurally connected mathematical slice at an actual embedded
region. Capture locations, extent, frame preservation and the output tuple are
derived here. The caller supplies the checked source/body association, not a
second execution law or a postulated result for the generated helper. -/
noncomputable def Alignment.embedded {definitions : List CheckedDefinition}
    {inputs captures outputs : List Ty} {body : Region dialect inputs outputs}
    {target : TargetBlock} {region : InstructionRegion} {finalSize : Nat}
    {sourceReferences : List Nat}
    (certificate : Alignment definitions body (sourceReferences.map Original.Location.data) captures.length
      target region.yielded finalSize)
    (positions : Operands captures inputs)
    (selected : ConnectionCalculations.operandReferences (arguments captures.length) positions =
      some sourceReferences)
    (model : DomainModel) (program : Program) (context : Context)
    (inputSorts : region.inputs = captures.map ValueSort.data)
    (formed : checkClosedBodyResults .math (outputs.map ValueSort.data) region
      (checkClosedFrom .math (Domain.closedOperationMatches program)
        region.inputs region.instructions) = .ok ())
    (correspondence : Domain.Correspondence.Block (model := model) (program := program)
      (context := context) region.instructions (target model))
    (captureData : captures.all Domain.localType = true)
    (inputData : inputs.all Domain.localType = true)
    (outputData : outputs.all Domain.localType = true)
    (values : Values model.Value captures) (environment : Domain.Environment model.toCarriers)
    (references : List Nat)
    (read : Domain.read environment references = Domain.encodeValues values) :
    Original.Simulation (fun result frame ↦ frame = environment ++ Original.encodeHelperResult result)
      (fun _ frame ↦ ArtifactBinding.Captures environment frame)
      ((body.denote (meaning model definitions) (positions.eval values.get).get).interpret
        (closedLift (I := Domain.effects model.toCarriers)))
      (Domain.step model program context
        ⟨.mathCompute, references, outputs.map ValueSort.data, [region]⟩ environment) := by
  have encoding := Original.encodeHelperResult_eq captureData values
  have extent := encoded_length values encoding
  have captured : Original.ValuesHolds (Original.encodeHelperResult values)
      (arguments captures.length) values.present := by
    simpa only [List.nil_append, List.append_nil, List.length_nil, arguments] using
      valuesHolds_encoded values [] [] encoding
  have selectedEncoding := Original.encodeHelperResult_eq inputData (positions.eval values.get)
  have selectedRead := (read_present values positions selected captured).trans selectedEncoding
  have sourceFrame := read_encoded (positions.eval values.get) _ sourceReferences
    selectedEncoding selectedRead
  have connected := certificate.sound model (positions.eval values.get)
    (Original.encodeHelperResult values) outputData extent
    (by simpa only [extent] using sourceFrame.2) sourceFrame.1
  have placed := Original.Simulation.mathCompute program values
    (body.denote (meaning model definitions) (positions.eval values.get).get) (target model) region
    inputSorts formed captureData outputData environment references read
    (connected.mapRelations (fun _ _ result ↦ result.1) (fun _ _ retained ↦ retained))
  rw [Domain.Correspondence.mathCompute references (outputs.map ValueSort.data) region correspondence]
  exact placed

end Zkc.Construction.ConnectionMathRegion
