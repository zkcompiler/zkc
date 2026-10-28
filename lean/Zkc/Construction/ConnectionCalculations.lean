module

public import Zkc.Construction.OriginalHelperEncoding
public import Zkc.Source.Structured.ComponentClosure
public import Zkc.Source.Structured.NormalForm.Soundness

@[expose] public section

/-! Mechanical connections for nominal calculations and kept helpers.

The source and target use the same actual implementation. Declared data types
supply complete encoding and sorts; finite operand selection supplies readback.
These laws do not require mathematical reference laws or a root simulation.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Zkc.Construction.ConnectionCalculations
open Zkc.Source Zkc.Source.Structured
variable {carriers : Carriers}

theorem calculation_allowed (calculation : Calculation) : calculation.op.isCalculation = true := by
  cases calculation <;> rfl

/-- The actual callback tuple is empty for every constructed calculation. -/
def calculationRegions (calculation : Calculation) {Value : Ty → Type} {I : PIR.Signature} :
    Values (RegionFunction Value I) calculation.op.regions := by
  cases calculation <;> exact .nil

theorem calculationRegions_unique (calculation : Calculation) {Value : Ty → Type} {I : PIR.Signature}
    (bodies : Values (RegionFunction Value I) calculation.op.regions) :
    bodies = calculationRegions calculation := by
  cases calculation <;> cases bodies <;> rfl

/-- A name for the existing closed operation, not another evaluator. -/
abbrev closedCalculation (model : DomainModel) (calculation : Calculation)
    (arguments : Values model.Value calculation.op.arguments) :=
  Evaluation.operationOn model SiteObservations.closed [] calculation.op arguments
    (calculationRegions calculation)

/-- Silent calculations do not consult helper tables. The entire closed
process lifts, so an out-of-bounds read keeps its refusal. -/
theorem operation_closed (model : DomainModel) {I : PIR.Signature}
    (table : Evaluation.MeaningsOn model.toCarriers I) (calculation : Calculation)
    (arguments : Values model.Value calculation.op.arguments) :
    Evaluation.operationOn model (.silent I) table calculation.op arguments
        (calculationRegions calculation) =
      (closedCalculation model calculation arguments).interpret (closedLift (I := I)) := by
  cases calculation <;>
    (rcases arguments with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | _⟩⟩⟩) <;> try rfl
  simp only [closedCalculation, Calculation.op, calculationRegions, Evaluation.operationOn]
  split <;> rfl

/-- Present source component operations use precisely that closed meaning.
No adequacy assumption is needed for calculations, even stopping ones. -/
theorem component_calculation_closed (model : DomainModel) {I : PIR.Signature}
    (tables : Evaluation.ComponentTablesOn model.toCarriers I) (calculation : Calculation)
    (arguments : Values model.Value calculation.op.arguments) :
    Evaluation.componentOperationOn model (.silent I) tables calculation.op arguments.present
        (calculationRegions calculation) =
      ((closedCalculation model calculation arguments).interpret (closedLift (I := I))).bind
        (fun results => .done results.present) := by
  have strict : Evaluation.componentOperationOn model (.silent I) tables calculation.op
      arguments.present (calculationRegions calculation) =
      (Evaluation.operationOn model (.silent I) tables.closed calculation.op arguments
        (calculationRegions calculation)).bind (fun results => .done results.present) := by
    have strictOperation : Evaluation.componentOperationOn model (.silent I) tables calculation.op =
        strictComponent (Evaluation.meaningOn model (.silent I) tables.closed) calculation.op := by
      cases calculation <;> rfl
    rw [strictOperation]
    exact strictComponent_adequate
      (Evaluation.meaningOn model (.silent I) tables.closed) calculation.op arguments _
  rw [strict, operation_closed]

/-- The actual nominal calculation encoder preserves every result and stop.
Both type checks are finite properties of the declared signature. -/
theorem calculate_encoded (model : DomainModel) (calculation : Calculation)
    (arguments : Values model.Value calculation.op.arguments)
    (inputData : calculation.op.arguments.all Domain.dataType = true)
    (outputData : calculation.op.results.all Domain.dataType = true) :
    Domain.calculate model calculation (Original.encodeHelperResult arguments) =
      (match Domain.closedOutcome (closedCalculation model calculation arguments) with
      | .returned results => .returned (Original.encodeHelperResult results)
      | .stopped reason => .stopped reason) := by
  have decoded := Domain.decodeValues_encodeValues (Original.encodeHelperResult_eq inputData arguments)
  simp only [Domain.calculate, decoded]
  have operationEq (bodies : Values (RegionFunction model.Value closedInterface) calculation.op.regions) :
      Evaluation.operationOn model SiteObservations.closed [] calculation.op arguments bodies =
        closedCalculation model calculation arguments := by
    rw [calculationRegions_unique calculation bodies]
  rw [operationEq]
  change ((match Domain.closedOutcome (closedCalculation model calculation arguments) with
    | .stopped reason => .stopped reason
    | .returned results =>
      match Domain.encodeValues results with
      | some encoded => .returned encoded
      | none => .stopped .refused) : PIR.Outcome (Domain.Environment model.toCarriers)) = _
  cases Domain.closedOutcome (closedCalculation model calculation arguments) with
  | stopped reason => rfl
  | returned results => simp only [Original.encodeHelperResult_eq outputData results]

/-- General closed-calculation rule for the actual constructed view. Encoding
and sorts follow from the source types, including aggregates and fieldEmbed.
Only the local physical readback remains; the finite check below supplies it.
-/
theorem view_calculation (model : DomainModel) (calculation : Calculation)
    (arguments : Values model.Value calculation.op.arguments)
    (inputData : calculation.op.arguments.all Domain.dataType = true)
    (outputData : calculation.op.results.all Domain.dataType = true)
    (environment : Domain.Environment model.toCarriers) (references : List Nat)
    (read : Domain.read environment references = Domain.encodeValues arguments) :
    Domain.View.calculation model calculation references (calculation.op.results.map ValueSort.data)
        environment =
      ((closedCalculation model calculation arguments).interpret
        (closedLift (I := Domain.effects model.toCarriers))).bind
          (fun results => .done (environment ++ Original.encodeHelperResult results)) := by
  simp only [Domain.View.calculation, read, Original.encodeHelperResult_eq inputData arguments,
    calculate_encoded model calculation arguments inputData outputData]
  cases computed : closedCalculation model calculation arguments with
  | done results =>
    simp only [Domain.closedOutcome, Domain.View.append,
      Original.encodeHelperResult_sorts outputData results, ↓reduceIte,
      PIR.Process.interpret, PIR.Process.bind]
  | halt reason => rfl
  | call operation _ => exact nomatch operation

/-- Totality is the existing operation predicate, not an assumed success law. -/
theorem view_calculation_total (model : DomainModel) (calculation : Calculation)
    (total : calculation.op.total = true) (arguments : Values model.Value calculation.op.arguments)
    (inputData : calculation.op.arguments.all Domain.dataType = true)
    (outputData : calculation.op.results.all Domain.dataType = true)
    (environment : Domain.Environment model.toCarriers) (references : List Nat)
    (read : Domain.read environment references = Domain.encodeValues arguments) :
    Domain.View.calculation model calculation references (calculation.op.results.map ValueSort.data)
        environment =
      .done (environment ++ Original.encodeHelperResult (calculation.op.evalTotal model total arguments)) := by
  rw [view_calculation model calculation arguments inputData outputData environment references read,
    closedCalculation, NormalForm.operationOn_total model _ _ _ total]
  rfl

/-- Kept helpers need declaration membership and their complete data signature,
not a mathematical formula. Lookup uses admission's actual captured closure.
-/
theorem view_helper (model : DomainModel) (program : Program) (helper : Helper)
    (present : helper ∈ program.payload.definitions.map CheckedDefinition.helper)
    (arguments : Values model.Value helper.inputs)
    (inputData : helper.inputs.all Domain.dataType = true)
    (outputData : helper.outputs.all Domain.dataType = true)
    (environment : Domain.Environment model.toCarriers) (references : List Nat)
    (read : Domain.read environment references = Domain.encodeValues arguments) :
    Domain.View.helper model program helper.name references (helper.outputs.map ValueSort.data)
        environment =
      ((invoke (Domain.helperTable model program) helper arguments).interpret
        (closedLift (I := Domain.effects model.toCarriers))).bind
          (fun results => .done (environment ++ Original.encodeHelperResult results)) := by
  obtain ⟨entry, found, same⟩ := Evaluation.linked_lookupOn model SiteObservations.closed
    program.payload.linked helper present
  subst helper
  change (Domain.helperTable model program).find?
    (fun candidate => candidate.helper.name == entry.helper.name) = some entry at found
  have called := Domain.Binding.callHelper_of_lookup model program entry found arguments
    (Original.encodeHelperResult arguments) (Original.encodeHelperResult_eq inputData arguments)
  simp only [Domain.View.helper, read, Original.encodeHelperResult_eq inputData arguments, called]
  simp only [invoke, found, ↓reduceDIte]
  cases computed : entry.invoke arguments with
  | done results =>
    simp only [Domain.closedOutcome, Original.encodeHelperResult_eq outputData results,
      Domain.View.append, Original.encodeHelperResult_sorts outputData results,
      ↓reduceIte, PIR.Process.interpret, PIR.Process.bind]
  | halt reason => rfl
  | call operation _ => exact nomatch operation

/-- Read a physical data location for each typed source operand. Hidden
components and capabilities are refused; order and repeated operands persist.
The parent owns full layout validation and extension across instructions.
-/
def operandReferences {Γ : List Ty} (locations : List Original.Location) :
    {types : List Ty} → Operands Γ types → Option (List Nat)
  | _, .nil => some []
  | _, .cons position rest => do
      let .data reference ← locations[position.index]? | none
      let remaining ← operandReferences locations rest
      pure (reference :: remaining)

private theorem located_component {Γ : List Ty} {ty : Ty}
    {environment : Domain.Environment carriers} {locations : List Original.Location}
    (values : Values (Component carriers.Value) Γ) (position : Var Γ ty)
    (related : Original.ValuesHolds environment locations values)
    {location : Original.Location} (found : locations[position.index]? = some location) :
    Original.ComponentHolds environment location ty (values.get position) := by
  induction position generalizing locations with
  | here =>
    cases values with
    | cons value rest =>
      cases locations with
      | nil => cases related
      | cons head tail =>
        simp only [Var.index, List.getElem?_cons_zero, Option.some.injEq] at found
        subst location
        exact related.1
  | there position ih =>
    cases values with
    | cons value rest =>
      cases locations with
      | nil => cases related
      | cons head tail =>
        exact ih rest related.2 (by simpa only [Var.index, List.getElem?_cons_succ] using found)

/-- A passing finite selection and the existing frame relation provide all
present operands and exact nominal readback, without an instance read lemma.
-/
theorem operandReferences_read {Γ types : List Ty}
    {environment : Domain.Environment carriers} {locations : List Original.Location}
    (values : Values (Component carriers.Value) Γ) (operands : Operands Γ types)
    {references : List Nat} (checked : operandReferences locations operands = some references)
    (related : Original.ValuesHolds environment locations values) :
    ∃ arguments : Values carriers.Value types,
      operands.eval values.get = arguments.present ∧
      Domain.read environment references = Domain.encodeValues arguments := by
  induction operands generalizing references with
  | nil =>
    simp only [operandReferences, Option.some.injEq] at checked
    subst references
    exact ⟨.nil, rfl, rfl⟩
  | @cons ty types position rest ih =>
    cases found : locations[position.index]? with
    | none => simp [operandReferences, found] at checked
    | some location =>
      cases location with
      | absent => simp [operandReferences, found] at checked
      | capability _ => simp [operandReferences, found] at checked
      | data reference =>
        cases remaining : operandReferences locations rest with
        | none => simp [operandReferences, found, remaining] at checked
        | some refs =>
          simp only [operandReferences, found, remaining, bind, Option.bind,
            Option.pure_def, Option.some.injEq] at checked
          subst references
          obtain ⟨arguments, present, read⟩ := ih remaining
          obtain ⟨head, headEq, decoded⟩ := located_component values position related found
          cases physical : environment[reference]? with
          | none => simp [physical] at decoded
          | some encoded =>
            have encodedHead : Domain.Value.encode ty head = some encoded :=
              Domain.Value.encode_decode (by simpa [physical] using decoded)
            refine ⟨.cons head arguments, ?_, ?_⟩
            · simp only [Operands.eval, Values.present, headEq, present]
            · change refs.mapM (fun reference => environment[reference]?) = Domain.encodeValues arguments at read
              simp only [Domain.read, List.mapM_cons, physical, Domain.encodeValues,
                encodedHead, bind, Option.bind]
              rw [read]

/-- A finite operand check discharges the calculation rule's readback premise.
No source or target operation equation is supplied by the caller. -/
theorem view_calculation_of_operands (model : DomainModel) (calculation : Calculation)
    {Γ : List Ty} (values : Values (Component model.Value) Γ)
    (operands : Operands Γ calculation.op.arguments)
    {environment : Domain.Environment model.toCarriers} {locations : List Original.Location}
    {references : List Nat} (checked : operandReferences locations operands = some references)
    (related : Original.ValuesHolds environment locations values)
    (inputData : calculation.op.arguments.all Domain.dataType = true)
    (outputData : calculation.op.results.all Domain.dataType = true) :
    ∃ arguments : Values model.Value calculation.op.arguments,
      operands.eval values.get = arguments.present ∧
      Domain.View.calculation model calculation references (calculation.op.results.map ValueSort.data)
          environment =
        ((closedCalculation model calculation arguments).interpret
          (closedLift (I := Domain.effects model.toCarriers))).bind
            (fun results => .done (environment ++ Original.encodeHelperResult results)) := by
  obtain ⟨arguments, present, read⟩ := operandReferences_read values operands checked related
  exact ⟨arguments, present,
    view_calculation model calculation arguments inputData outputData environment references read⟩

/-- The same finite check supplies the kept-helper rule's complete operands. -/
theorem view_helper_of_operands (model : DomainModel) (program : Program) (helper : Helper)
    (present : helper ∈ program.payload.definitions.map CheckedDefinition.helper)
    {Γ : List Ty} (values : Values (Component model.Value) Γ)
    (operands : Operands Γ helper.inputs)
    {environment : Domain.Environment model.toCarriers} {locations : List Original.Location}
    {references : List Nat} (checked : operandReferences locations operands = some references)
    (related : Original.ValuesHolds environment locations values)
    (inputData : helper.inputs.all Domain.dataType = true)
    (outputData : helper.outputs.all Domain.dataType = true) :
    ∃ arguments : Values model.Value helper.inputs,
      operands.eval values.get = arguments.present ∧
      Domain.View.helper model program helper.name references (helper.outputs.map ValueSort.data)
          environment =
        ((invoke (Domain.helperTable model program) helper arguments).interpret
          (closedLift (I := Domain.effects model.toCarriers))).bind
            (fun results => .done (environment ++ Original.encodeHelperResult results)) := by
  obtain ⟨arguments, presentArguments, read⟩ := operandReferences_read values operands checked related
  exact ⟨arguments, presentArguments,
    view_helper model program helper present arguments inputData outputData environment references read⟩

section Forms
open NormalForm
variable (model : DomainModel) {I : PIR.Signature} {laws : List LawKey} {callees : List CalleeKey}
  (actions : PIR.OperationInterpretation (Interface model) I)
  (results : LawResults model laws) (context : ProtocolContext)
  (runs : Runs model I) (processes : CalleeProcesses model callees I)
  {Δ : Scope} {out : List Ty}

/-- The actual normal-form compute node runs the same closed calculation.
Its continuation receives every returned value; a stop never reaches it. -/
theorem form_compute_closed (tables : Tables model I) (calculation : Calculation)
    (terms : Terms laws Δ calculation.op.arguments)
    (next : Form laws callees (.results calculation.op.results :: Δ) out)
    (binders : Binders model Δ) :
    (Form.compute calculation.op (calculation_allowed calculation) terms next).denoteOn
        model actions tables results context runs processes binders =
      ((closedCalculation model calculation (Terms.eval results terms binders)).interpret
        (closedLift (I := I))).bind fun values =>
          next.denoteOn model actions tables results context runs processes (.cons values binders) := by
  change (Evaluation.operationOn model (.silent I) tables.closed calculation.op
    (Terms.eval results terms binders)
    (calculation.op.calculationRegions (calculation_allowed calculation))).bind _ = _
  rw [calculationRegions_unique calculation
    (calculation.op.calculationRegions (calculation_allowed calculation)), operation_closed]
  rfl

/-- Strict kept calls use the actual declaration fold, including the captured
prefix of every dependency. Mathematical helper laws are unnecessary here. -/
theorem form_strict_closed (definitions : List CheckedDefinition) (helper : Helper)
    (terms : Terms laws Δ helper.inputs)
    (next : Form laws callees (.results helper.outputs :: Δ) out)
    (binders : Binders model Δ) :
    (Form.strict helper terms next).denoteOn model actions
        (definitions.foldl (Evaluation.ComponentTablesOn.extend model (.silent I)) ⟨[], []⟩)
        results context runs processes binders =
      ((invoke (definitions.foldl (Evaluation.extendMeaningsOn model SiteObservations.closed) [])
        helper (Terms.eval results terms binders)).interpret (closedLift (I := I))).bind fun values =>
          next.denoteOn model actions
            (definitions.foldl (Evaluation.ComponentTablesOn.extend model (.silent I)) ⟨[], []⟩)
            results context runs processes (.cons values binders) := by
  change (invoke _ helper _).bind _ = _
  rw [Evaluation.closed_invoke_componentTablesOn]
  rfl

/-- A kept Math node on present operands has the same closed implementation.
This does not align a separately inlined or rewritten Math helper body. -/
theorem form_math_present_closed (definitions : List CheckedDefinition) (helper : Helper)
    (terms : Values (Comp laws Δ) helper.inputs) (arguments : Values model.Value helper.inputs)
    (next : Form laws callees (.tuple helper.outputs :: Δ) out)
    (binders : Binders model Δ) (present : Comps.eval results terms binders = arguments.present) :
    (Form.math helper terms next).denoteOn model actions
        (definitions.foldl (Evaluation.ComponentTablesOn.extend model (.silent I)) ⟨[], []⟩)
        results context runs processes binders =
      ((invoke (definitions.foldl (Evaluation.extendMeaningsOn model SiteObservations.closed) [])
        helper arguments).interpret (closedLift (I := I))).bind fun values =>
          next.denoteOn model actions
            (definitions.foldl (Evaluation.ComponentTablesOn.extend model (.silent I)) ⟨[], []⟩)
            results context runs processes (.cons values.present binders) := by
  change (invoke _ helper (Comps.eval results terms binders)).bind _ = _
  rw [present, Evaluation.ComponentTablesOn.adequate_fold model _ _
    (Evaluation.ComponentTablesOn.adequate_empty model) definitions helper arguments,
    Evaluation.closed_invoke_componentTablesOn, PIR.Process.bind_assoc]
  rfl

end Forms

end Zkc.Construction.ConnectionCalculations

namespace Zkc.Construction.Original
open Zkc.Source Zkc.Source.Structured ConnectionCalculations

/-- Construct a calculation certificate from the actual closed evaluator.
All encoding and sort laws come from the signature, without a Simulation input.
-/
noncomputable def Simulation.closedCalculationOn (model : DomainModel) (routing : Routing)
    (calculation : Calculation) (arguments : Values model.Value calculation.op.arguments)
    (inputData : calculation.op.arguments.all Domain.dataType = true)
    (outputData : calculation.op.results.all Domain.dataType = true)
    (state : State model.toCarriers) (environment : Domain.Environment model.toCarriers)
    (references : List Nat) (read : Domain.read environment references = Domain.encodeValues arguments) :
    Simulation (HelperReturns encodeHelperResult state environment) (fun _ frame => frame = environment)
      (fold routing ((closedCalculation model calculation arguments).interpret
        (closedLift (I := Occurrence.signature model.toCarriers))) state)
      (Domain.View.calculation model calculation references
        (calculation.op.results.map ValueSort.data) environment) := by
  rw [view_calculation model calculation arguments inputData outputData environment references read]
  cases computed : closedCalculation model calculation arguments with
  | done results =>
    simp only [PIR.Process.interpret, PIR.Process.bind, fold, PIR.Process.interpretState]
    exact .done ⟨results, rfl, rfl⟩
  | halt reason => exact .halt reason
  | call operation _ => exact nomatch operation

end Zkc.Construction.Original
