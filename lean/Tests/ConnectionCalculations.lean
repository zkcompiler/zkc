import Zkc.Construction.ConnectionCalculations
import Mathlib.Data.ZMod.Basic

/-! Nominal calculation, kept-helper, readback and all-reply controls.
The mixed model is operational test data, not a claim about field extensions.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Tests.ConnectionCalculations
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open Zkc.Construction.ConnectionCalculations

private def fieldCarrier (name : String) : Type := if name = "base" then Int else ZMod 5

private def toInt (name : String) : fieldCarrier name → Int := by
  unfold fieldCarrier
  split
  · exact id
  · exact fun value => value.val

private def fromInt (name : String) (value : Int) : fieldCarrier name := by
  unfold fieldCarrier
  split
  · exact value
  · exact (value : ZMod 5)

private def model : DomainModel where
  Field := fieldCarrier
  Group _ := Int
  fieldRing name := by unfold fieldCarrier; split <;> infer_instance
  fieldDecEq name := by unfold fieldCarrier; split <;> infer_instance
  inverse _ := none
  embed extension base value := fromInt extension (toInt base value)
  groupAdd _ := inferInstance
  groupDecEq _ := inferInstance
  smul _ field scalar point := toInt field scalar * point

private def base (value : Int) : Domain.Value model.toCarriers := .data (.field "base" value)
private def extension (value : ZMod 5) : Domain.Value model.toCarriers := .data (.field "extension" value)

example (left right : Int) :
    Domain.View.calculation model (.fieldAdd "base") [0, 1] [.data (.field "base")]
      [base left, base right] = .done [base left, base right, base (left + right)] :=
  view_calculation_total model (.fieldAdd "base") rfl
    (.cons left (.cons right .nil)) rfl rfl _ _ rfl

example (left right : ZMod 5) :
    Domain.View.calculation model (.fieldMultiply "extension") [0, 1] [.data (.field "extension")]
      [extension left, extension right] =
      .done [extension left, extension right, extension (left * right)] :=
  view_calculation_total model (.fieldMultiply "extension") rfl
    (.cons left (.cons right .nil)) rfl rfl _ _ rfl

-- The base and extension have distinct host types; the actual embedding is used.
example (value : Int) :
    Domain.View.calculation model (.fieldEmbed "extension" "base") [0] [.data (.field "extension")]
      [base value] = .done [base value, extension (value : ZMod 5)] :=
  view_calculation_total model (.fieldEmbed "extension" "base") rfl
    (.cons value .nil) rfl rfl _ _ rfl

example (point : Int) (scalar : ZMod 5) :
    Domain.View.calculation model (.groupScale "points" "extension") [0, 1] [.data (.group "points")]
      [.data (.group "points" point), extension scalar] =
      .done [.data (.group "points" point), extension scalar,
        .data (.group "points" (toInt "extension" scalar * point))] :=
  view_calculation_total model (.groupScale "points" "extension") rfl
    (.cons point (.cons scalar .nil)) rfl rfl _ _ rfl

private def packet : Ty := .product "record" "packet"
  (.cons (.field "base") (.cons (.field "extension") .nil))
private def packets : Ty := .sequence packet
private def packed (values : model.Value packets) : Domain.Value model.toCarriers :=
  .data ⟨packets, rfl, values⟩

-- Complete sequences of mixed products are encoded without a scalar adapter.
example (condition : Bool) (left right : model.Value packets) :
    Domain.View.calculation model (.select packets) [0, 1, 2] [.data packets]
      [.data (.boolean condition), packed left, packed right] =
      .done [.data (.boolean condition), packed left, packed right,
        packed (if condition then left else right)] :=
  view_calculation_total model (.select packets) rfl
    (.cons condition (.cons left (.cons right .nil))) rfl rfl _ _ rfl

example (values : List (model.Field "extension")) (index : Nat) (missing : values[index]? = none) :
    Domain.View.calculation model (.boundedAt "extension") [0, 1] [.data (.field "extension")]
      [.data (.vector "extension" values), .data (.index index)] = .halt .refused := by
  have same := view_calculation model (.boundedAt "extension")
    (.cons values (.cons index .nil)) rfl rfl
    [.data (.vector "extension" values), .data (.index index)] [0, 1] rfl
  refine same.trans ?_
  simp only [closedCalculation, Calculation.op, calculationRegions, Evaluation.operationOn,
    missing, PIR.Process.interpret, PIR.Process.bind]

example (values : List (model.Field "extension")) (index : Nat)
    (value : model.Field "extension") (found : values[index]? = some value) :
    Domain.View.calculation model (.boundedAt "extension") [0, 1] [.data (.field "extension")]
      [.data (.vector "extension" values), .data (.index index)] =
      .done [.data (.vector "extension" values), .data (.index index), extension value] := by
  have same := view_calculation model (.boundedAt "extension")
    (.cons values (.cons index .nil)) rfl rfl
    [.data (.vector "extension" values), .data (.index index)] [0, 1] rfl
  refine same.trans ?_
  simp only [closedCalculation, Calculation.op, calculationRegions, Evaluation.operationOn,
    found, PIR.Process.interpret, PIR.Process.bind]
  rfl

-- Nominal decoding, physical operand bounds and result declarations still refuse.
example : Domain.View.calculation model (.fieldAdd "extension") [0, 1] [.data (.field "extension")]
    [base 1, base 2] = .halt .refused := rfl

example : Domain.View.calculation model (.fieldConstant "base" 7) [0] [.data (.field "base")]
    [] = .halt .refused := rfl

example : Domain.View.calculation model (.fieldConstant "base" 7) [] [.data (.field "extension")]
    [] = .halt .refused := rfl

-- Type-directed checks exclude direct and nested service handles.
example : Domain.dataType (.service "random.base/0") = false := rfl
example : Domain.dataType (.sequence (.service "random.base/0")) = false := rfl

private def inputTypes : List Ty := [.field "base", .field "extension", .boolean]
private def inputLocations : List Original.Location := [.data 2, .data 0, .absent]
private def baseOperands : Operands inputTypes [.field "base", .field "base"] :=
  .cons .here (.cons .here .nil)

example : operandReferences inputLocations baseOperands = some [2, 2] := rfl
example : operandReferences inputLocations
    (Values.cons (.there (.there .here)) .nil : Operands inputTypes [.boolean]) = none := rfl
example : operandReferences [.capability 0]
    (Values.cons .here .nil : Operands [.service "random.base/0"] [.service "random.base/0"]) = none := rfl
example : operandReferences []
    (Values.cons .here .nil : Operands [.field "base"] [.field "base"]) = none := rfl

-- The check, together with the existing frame relation, supplies the read lemma.
example (environment : Domain.Environment model.toCarriers)
    (values : Values (Component model.Value) inputTypes)
    (related : Original.ValuesHolds environment inputLocations values) :
    ∃ arguments : Values model.Value (.fieldAdd "base" : Calculation).op.arguments,
      baseOperands.eval values.get = arguments.present ∧
      Domain.View.calculation model (.fieldAdd "base") [2, 2] [.data (.field "base")] environment =
        ((closedCalculation model (.fieldAdd "base") arguments).interpret
          (closedLift (I := Domain.effects model.toCarriers))).bind
            (fun results => .done (environment ++ Original.encodeHelperResult results)) :=
  view_calculation_of_operands model (.fieldAdd "base") values baseOperands rfl related rfl rfl

private def stopBody (reason : PIR.Stop) : Region dialect [] [] :=
  .letOp (.mark "stop") .nil .nil (.stop reason)
private def stopDefinition (reason : PIR.Stop) : CheckedDefinition :=
  ⟨"stop", .local, [], [], (stopBody reason).erase, stopBody reason, (stopBody reason).elaborate_erase⟩
private def mainBody : Region protocolDialect [] [] := .ret .nil
private def mainDefinition : CheckedProtocol :=
  ⟨⟨"main", ["P", "V"], [], [], [], []⟩, mainBody.erase, mainBody, mainBody.elaborate_erase⟩
private def snapshot (reason : PIR.Stop) : Snapshot where
  source := "sha256:" ++ String.ofList (List.replicate 64 '0')
  entry := "main"
  domains := []
  relations := []
  bindings := []
  definitions := [
    .function ⟨"stop", .local, .privateDef, [], [], none, [], some (.local "stop" []),
      .block [] (.stop reason "stop")⟩,
    .function ⟨"main", .protocol, .publicDef, [], [], some ⟨["P", "V"], [], []⟩,
      [], some (.protocol ⟨"main", []⟩), .block [] (.ret [])⟩]
  contracts := [⟨"main", []⟩]
  catalogue := ⟨[], [], []⟩
private def unit (reason : PIR.Stop) : UnitPayload where
  definitions := [stopDefinition reason]
  protocols := [mainDefinition]
  entryIndex := ⟨0, by decide⟩
  linked := by cases reason <;> decide +kernel
  protocolsLinked := by cases reason <;> decide +kernel
  available := by cases reason <;> rfl
  realizationClosed := by cases reason <;> decide +kernel
  mapClosed := by cases reason <;> decide +kernel
private def program (reason : PIR.Stop) : Program := ⟨snapshot reason, unit reason⟩

-- The synthetic source unit is actually admitted, with no helper success law.
set_option maxHeartbeats 2000000 in
example (reason : PIR.Stop) : check (snapshot reason) = .ok (program reason) := by
  cases reason <;> rfl

-- All five stops, including refused and exhausted, survive the kept Local call.
example (reason : PIR.Stop) (environment : Domain.Environment model.toCarriers) :
    Domain.View.helper model (program reason) "stop" [] [] environment = .halt reason := by
  have same := view_helper model (program reason) (stopDefinition reason).helper
    (by simp [program, unit]) .nil rfl rfl environment [] rfl
  refine same.trans ?_
  rfl

-- Reuse the existing nominal helper certificate, including stopping executions.
noncomputable example (reason : PIR.Stop) (routing : Original.Routing)
    (state : Original.State model.toCarriers) (environment : Domain.Environment model.toCarriers) :
    Original.Simulation (Original.HelperReturns Original.encodeHelperResult state environment)
      (fun _ frame => frame = environment)
      (Original.fold routing ((invoke (Domain.helperTable model (program reason))
        (stopDefinition reason).helper .nil).interpret
          (closedLift (I := Occurrence.signature model.toCarriers))) state)
      (Domain.View.helper model (program reason) "stop" [] [] environment) :=
  Original.Simulation.linkedDataHelperOn model (program reason) routing (stopDefinition reason).helper
    (by simp [program, unit]) rfl .nil environment [] rfl state rfl

-- A later helper invokes the earlier captured closure. Unrelated suffixes do
-- not replace that prefix with an independently supplied implementation.
private def wrapperBody (reason : PIR.Stop) : Region dialect [] [] :=
  .letOp (.invoke (stopDefinition reason).helper) .nil .nil (.ret .nil)
private def wrapperDefinition (reason : PIR.Stop) : CheckedDefinition :=
  ⟨"wrapper", .local, [], [], (wrapperBody reason).erase, wrapperBody reason,
    (wrapperBody reason).elaborate_erase⟩

example {I : PIR.Signature} (reason : PIR.Stop) :
    Evaluation.componentOperationOn model (.silent I)
      ([stopDefinition reason, wrapperDefinition reason].foldl
        (Evaluation.ComponentTablesOn.extend model (.silent I)) ⟨[], []⟩)
      (.invoke (wrapperDefinition reason).helper) Values.nil.present .nil = .halt reason := by
  rw [Evaluation.component_invoke_closed]
  rfl

-- Arbitrary observation replies remain in the process equation. False stops
-- after the reached mark; true returns the complete typed result.
private abbrev choiceInterface : PIR.Signature := ⟨Unit, fun _ => Bool⟩
private def choiceSites : SiteObservations choiceInterface where
  mark _ := .call () fun reply => if reply then .done () else .halt .exhausted
private def markedBody : Region dialect [] [.boolean] :=
  .letOp (.mark "choice") .nil .nil <|
  .letOp (.booleanConstant true) .nil .nil <| .ret (.cons .here .nil)
private def markedDefinition : CheckedDefinition :=
  ⟨"marked", .math, [], [.boolean], markedBody.erase, markedBody, markedBody.elaborate_erase⟩

example : invoke ([markedDefinition].foldl (Evaluation.ComponentTablesOn.extend model choiceSites)
      ⟨[], []⟩).components markedDefinition.helper Values.nil.present =
    .call () (fun reply => if reply then .done (.cons (some true) .nil) else .halt .exhausted) := by
  have adequate := Evaluation.ComponentTablesOn.adequate_fold model choiceSites ⟨[], []⟩
    (Evaluation.ComponentTablesOn.adequate_empty model) [markedDefinition] markedDefinition.helper .nil
  refine adequate.trans ?_
  change (PIR.Process.call (I := choiceInterface) () fun reply => _) = _
  congr 1
  funext reply
  cases reply <;> rfl

private def lengthBody : Region dialect [.vector "extension"] [.index] :=
  .letOp (.exec (.vectorLength "extension")) (.cons .here .nil) .nil <| .ret (.cons .here .nil)
private def lengthDefinition : CheckedDefinition :=
  ⟨"length", .local, [.vector "extension"], [.index], lengthBody.erase, lengthBody,
    lengthBody.elaborate_erase⟩

-- Exhaustion comes from the actual bounded primitive inside a Local helper.
example {I : PIR.Signature} (values : List (model.Field "extension"))
    (overbound : ¬ values.length < indexLimit) :
    Evaluation.componentOperationOn model (.silent I)
      ([lengthDefinition].foldl (Evaluation.ComponentTablesOn.extend model (.silent I)) ⟨[], []⟩)
      (.invoke lengthDefinition.helper) (Values.cons values .nil).present .nil = .halt .exhausted := by
  rw [Evaluation.component_invoke_closed]
  have stopped : invoke ([lengthDefinition].foldl
      (Evaluation.extendMeaningsOn model SiteObservations.closed) []) lengthDefinition.helper
      (.cons values .nil) = .halt .exhausted := by
    change (primitiveOutcome (if values.length < indexLimit then
      PIR.Outcome.returned (Values.cons values.length Values.nil : Values model.Value [.index])
      else .stopped .exhausted)).bind _ = _
    rw [ite_eq_right overbound]
    rfl
  rw [stopped]
  rfl

private def projectionBody : Region dialect [packets, .field "base"] [packets] :=
  .ret (.cons .here .nil)
private def projectionDefinition : CheckedDefinition :=
  ⟨"projection", .math, [packets, .field "base"], [packets], projectionBody.erase,
    projectionBody, projectionBody.elaborate_erase⟩

-- Kept Math helpers on present aggregate arguments use the closed meaning.
example {I : PIR.Signature} (value : model.Value packets) (unused : model.Field "base") :
    Evaluation.componentOperationOn model (.silent I)
      ([projectionDefinition].foldl (Evaluation.ComponentTablesOn.extend model (.silent I)) ⟨[], []⟩)
      (.invoke projectionDefinition.helper) (Values.cons value (.cons unused .nil)).present .nil =
      .done (.cons (some value) .nil) := by
  rw [Evaluation.component_invoke_closed]
  rfl

-- Optional Math dependency semantics really differ from strict closed calls.
-- The present-input premise is necessary, even when an operand is unused.
example {I : PIR.Signature} (value : model.Value packets) :
    Evaluation.componentOperationOn model (.silent I)
      ([projectionDefinition].foldl (Evaluation.ComponentTablesOn.extend model (.silent I)) ⟨[], []⟩)
      (.invoke projectionDefinition.helper) (.cons (some value) (.cons none .nil)) .nil =
      .done (.cons (some value) .nil) := rfl

section Forms
open NormalForm
variable {I : PIR.Signature} (actions : PIR.OperationInterpretation (Interface model) I)
  (context : ProtocolContext) (runs : Runs model I) (processes : CalleeProcesses model [] I)

private def noLaws : LawResults model [] := ⟨fun entry => entry.elim0⟩
private def readScope : Scope := [.value (.vector "extension"), .value .index]
private def readTerms : Terms [] readScope [.vector "extension", .index] :=
  .cons (.var .here) (.cons (.var (.there .here)) .nil)
private def readNext : Form [] [] (.results [.field "extension"] :: readScope) [.field "extension"] :=
  .done (.cons (.present (.result .here .here)) .nil)

-- The real normal-form compute node stops before binding its continuation.
example (tables : Tables model I) (values : List (model.Field "extension")) (index : Nat)
    (missing : values[index]? = none) :
    (Form.compute (.boundedAt "extension") rfl readTerms readNext).denoteOn model actions tables
      noLaws context runs processes (.cons values (.cons index .nil)) = .halt .refused := by
  have same := form_compute_closed model actions noLaws context runs processes tables
    (.boundedAt "extension") readTerms readNext (.cons values (.cons index .nil))
  refine same.trans ?_
  have arguments : Terms.eval noLaws readTerms (.cons values (.cons index .nil)) =
      .cons values (.cons index .nil) := rfl
  rw [arguments]
  simp only [closedCalculation, Calculation.op, calculationRegions, Evaluation.operationOn,
    missing, PIR.Process.interpret, PIR.Process.bind]

-- The actual normal-form strict call preserves every Local helper stop.
example (reason : PIR.Stop) :
    (Form.strict (stopDefinition reason).helper .nil (.done .nil) : Form [] [] [] []).denoteOn
      model actions ([stopDefinition reason].foldl
        (Evaluation.ComponentTablesOn.extend model (.silent I)) ⟨[], []⟩)
      noLaws context runs processes .nil = .halt reason := by
  have same := form_strict_closed model actions noLaws context runs processes
    [stopDefinition reason] (stopDefinition reason).helper .nil (.done .nil) .nil
  exact same.trans (by rfl)

-- A kept normal-form Math node needs presence, but needs no result law.
example :
    (Form.math markedDefinition.helper .nil (.done .nil) : Form [] [] [] []).denoteOn
      model actions ([markedDefinition].foldl
        (Evaluation.ComponentTablesOn.extend model (.silent I)) ⟨[], []⟩)
      noLaws context runs processes .nil = .done .nil := by
  have same := form_math_present_closed model actions noLaws context runs processes
    [markedDefinition] markedDefinition.helper .nil .nil (.done .nil) .nil rfl
  exact same.trans (by rfl)

end Forms

-- The calculation certificate has no source/target equality or Simulation premise.
noncomputable example (routing : Original.Routing) (state : Original.State model.toCarriers)
    (values : List (ZMod 5)) (index : Nat) :
    Original.Simulation
      (Original.HelperReturns Original.encodeHelperResult state
        [.data (.vector "extension" values), .data (.index index)])
      (fun _ frame => frame = [.data (.vector "extension" values), .data (.index index)])
      (Original.fold routing ((closedCalculation model (.boundedAt "extension")
        (.cons values (.cons index .nil))).interpret
          (closedLift (I := Occurrence.signature model.toCarriers))) state)
      (Domain.View.calculation model (.boundedAt "extension") [0, 1] [.data (.field "extension")]
        [.data (.vector "extension" values), .data (.index index)]) :=
  Original.Simulation.closedCalculationOn model routing (.boundedAt "extension")
    (.cons values (.cons index .nil)) rfl rfl state _ _ rfl

end Tests.ConnectionCalculations
