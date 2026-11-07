module

public import Zkc.Realization.RecordAllocator

@[expose] public section

/-! Typed field projection from an immutable nominal record. Selection order
comes from the actual calculations; source authors supply no field-routing proof.
The complete caller frame is retained at every administrative checkpoint. -/
set_option autoImplicit false
namespace Zkc.Realization.RecordProjection
open Zkc.Source Zkc.Source.Structured Zkc.Construction

structure Layout where
  identity : String
  constructor : String
  fields : ProductFields

def Layout.type (layout : Layout) : Ty :=
  .product layout.identity layout.constructor layout.fields

structure Selection (fields : ProductFields) where
  type : Ty
  field : Var fields.toList type

def Selection.calculation {layout : Layout} (selection : Selection layout.fields) : Calculation :=
  .getProduct layout.identity layout.constructor layout.fields selection.type selection.field

def instructions (layout : Layout) (record : Nat) (selections : List (Selection layout.fields)) :
    List Construction.Instruction :=
  selections.map fun selected ↦
    ⟨.calculate selected.calculation, [record], [.data selected.type], []⟩

structure Recognized (body : List Construction.Instruction) where
  layout : Layout
  reference : Nat
  selections : List (Selection layout.fields)
  exactBody : body = instructions layout reference selections

def Selection.fromInstruction (layout : Layout) (instruction : Construction.Instruction) :
    Option (Selection layout.fields) := do
  let .calculate (.getProduct _ _ fields type field) := instruction.operation | none
  if same : fields = layout.fields then some ⟨type, same ▸ field⟩ else none

/-- Finite recognition retains the declared nominal identity, each selected
field, the common record reference and the complete instruction spelling. -/
def recognize (body : List Construction.Instruction) : Option (Recognized body) := do
  let first :: _ := body | none
  let .calculate (.getProduct identity constructor fields _ _) := first.operation | none
  let [reference] := first.operands | none
  let layout : Layout := ⟨identity, constructor, fields⟩
  let selections ← body.mapM (Selection.fromInstruction layout)
  if exactBody : body = instructions layout reference selections then
    some ⟨layout, reference, selections, exactBody⟩
  else none

def spine (layout : Layout) (record : Nat) :
    List (Selection layout.fields) → ConnectionTargetPrefix.Prefix
  | [] => .empty
  | selected :: rest =>
      .step (fun model ↦ Domain.View.calculation model selected.calculation
        [record] [.data selected.type]) (spine layout record rest)

theorem correspondence (model : DomainModel) (program : Program) (context : Context)
    (layout : Layout) (record : Nat) (selections : List (Selection layout.fields)) :
    Domain.Correspondence.Block (model := model) (program := program) (context := context)
      (instructions layout record selections) ((spine layout record selections).block model) := by
  induction selections with
  | nil => exact Domain.Correspondence.empty
  | cons selected rest ih =>
      exact Domain.Correspondence.sequence (Domain.Correspondence.calculation _ _ _) ih

def results (model : DomainModel) (layout : Layout) (record : model.Value layout.type)
    (selections : List (Selection layout.fields)) : Domain.Environment model.toCarriers :=
  selections.flatMap fun selected ↦ Original.encodeHelperResult
    (.cons ((layout.fields.unpack record).get selected.field) .nil)

theorem results_length (model : DomainModel) (layout : Layout) (record : model.Value layout.type)
    (selections : List (Selection layout.fields))
    (localFields : ∀ selection ∈ selections, Domain.localType selection.type = true) :
    (results model layout record selections).length = selections.length := by
  induction selections with
  | nil => rfl
  | cons selected rest ih =>
      have fieldLocal := localFields selected (by simp)
      have length := congrArg List.length (Domain.encodeValues_sorts
        (Original.encodeHelperResult_eq (by simpa using fieldLocal)
          (.cons ((layout.fields.unpack record).get selected.field) .nil)))
      simp only [List.length_map, List.length_cons, List.length_nil] at length
      have tail := ih (fun selection present ↦ localFields selection (by simp [present]))
      simp only [results, List.flatMap_cons, List.length_append, List.length_cons, length] at *
      omega

/-- One selected local field occupies one SSA result, with the value read by
the typed product projection. Handle-like values cannot satisfy this rule. -/
theorem result_single (model : DomainModel) (layout : Layout)
    (record : model.Value layout.type) (selected : Selection layout.fields)
    (data : selected.type.isHandle = false) :
    Original.encodeHelperResult (.cons ((layout.fields.unpack record).get selected.field) .nil) =
      [Domain.Value.data ⟨selected.type, data, (layout.fields.unpack record).get selected.field⟩] := by
  have encoded : Domain.Value.encode selected.type
      ((layout.fields.unpack record).get selected.field) =
      some (Domain.Value.data (carriers := model.toCarriers)
        ⟨selected.type, data, (layout.fields.unpack record).get selected.field⟩) :=
    Domain.Value.encode_ofPayload
    (by simp [Domain.Payload.ofValue, data])
  simp [Original.encodeHelperResult, Domain.encodeValues_cons, Domain.encodeValues_nil, encoded]

/-- The generated output position selects the actual ordered field. Both its
type and its field variable are retained; equal field types do not suffice. -/
theorem results_get (model : DomainModel) (layout : Layout) (record : model.Value layout.type)
    (selections : List (Selection layout.fields))
    (localFields : ∀ selection ∈ selections, Domain.localType selection.type = true)
    (index : Nat) (selected : Selection layout.fields)
    (found : selections[index]? = some selected) (data : selected.type.isHandle = false) :
    (results model layout record selections)[index]? =
      some (.data ⟨selected.type, data, (layout.fields.unpack record).get selected.field⟩) := by
  induction selections generalizing index with
  | nil => simp at found
  | cons first rest ih =>
      have firstLocal := localFields first (by simp)
      simp only [results, List.flatMap_cons]
      cases index with
      | zero =>
          cases Option.some.inj found
          rw [result_single model layout record selected data]
          rfl
      | succ index =>
          obtain ⟨firstValue, encoded⟩ := Domain.Value.encode_local_exists firstLocal
            ((layout.fields.unpack record).get first.field)
          have firstResult : Original.encodeHelperResult
              (.cons ((layout.fields.unpack record).get first.field) .nil) = [firstValue] := by
            simp [Original.encodeHelperResult, Domain.encodeValues_cons,
              Domain.encodeValues_nil, encoded]
          rw [firstResult]
          change (results model layout record rest)[index]? = _
          exact ih (fun selection present ↦ localFields selection (by simp [present])) index found

set_option backward.isDefEq.respectTransparency false in
/-- The existing typed calculation determines each result. This rule is valid
for arbitrary selection order, repeated fields and additional caller values. -/
theorem simulation (model : DomainModel) (layout : Layout)
    (data : layout.type.isHandle = false) (selections : List (Selection layout.fields))
    (localFields : ∀ selection ∈ selections, Domain.localType selection.type = true)
    (environment captured : Domain.Environment model.toCarriers)
    (preserved : captured <+: environment) (reference : Nat) (record : model.Value layout.type)
    (readRecord : environment[reference]? = some (.data ⟨layout.type, data, record⟩)) :
    Nonempty (Original.Simulation Eq (fun _ frame ↦ captured <+: frame)
      (.done (environment ++ results model layout record selections))
      ((spine layout reference selections).block model environment)) := by
  induction selections generalizing environment with
  | nil => exact ⟨by simpa [results, spine, ConnectionTargetPrefix.Prefix.block,
      ConnectionTargetPrefix.Prefix.plug, Domain.View.empty] using
        (Original.Simulation.done (returns := Eq) (live := fun _ frame ↦ captured <+: frame)
          (a := environment) rfl)⟩
  | cons selected rest ih =>
      let value := (layout.fields.unpack record).get selected.field
      let encoded := Original.encodeHelperResult (tys := [selected.type]) (.cons value .nil)
      have encodedRecord : Domain.Value.encode layout.type record =
          some (.data ⟨layout.type, data, record⟩) :=
        Domain.Value.encode_ofPayload (by simp [Domain.Payload.ofValue, data])
      have read : Domain.read environment [reference] =
          Domain.encodeValues (tys := [layout.type]) (.cons record .nil) := by
        simp [Domain.read, readRecord, Domain.encodeValues_cons, Domain.encodeValues_nil,
          encodedRecord]
      have inputLocal : Domain.localType layout.type = true := by
        simp [Domain.localType, Domain.dataType, data]
      have outputLocal := localFields selected (by simp)
      have step : Domain.View.calculation model selected.calculation [reference]
          [.data selected.type] environment = .done (environment ++ encoded) := by
        have law := ConnectionCalculations.view_calculation model selected.calculation
          (.cons record .nil)
          (by simpa [Selection.calculation, Calculation.op, Op.arguments, Layout.type]
            using inputLocal)
          (by simpa [Selection.calculation, Calculation.op, Op.results] using outputLocal)
          environment [reference] read
        simpa [Selection.calculation, ConnectionCalculations.closedCalculation,
          ConnectionCalculations.calculationRegions, Calculation.op, Op.results,
          Evaluation.operationOn, PIR.Process.interpret, PIR.Process.bind, value, encoded]
          using law
      obtain ⟨tail⟩ := ih (fun selection present ↦ localFields selection (by simp [present]))
        (environment ++ encoded) (preserved.trans (List.prefix_append _ _))
        (Original.read_append readRecord encoded)
      refine ⟨?_⟩
      change Original.Simulation _ _ _ (Domain.View.sequence _ _ environment)
      apply RecordAllocator.silent_sequence step preserved
        (preserved.trans (List.prefix_append _ _))
      simpa [results, List.append_assoc, encoded, value, ConnectionTargetPrefix.Prefix.block]
        using tail

theorem Recognized.simulation {body : List Construction.Instruction} (checked : Recognized body)
    (model : DomainModel) (program : Program) (context : Context)
    (data : checked.layout.type.isHandle = false)
    (localFields : ∀ selection ∈ checked.selections, Domain.localType selection.type = true)
    (environment captured : Domain.Environment model.toCarriers)
    (preserved : captured <+: environment) (record : model.Value checked.layout.type)
    (readRecord : environment[checked.reference]? =
      some (.data ⟨checked.layout.type, data, record⟩)) :
    Nonempty (Original.Simulation Eq (fun _ frame ↦ captured <+: frame)
      (.done (environment ++ results model checked.layout record checked.selections))
      (Domain.evaluate model program context body environment)) := by
  rcases checked with ⟨layout, reference, selections, rfl⟩
  rw [correspondence]
  exact RecordProjection.simulation model layout data selections localFields
    environment captured preserved reference record readRecord

end Zkc.Realization.RecordProjection
