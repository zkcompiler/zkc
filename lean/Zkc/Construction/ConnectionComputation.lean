module

public import Zkc.Construction.ConnectionCalculations
public import Zkc.Construction.ConnectionFrame

@[expose] public section

/-! Static component readback and layout extension for nominal calculations.
The result terms are exactly the existing normalizer's `calculation`, including
its constant folding, or the actual result/tuple binders after a successful
partial calculation or retained helper call. No evaluator is introduced here. -/
set_option autoImplicit false
namespace Zkc.Construction.ConnectionComputation
open Zkc.Source Zkc.Source.Structured NormalForm ConnectionFrame

/-- Project the tuple spine without inspecting the term in its head. -/
def firstTerm {scope : Scope} {ty : Ty} {types : List Ty}
    (terms : Terms [] scope (ty :: types)) : Term [] scope ty :=
  Terms.casesOn (motive_2 := fun index _ => match index with
    | [] => PUnit | head :: _ => Term [] scope head) terms
    PUnit.unit fun head _ => head

/-- Drop the tuple head without evaluating it. -/
def laterTerms {scope : Scope} {ty : Ty} {types : List Ty}
    (terms : Terms [] scope (ty :: types)) : Terms [] scope types :=
  Terms.casesOn (motive_2 := fun index _ => match index with
    | [] => PUnit | _ :: tail => Terms [] scope tail) terms
    PUnit.unit fun _ tail => tail

/-- Recursion follows the type-list spine. Operand inference therefore does
not need to evaluate unknown term heads or dependent pattern-match casts. -/
def components {scope : Scope} : {types : List Ty} → Terms [] scope types → Values (Comp [] scope) types
  | [], _ => .nil
  | _ :: _, terms => .cons (.present (firstTerm terms)) (components (laterTerms terms))
termination_by structural types => types

theorem components_eval {model : DomainModel} {scope : Scope} (binders : Binders model scope) :
    {types : List Ty} → (terms : Terms [] scope types) →
    Comps.eval (LawResults.empty model) (components terms) binders =
      (Terms.eval (LawResults.empty model) terms binders).present
  | _, .nil => rfl
  | _, .cons head tail => by
    simp only [components, firstTerm, laterTerms, Comps.eval, Comp.eval, Terms.eval,
      Values.present, components_eval binders tail]

def cells {scope : Scope} : {types : List Ty} → Values (Comp [] scope) types → Layout scope
  | _, .nil => []
  | _, .cons head tail => .data head :: cells tail

theorem cells_encoded {model : DomainModel} {scope : Scope} (binders : Binders model scope)
    (history : Domain.History model.toCarriers) {types : List Ty}
    (values : Values (Comp [] scope) types) (actual : Values model.Value types)
    (present : Comps.eval (LawResults.empty model) values binders = actual.present)
    {encoded : Domain.Environment model.toCarriers} (encoding : Domain.encodeValues actual = some encoded) :
    Holds model binders history (cells values) encoded := by
  induction values generalizing encoded with
  | nil =>
    cases actual
    simp only [Domain.encodeValues, Option.some.injEq] at encoding
    subst encoded
    exact .nil
  | cons head tail ih =>
    cases actual with
    | cons value rest =>
      have headEq : head.eval (LawResults.empty model) binders = some value :=
        congrArg firstEntry present
      have tailEq : Comps.eval (LawResults.empty model) tail binders = rest.present :=
        congrArg laterEntries present
      cases first : Domain.Value.encode _ value with
      | none => simp [Domain.encodeValues, first] at encoding
      | some physical =>
        cases remaining : Domain.encodeValues rest with
        | none => simp [Domain.encodeValues, first, remaining] at encoding
        | some physicals =>
          simp only [Domain.encodeValues, first, remaining, bind, Option.bind,
            Option.pure_def, Option.some.injEq] at encoding
          subst encoded
          exact .cons ⟨value, headEq, first⟩ (ih rest tailEq remaining)

private theorem read_values {carriers : Carriers} {types : List Ty}
    (values : Values carriers.Value types) (references : List Nat)
    (environment : Domain.Environment carriers)
    (related : Original.ValuesHolds environment (references.map Original.Location.data) values.present) :
    Domain.read environment references = Domain.encodeValues values := by
  induction values generalizing references with
  | nil => cases references with
    | nil => rfl
    | cons => exact False.elim related
  | cons value tail ih =>
    cases references with
    | nil => exact False.elim related
    | cons reference references =>
      obtain ⟨⟨actual, same, decoded⟩, rest⟩ := related
      have sameValue : value = actual := Option.some.inj same
      subst actual
      cases physical : environment[reference]? with
      | none => simp [physical] at decoded
      | some encoded =>
        have encodedValue := Domain.Value.encode_decode (by simpa [physical] using decoded)
        simp only [Domain.read, List.mapM_cons, physical, Domain.encodeValues,
          encodedValue, bind, Option.bind]
        have tailRead := ih references rest
        change references.mapM (fun reference => environment[reference]?) = Domain.encodeValues tail at tailRead
        rw [tailRead]

private theorem values_present {carriers : Carriers} {types : List Ty}
    (values : Values (Component carriers.Value) types) (references : List Nat)
    {environment : Domain.Environment carriers}
    (related : Original.ValuesHolds environment (references.map Original.Location.data) values) :
    ∃ actual : Values carriers.Value types, values = actual.present := by
  induction values generalizing references with
  | nil => exact ⟨.nil, rfl⟩
  | cons head tail ih =>
    cases references with
    | nil => exact False.elim related
    | cons reference references =>
      obtain ⟨⟨value, present, _⟩, rest⟩ := related
      obtain ⟨values, same⟩ := ih references rest
      exact ⟨.cons value values, by cases present; cases same; rfl⟩

/-- Physical readback supplies presence for arbitrary components, including
optional inputs and tuple projections. No proposal can assume presence. -/
theorem read_components {model : DomainModel} {scope : Scope} {types : List Ty}
    {layout : Layout scope} {values : Values (Comp [] scope) types} {references : List Nat}
    (checked : Readback layout values (references.map Original.Location.data))
    (binders : Binders model scope) {history : Domain.History model.toCarriers}
    {environment : Domain.Environment model.toCarriers}
    (related : Holds model binders history layout environment) :
    ∃ actual : Values model.Value types,
      Comps.eval (LawResults.empty model) values binders = actual.present ∧
      Domain.read environment references = Domain.encodeValues actual := by
  have read := checked.sound related
  obtain ⟨actual, same⟩ := values_present _ references read
  exact ⟨actual, same, read_values actual references environment (by simpa only [same] using read)⟩

/-- The checked ordered operand tuple yields exact nominal readback. -/
theorem read_terms {model : DomainModel} {scope : Scope} {types : List Ty}
    {layout : Layout scope} {terms : Terms [] scope types} {references : List Nat}
    (checked : Readback layout (components terms) (references.map Original.Location.data))
    (binders : Binders model scope) {history : Domain.History model.toCarriers}
    {environment : Domain.Environment model.toCarriers}
    (related : Holds model binders history layout environment) :
    Domain.read environment references = Domain.encodeValues (Terms.eval (LawResults.empty model) terms binders) :=
  read_values _ references environment (by simpa only [components_eval] using checked.sound related)

/-- A target-only calculation extends the symbolic frame without consuming a
source form. Its results use the very same constant-folded source terms. -/
theorem calculation_frame (model : DomainModel) {scope : Scope}
    (calculation : Calculation) (total : calculation.op.total = true)
    (terms : Terms [] scope calculation.op.arguments)
    (outputData : calculation.op.results.all Domain.dataType = true)
    (binders : Binders model scope) {history : Domain.History model.toCarriers}
    {layout : Layout scope} {environment : Domain.Environment model.toCarriers}
    (related : Holds model binders history layout environment) :
    Holds model binders history
      (layout ++ cells (NormalForm.calculation calculation.op total terms))
      (environment ++ Original.encodeHelperResult
        (calculation.op.evalTotal model total (Terms.eval (LawResults.empty model) terms binders))) :=
  related.append (cells_encoded binders history _ _
    (calculation_eval (LawResults.empty model) binders calculation.op total terms)
    (Original.encodeHelperResult_eq outputData _))

/-- Only a successful computation binds these actual result positions. -/
def resultComponents {scope : Scope} (types : List Ty) : Values (Comp [] (.results types :: scope)) types :=
  mapValues (fun position => .present (.result .here position)) (Operands.identity types)

def resultsLayout {scope : Scope} (layout : Layout scope) (types : List Ty) : Layout (.results types :: scope) :=
  layout.map (Cell.rename .there) ++ cells (resultComponents types)

def tupleLayout {scope : Scope} (layout : Layout scope) (types : List Ty) : Layout (.tuple types :: scope) :=
  layout.map (Cell.rename .there) ++ cells (readComps types)

theorem results_frame (model : DomainModel) {scope : Scope} {types : List Ty}
    (outputData : types.all Domain.dataType = true) (values : Values model.Value types)
    (binders : Binders model scope) {history : Domain.History model.toCarriers}
    {layout : Layout scope} {environment : Domain.Environment model.toCarriers}
    (related : Holds model binders history layout environment) :
    Holds model (.cons values binders) history (resultsLayout layout types)
      (environment ++ Original.encodeHelperResult values) :=
  (related.rename .there (fun _ => rfl)).append (cells_encoded _ history _ values
    (comps_eval_positions (LawResults.empty model) (.cons values binders)
      (fun position => .result .here position) values (fun _ => rfl))
    (Original.encodeHelperResult_eq outputData values))

theorem tuple_frame (model : DomainModel) {scope : Scope} {types : List Ty}
    (outputData : types.all Domain.dataType = true) (values : Values model.Value types)
    (binders : Binders model scope) {history : Domain.History model.toCarriers}
    {layout : Layout scope} {environment : Domain.Environment model.toCarriers}
    (related : Holds model binders history layout environment) :
    Holds model (.cons values.present binders) history (tupleLayout layout types)
      (environment ++ Original.encodeHelperResult values) :=
  (related.rename .there (fun _ => rfl)).append (cells_encoded _ history _ values
    (comps_eval_reads (LawResults.empty model) binders values.present)
    (Original.encodeHelperResult_eq outputData values))

end Zkc.Construction.ConnectionComputation
