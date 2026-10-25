module

public import Zkc.Source.Structured.Linking
public import Zkc.Source.Structured.Import
public import Zkc.Source.RegionTotality

@[expose] public section

/-! Immediate return for the admitted region-free mathematical fragment.
The proof interprets the existing checked Region through the existing helper
closures. Structural admission and exact ABI linking are explicit evidence;
no operation annotation or name supplies an execution equation. -/
set_option autoImplicit false
namespace Zkc.Source.Structured
namespace Evaluation

variable {F G : Type} {interface : PIR.Signature}
variable [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]
variable (observations : SiteObservations interface)

/-- Every primitive of the preparation profile immediately returns. The invoke
case requires the complete helper signature and all of its ordered results. -/
theorem operation_total_of_preparation (table : Meanings F G interface)
    (profile : PreparationProfile) (op : Op)
    (allowed : op.preparationAllowed profile = true)
    (helpers : ∀ helper ∈ op.helpers, ∀ args, Returns (invoke table helper args)) :
    (meaning observations table).TotalOperation op := by
  intro args bodies _
  cases op with
  | fieldEmbed =>
    cases args with
    | cons value rest => cases rest; cases bodies; exact ⟨_, rfl⟩
  | indexConstant | fieldConstant | booleanConstant | groupIdentity =>
    cases args
    cases bodies
    exact ⟨_, rfl⟩
  | indexEqual | fieldAdd | fieldSubtract | fieldMultiply | fieldEqual | booleanAnd |
      booleanOr | booleanXor | booleanEqual | booleanNotEqual | groupAdd | groupScale |
      groupEqual =>
    cases args with
    | cons a rest => cases rest with
      | cons b rest => cases rest; cases bodies; exact ⟨_, rfl⟩
  | select =>
    cases args with
    | cons condition rest => cases rest with
      | cons yes rest => cases rest with
        | cons no rest => cases rest; cases bodies; exact ⟨_, rfl⟩
  | makeProduct => cases bodies; exact ⟨_, rfl⟩
  | getProduct =>
    cases args with
    | cons value rest => cases rest; cases bodies; exact ⟨_, rfl⟩
  | invoke helper =>
    cases bodies
    exact helpers helper (by simp only [Op.helpers, List.mem_singleton]) args
  | exec | boundedAt | fold | map | branch | loop | loopCondition | guard | mark =>
    simp only [Op.preparationAllowed, Bool.false_eq_true] at allowed

private theorem regions_total_of_empty (table : Meanings F G interface) :
    {signatures : List (List Ty × List Ty)} → (bodies : Regions dialect signatures) →
    bodies.erase = .nil → bodies.Total (meaning observations table)
  | _, .nil, _ => trivial
  | _, .cons _ _, impossible => by cases impossible

/-- Raw-profile evidence transports through exact erasure to structural totality
of the one typed carrier. No callback, stop, finite loop or bounded read enters. -/
theorem region_total_of_preparation (table : Meanings F G interface)
    (profile : PreparationProfile) {Γ out : List Ty} (region : Region dialect Γ out)
    (allowed : region.erase.preparationAllowed profile = true)
    (helpers : ∀ helper ∈ region.erase.operations.flatMap Op.helpers,
      ∀ args, Returns (invoke table helper args)) :
    region.Total (meaning observations table) := by
  refine Region.rec (dialect := dialect)
    (motive_1 := fun _ _ region => region.erase.preparationAllowed profile = true →
      (∀ helper ∈ region.erase.operations.flatMap Op.helpers,
        ∀ args, Returns (invoke table helper args)) →
      region.Total (meaning observations table))
    (motive_2 := fun _ _ => True) ?_ ?_ ?_ ?_ ?_ ?_ region allowed helpers
  · intro Γ out values _ _
    trivial
  · intro Γ out reason allowed _
    simp only [Region.erase, RawRegion.preparationAllowed, Bool.false_eq_true] at allowed
  · intro Γ out op args bodies next _ nextIH allowed helpers
    have parts : op.preparationAllowed profile = true ∧
        bodies.erase = .nil ∧ next.erase.preparationAllowed profile = true := by
      cases erased : bodies.erase with
      | nil =>
        simp only [Region.erase, erased, RawRegion.preparationAllowed,
          Bool.and_eq_true] at allowed
        exact ⟨allowed.1.1, rfl, allowed.2⟩
      | cons =>
        simp only [Region.erase, erased, RawRegion.preparationAllowed,
          Bool.false_eq_true] at allowed
    have bodiesTotal : bodies.Total (meaning observations table) :=
      regions_total_of_empty observations table bodies parts.2.1
    refine ⟨operation_total_of_preparation observations table profile op parts.1 ?_,
      bodiesTotal, nextIH parts.2.2 ?_⟩
    · intro helper used args
      exact helpers helper (by
        simp only [Region.erase, RawRegion.operations, parts.2.1, RawRegions.operations,
          List.nil_append, List.flatMap_cons, List.mem_append]
        exact Or.inl used) args
    · intro helper used args
      exact helpers helper (by
        simp only [Region.erase, RawRegion.operations, parts.2.1, RawRegions.operations,
          List.nil_append, List.flatMap_cons, List.mem_append]
        exact Or.inr used) args
  · intro Γ mid out body next _ _ allowed _
    simp only [Region.erase, RawRegion.preparationAllowed, Bool.false_eq_true] at allowed
  · trivial
  · intros
    trivial

/-- Actual semantic totality, including vector projections and empty result tuples. -/
theorem region_returns_of_preparation (table : Meanings F G interface)
    (profile : PreparationProfile) {Γ out : List Ty} (region : Region dialect Γ out)
    (allowed : region.erase.preparationAllowed profile = true)
    (helpers : ∀ helper ∈ region.erase.operations.flatMap Op.helpers,
      ∀ args, Returns (invoke table helper args))
    (env : Environment (assignment F G) Γ) :
    Returns (region.denote (meaning observations table) env) :=
  region.returns_of_total (meaning observations table)
    (region_total_of_preparation observations table profile region allowed helpers) env

/-- Prefix induction proves closure return without a semantic premise on any
callee. Nonselected declarations may contain arbitrary Local control. -/
private theorem fold_returns_selected (profile : PreparationProfile) (selected : List Helper)
    (definitions : List CheckedDefinition) (available : List Helper)
    (table : Meanings F G interface)
    (linked : DeclarationsLinked available definitions)
    (structural : ∀ definition ∈ definitions, definition.helper ∈ selected →
      definition.raw.preparationAllowed profile = true ∧
      ∀ helper ∈ definition.helpers, helper ∈ selected)
    (returned : ∀ helper ∈ available, helper ∈ selected →
      ∀ args, Returns (invoke table helper args)) :
    ∀ helper ∈ definitions.map CheckedDefinition.helper ++ available,
      helper ∈ selected → ∀ args,
      Returns (invoke (definitions.foldl (extendMeanings observations) table) helper args) := by
  induction definitions generalizing available table with
  | nil => exact returned
  | cons definition rest ih =>
    have extended : ∀ helper ∈ definition.helper :: available, helper ∈ selected →
        ∀ args, Returns (invoke (extendMeanings observations table definition) helper args) := by
      intro helper present selectedHelper args
      rcases List.mem_cons.mp present with same | present
      · subst helper
        rw [invoke_extended observations table definition args]
        have body := structural definition List.mem_cons_self selectedHelper
        apply region_returns_of_preparation observations table profile definition.body
        · simpa only [definition.exactBody] using body.1
        · intro helper used values
          have usedRaw : helper ∈ definition.helpers := by
            simpa only [definition.helpers_eq_body] using used
          exact returned helper (linked.2.1 helper usedRaw) (body.2 helper usedRaw) values
      · have different : definition.name ≠ helper.name := by
          intro same
          exact linked.1 (List.mem_map.mpr ⟨helper, present, same.symm⟩)
        rw [invoke_extend_other observations table definition helper different]
        exact returned helper present selectedHelper args
    intro helper present selectedHelper args
    apply ih (definition.helper :: available) (extendMeanings observations table definition)
      linked.2.2 (fun d member => structural d (List.mem_cons_of_mem _ member))
      extended helper ?_ selectedHelper args
    simp only [List.map_cons, List.mem_append, List.mem_cons] at present ⊢
    rcases present with (same | member) | member
    · exact Or.inr (Or.inl same)
    · exact Or.inl member
    · exact Or.inr (Or.inr member)

/-- Checked full-ABI closure plus structural admission proves immediate return
for every selected helper, including zero/multiple results and vector ports. -/
theorem preparation_closed_returns (profile : PreparationProfile)
    (definitions : List CheckedDefinition) (linked : DeclarationsLinked [] definitions)
    (selected : List Helper) (closed : PreparationClosed profile definitions selected)
    (helper : Helper) (member : helper ∈ selected)
    (args : Values (assignment F G) helper.inputs) :
    Returns (invoke (definitions.foldl (extendMeanings observations) []) helper args) := by
  apply fold_returns_selected observations profile selected definitions [] [] linked
    (fun definition present chosen => (closed.2 definition present chosen).2)
    (by intro helper impossible; cases impossible) helper
  · simpa only [List.append_nil] using closed.1 helper member
  · exact member

/-- Admission retains the checked closure certificate; callers provide only
membership of the exact Math signature, never a semantic totality premise. -/
theorem admitted_realization_helper_returns (payload : UnitPayload)
    (helper : Helper) (member : helper ∈ preparationHelpers .realization payload.definitions)
    (args : Values (assignment F G) helper.inputs) :
    Returns (invoke (payload.definitions.foldl (extendMeanings observations) []) helper args) :=
  preparation_closed_returns observations .realization payload.definitions payload.linked
    _ payload.realizationClosed helper member args

/-- The stricter scalar map closure is total under the same interpreter. -/
theorem admitted_map_helper_returns (payload : UnitPayload)
    (helper : Helper) (member : helper ∈ preparationHelpers .map payload.definitions)
    (args : Values (assignment F G) helper.inputs) :
    Returns (invoke (payload.definitions.foldl (extendMeanings observations) []) helper args) :=
  preparation_closed_returns observations .map payload.definitions payload.linked
    _ payload.mapClosed helper member args

private theorem region_total_of_invoke_return (table : Meanings F G interface)
    (helper : Helper) (returned : ∀ args, Returns (invoke table helper args))
    {Γ out : List Ty} (region : Region dialect Γ out) (operands results : List Nat)
    (derived : region.erase =
      .letOp (Op.invoke helper) operands helper.outputs .nil (.ret results)) :
    region.Total (meaning observations table) := by
  refine Region.rec (dialect := dialect)
    (motive_1 := fun _ _ region => region.erase =
      .letOp (Op.invoke helper) operands helper.outputs .nil (.ret results) →
      region.Total (meaning observations table))
    (motive_2 := fun _ _ => True) ?_ ?_ ?_ ?_ ?_ ?_ region derived
  · intro Γ out values impossible
    cases impossible
  · intro Γ out reason impossible
    cases impossible
  · intro Γ out op arguments bodies next _ _ exactRaw
    obtain ⟨sameOp, _, _, sameBodies, sameNext⟩ := RawRegion.letOp.inj exactRaw
    subst op
    refine ⟨?_, regions_total_of_empty observations table bodies sameBodies, ?_⟩
    · intro args callbacks _
      cases callbacks
      exact returned args
    · apply region_total_of_preparation observations table .realization next
      · rw [sameNext]
        rfl
      · intro dependency used
        simp only [sameNext, RawRegion.operations, List.flatMap_nil, List.not_mem_nil] at used
  · intro Γ mid out body next _ _ impossible
    cases impossible
  · trivial
  · intros
    trivial

/-- A retained realization's checked raw derivation invokes exactly its selected
Math closure. All inputs and all zero/multiple results retain their declared ABI.
The only membership premise is structural; callee return is proved above. -/
theorem admitted_realization_returns (program : Program) (domains : List DomainSpec)
    (summaries : IdentitySummaries) (declaration : RealizationDeclaration)
    (definition : CheckedDefinition)
    (checked : checkDefinition program.snapshot domains summaries (.realization declaration) =
      .ok definition)
    (selected : declaration.helperSpec ∈
      preparationHelpers .realization program.payload.definitions)
    (args : Values (assignment F G) definition.inputs) :
    Returns (definition.body.denote
      (meaning observations (program.payload.definitions.foldl (extendMeanings observations) []))
      args.get) := by
  apply definition.body.returns_of_total
  apply region_total_of_invoke_return observations _ declaration.helperSpec
    (admitted_realization_helper_returns observations program.payload declaration.helperSpec selected)
    definition.body (List.range declaration.inputs.length) (List.range declaration.outputs.length)
  rw [definition.exactBody, checkDefinition_realization_raw checked]
  rfl

private theorem unit_invoke_body (payload : UnitPayload) (definition : CheckedDefinition)
    (member : definition ∈ payload.definitions)
    (args : Values (assignment F G) definition.inputs) :
    invoke (payload.definitions.foldl (extendMeanings observations) []) definition.helper args =
      definition.body.denote
        (meaning observations (payload.definitions.foldl (extendMeanings observations) []))
        args.get := by
  obtain ⟨before, after, split⟩ := List.mem_iff_append.mp member
  have linked := payload.linked
  rw [split] at linked
  have tail := (DeclarationsLinked.append [] before (definition :: after)).mp linked |>.2
  have later : ∀ other ∈ after, other.name ≠ definition.helper.name := by
    intro other present
    exact tail.2.2.fresh List.mem_cons_self present
  have closure : invoke (payload.definitions.foldl (extendMeanings observations) [])
      definition.helper args = definition.body.denote
        (meaning observations (before.foldl (extendMeanings observations) [])) args.get := by
    simp only [split, List.foldl_append, List.foldl_cons]
    rw [invoke_foldl_other observations _ after definition.helper later]
    exact invoke_extended observations _ definition args
  rw [closure]
  refine congrFun (region_denote_table_congr observations
    (before.foldl (extendMeanings observations) [])
    (payload.definitions.foldl (extendMeanings observations) []) definition.body ?_) args.get
  intro helper used
  have available : helper ∈ before.reverse.map CheckedDefinition.helper ++ [] :=
    tail.2.1 helper (by simpa only [definition.helpers_eq_body] using used)
  have stable : ∀ other ∈ definition :: after, other.name ≠ helper.name := by
    intro other present
    exact tail.fresh available present
  simp only [split, List.foldl_append]
  exact (invoke_foldl_other observations _ (definition :: after) helper stable).symm

/-- Immediate return of an actual retained realization whose exact Math root
belongs to the narrow total fragment. General finite-computation admission is
insufficient: its reached domain checks may stop. The selected-fragment premise
is structural; no caller supplies a semantic callee-return assumption. -/
theorem imported_immediate_realization_returns {snapshot : Snapshot} (imported : Imported snapshot)
    (declaration : RealizationDeclaration)
    (_declared : Definition.realization declaration ∈ snapshot.definitions)
    (definition : CheckedDefinition) (member : definition ∈ imported.program.payload.definitions)
    (derived : definition.raw = declaration.raw)
    (selected : declaration.helperSpec ∈
      preparationHelpers .realization imported.program.payload.definitions)
    (args : Values (assignment F G) definition.inputs) :
    Returns (invoke
      (imported.program.payload.definitions.foldl (extendMeanings observations) [])
      definition.helper args) := by
  rw [unit_invoke_body observations imported.program.payload definition member args]
  apply definition.body.returns_of_total
  apply region_total_of_invoke_return observations _ declaration.helperSpec
    (admitted_realization_helper_returns observations imported.program.payload declaration.helperSpec
      selected)
    definition.body (List.range declaration.inputs.length) (List.range declaration.outputs.length)
  rw [definition.exactBody, derived]
  rfl

end Evaluation
end Zkc.Source.Structured
