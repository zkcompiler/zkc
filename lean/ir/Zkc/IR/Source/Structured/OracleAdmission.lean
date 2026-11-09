module

public import Zkc.IR.Source.Structured.OracleBody
public import Zkc.IR.Source.Structured.Checked

@[expose] public section

/-! Executable construction of the source-associated Oracle Math environment. Every stored
Math body is lowered and formed from the retained source. Names only select that source;
no checked body or replacement denotation is accepted as input. -/

set_option autoImplicit false
namespace Zkc.Source.Structured

structure OracleMathSource (snapshot : Snapshot) (domains : List DomainSpec) where
  function : Function
  member : .function function ∈ snapshot.definitions
  kind : function.kind = .math
  checked : CheckedDefinition
  signature : checked.helper = ⟨function.name, .math, function.inputs, function.outputs⟩
  lowered : (lowerBlock snapshot domains [] .math Limits.nesting function.inputs
    (function.preconditions.map (fun bound ↦ (bound.index, bound.container)))
    .function function.body).run' {} = .ok checked.raw

def checkOracleMathSource (snapshot : Snapshot) (domains : List DomainSpec) (name : String) :
    Except String (OracleMathSource snapshot domains) := do
  match found : snapshot.definitions.find? (·.name == name) with
  | some (.function function) =>
    if kind : function.kind = .math then
      match lowered : (lowerBlock snapshot domains [] .math Limits.nesting function.inputs
          (function.preconditions.map (fun bound ↦ (bound.index, bound.container)))
          .function function.body).run' {} with
      | .error error => throw error
      | .ok raw =>
        match formed : raw.elaborate (dialect := dialect) function.inputs function.outputs with
        | .error _ => throw "oracle-math-formation"
        | .ok body =>
          return ⟨function, List.mem_of_find?_eq_some found, kind,
            ⟨function.name, .math, function.inputs, function.outputs, raw, body, formed⟩,
            rfl, lowered⟩
    else throw "oracle-math-kind"
  | _ => throw "oracle-math-source"

def Snapshot.mathFunctions (snapshot : Snapshot) : List Function :=
  snapshot.definitions.filterMap fun definition ↦ match definition with
    | .function function => if function.kind == .math then some function else none
    | _ => none

theorem Snapshot.mem_mathFunctions {snapshot : Snapshot} {function : Function} :
    function ∈ snapshot.mathFunctions ↔
      .function function ∈ snapshot.definitions ∧ function.kind = .math := by
  simp only [Snapshot.mathFunctions, List.mem_filterMap]
  constructor
  · rintro ⟨definition, member, selected⟩
    cases definition with
    | function original =>
      change (if original.kind == .math then some original else none) = some function at selected
      by_cases kind : original.kind = .math
      · simp only [kind, beq_self_eq_true, ↓reduceIte] at selected
        cases Option.some.inj selected
        exact ⟨member, kind⟩
      · simp [kind] at selected
    | _ => contradiction
  · rintro ⟨member, kind⟩
    exact ⟨.function function, member, by simp [kind]⟩

/-- The ordinary phase supplies only a dependency order. Bodies and their association are
reconstructed from this snapshot, and completeness is checked independently of that order. -/
def checkOracleMathEnvironment (snapshot : Snapshot) (domains : List DomainSpec)
    (names : List String) : Except String
      (Σ math : OracleMathEnvironment, PLift (math.Associated snapshot domains)) := do
  let sources ← names.mapM (checkOracleMathSource snapshot domains)
  if complete : snapshot.mathFunctions.all (fun function ↦ sources.any (fun source ↦
      source.checked.helper == ⟨function.name, .math, function.inputs, function.outputs⟩)) = true then
    if bodies : sources.all (fun source ↦
        source.checked.kind == .math && oracleMathBody source.checked.raw) = true then
      let definitions := sources.map (·.checked)
      if linked : DeclarationsLinked [] definitions then
        let math : OracleMathEnvironment := ⟨definitions, linked, by
          intro checked member
          obtain ⟨source, present, rfl⟩ := List.mem_map.mp member
          have allowed := List.all_eq_true.mp bodies source present
          simpa only [Bool.and_eq_true, beq_iff_eq] using allowed⟩
        have associated : math.Associated snapshot domains := by
          constructor
          · intro checked member
            obtain ⟨source, _, rfl⟩ := List.mem_map.mp member
            exact ⟨source.function, source.member, source.kind, source.signature, source.lowered⟩
          · intro function member kind
            have covered := List.all_eq_true.mp complete function
              (Snapshot.mem_mathFunctions.mpr ⟨member, kind⟩)
            obtain ⟨source, present, same⟩ := List.any_eq_true.mp covered
            exact ⟨source.checked, List.mem_map.mpr ⟨source, present, rfl⟩,
              by simpa only [beq_iff_eq] using same⟩
        return ⟨math, ⟨associated⟩⟩
      else throw "oracle-math-link"
    else throw "oracle-math-profile"
  else throw "oracle-math-incomplete"

structure CheckedOracleUnit where
  snapshot : Snapshot
  domains : List DomainSpec
  math : OracleMathEnvironment
  associated : math.Associated snapshot domains
  oracles : List (CheckedOracle snapshot domains math)
  checked : checkOracles snapshot domains math associated = .ok oracles

def checkOracleUnit (snapshot : Snapshot) (names : List String) : Except String CheckedOracleUnit := do
  let domains ← snapshot.domains.mapM Domain.resolve
  let ⟨math, associated⟩ ← checkOracleMathEnvironment snapshot domains names
  match checked : checkOracles snapshot domains math associated.down with
  | .error error => throw (error.code ++ " at definition " ++ toString error.definition)
  | .ok oracles => return ⟨snapshot, domains, math, associated.down, oracles, checked⟩

theorem checkOracleUnit_source {snapshot : Snapshot} {names : List String}
    {unit : CheckedOracleUnit} (accepted : checkOracleUnit snapshot names = .ok unit) :
    unit.snapshot = snapshot := by
  unfold checkOracleUnit at accepted
  simp only [bind, Except.bind] at accepted
  repeat' first | contradiction | split at accepted
  all_goals cases accepted; rfl

theorem checkOracleUnit_some_source {snapshot : Snapshot} {names : List String}
    {unit : CheckedOracleUnit}
    (accepted : (checkOracleUnit snapshot names).map some = .ok (some unit)) :
    unit.snapshot = snapshot := by
  cases checked : checkOracleUnit snapshot names with
  | error error => simp [checked, Except.map] at accepted
  | ok value =>
    have same : value = unit := by simpa [checked, Except.map] using accepted
    subst value
    exact checkOracleUnit_source checked

private theorem mapM_covers {α β ε : Type} {checker : α → Except ε β}
    {source : List α} {checked : List β} (accepted : source.mapM checker = .ok checked) :
    ∀ original ∈ source, ∃ value ∈ checked, checker original = .ok value := by
  induction source generalizing checked with
  | nil => simp
  | cons head tail ih =>
    simp only [List.mapM_cons, bind, Except.bind] at accepted
    cases first : checker head with
    | error error => simp [first] at accepted
    | ok value =>
      cases rest : tail.mapM checker with
      | error error => simp [first, rest] at accepted
      | ok values =>
        have same : value :: values = checked := by
          simpa only [first, rest, Except.bind, pure, Except.pure, Except.ok.injEq] using accepted
        subst checked
        intro original member
        rcases List.mem_cons.mp member with rfl | member
        · exact ⟨value, List.mem_cons_self, first⟩
        · obtain ⟨result, present, equation⟩ := ih rest original member
          exact ⟨result, List.mem_cons_of_mem _ present, equation⟩

theorem checkOracle_index {snapshot : Snapshot} {domains : List DomainSpec}
    {math : OracleMathEnvironment} {associated : math.Associated snapshot domains}
    {index : Nat} {checked : CheckedOracle snapshot domains math}
    (accepted : checkOracle snapshot domains math associated index = .ok checked) :
    checked.sourceIndex = index := by
  unfold checkOracle at accepted
  repeat' first | contradiction | split at accepted
  all_goals cases accepted; rfl

/-- Every actual declaration, including dormant declarations, has its exact source index
and its checked retained body in the only admitted Oracle table. The converse is the
`sourceExact` field of each element, with its `lowered` and `formed` equations. -/
theorem CheckedOracleUnit.complete (unit : CheckedOracleUnit) (index : Nat)
    (declaration : OracleDeclaration)
    (original : unit.snapshot.definitions[index]? = some (.oracle declaration)) :
    ∃ checked ∈ unit.oracles, checked.sourceIndex = index := by
  have selected : index ∈ (List.range unit.snapshot.definitions.length).filter (fun position ↦
      match unit.snapshot.definitions[position]? with
      | some (.oracle _) => true | _ => false) := by
    simp only [List.mem_filter, List.mem_range]
    exact ⟨List.getElem?_eq_some_iff.mp original |>.1, by rw [original]⟩
  obtain ⟨checked, member, checkedEq⟩ := mapM_covers unit.checked index selected
  exact ⟨checked, member, checkOracle_index checkedEq⟩

end Zkc.Source.Structured
