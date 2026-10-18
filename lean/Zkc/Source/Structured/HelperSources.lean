module

public import Zkc.Source.Structured.Import

@[expose] public section

/-! Original-to-checked association for named helpers, the counterpart of
`Imported.protocolSource`: every checked helper of an admitted unit is the
exact checked form of one retained non-protocol source declaration. -/

namespace Zkc.Source.Structured

theorem formDefinition_name {definition : Definition} {kind : HelperKind} {raw : RawRegion Ty Op}
    {checked : CheckedDefinition} (accepted : formDefinition definition kind raw = .ok checked) :
    checked.name = definition.name := by
  unfold formDefinition formDefinitionDiagnostic at accepted
  split at accepted
  · contradiction
  · cases Except.ok.inj accepted
    rfl

/-- A checked helper keeps the name of the declaration it was checked from. -/
theorem checkDefinition_name {snapshot : Snapshot} {domains : List DomainSpec}
    {summaries : IdentitySummaries} {definition : Definition} {checked : CheckedDefinition}
    (accepted : checkDefinition snapshot domains summaries definition = .ok checked) :
    checked.name = definition.name := by
  unfold checkDefinition at accepted
  simp only [bind, Except.bind] at accepted
  repeat' first | contradiction | split at accepted
  all_goals exact formDefinition_name accepted

/-- Dependency ordering only selects among already checked candidates. -/
theorem orderDefinitions_mem {fuel : Nat} {pending : List CheckedDefinition}
    {ordered result : List OrderedDefinition}
    (accepted : orderDefinitions fuel pending ordered = .ok result) :
    ∀ item ∈ result, item.definition ∈ ordered.map (·.definition) ∨ item.definition ∈ pending := by
  induction fuel generalizing pending ordered with
  | zero =>
    cases pending with
    | nil =>
      simp only [orderDefinitions, Except.ok.injEq] at accepted
      subst accepted
      intro item member
      exact .inl (List.mem_map_of_mem member)
    | cons head tail => simp [orderDefinitions] at accepted
  | succ remaining ih =>
    cases pending with
    | nil =>
      simp only [orderDefinitions, Except.ok.injEq] at accepted
      subst accepted
      intro item member
      exact .inl (List.mem_map_of_mem member)
    | cons head tail =>
      simp only [orderDefinitions, bind, Except.bind] at accepted
      repeat' first | contradiction | split at accepted
      all_goals
        intro item member
        rcases ih accepted item member with old | later
        · rw [List.map_append, List.mem_append] at old
          rcases old with old | added
          · exact .inl old
          · simp only [List.map_cons, List.map_nil, List.mem_singleton] at added
            rw [added]
            exact .inr (List.mem_of_find?_eq_some (by assumption))
        · exact .inr (List.mem_filter.mp later).1

/-- Each helper produced by the helper phase is checked from a retained source
declaration that is not a protocol. -/
theorem checkUnitHelpers_sources {snapshot : Snapshot} {domains : List DomainSpec}
    {summaries : IdentitySummaries} {ordered : List OrderedDefinition}
    (accepted : checkUnitHelpers snapshot domains summaries = .ok ordered) :
    ∀ item ∈ ordered, ∃ original ∈ snapshot.definitions, original.kind ≠ .protocol ∧
      checkDefinition snapshot domains summaries original = .ok item.definition := by
  unfold checkUnitHelpers at accepted
  simp only [bind, Except.bind, pure, Except.pure] at accepted
  repeat' first | contradiction | split at accepted
  all_goals
    cases accepted
    intro item member
    rcases orderDefinitions_mem (by assumption) item member with absurd | candidate
    · simp at absurd
    · obtain ⟨original, retained, formed⟩ := (checkedMap_sources (by assumption)).1 _ candidate
      obtain ⟨present, kind⟩ := List.mem_filter.mp retained
      exact ⟨original, present, by simpa using kind, formed⟩

/-- Every checked helper is the exact checked form of a retained non-protocol
declaration, under the unit's own resolved domains and identity summaries. -/
theorem Imported.helperSource {snapshot : Snapshot} (imported : Imported snapshot)
    {definition : CheckedDefinition} (member : definition ∈ imported.program.payload.definitions) :
    ∃ original domains headers summaries,
      original ∈ snapshot.definitions ∧ original.kind ≠ .protocol ∧
      checkUnitHeaders snapshot = .ok (domains, headers, summaries) ∧
      checkDefinition snapshot domains summaries original = .ok definition := by
  obtain ⟨domains, headers, summaries, helpers, _, headerEq, helperEq, _, _, linked⟩ :=
    check_payload_stages imported.admission
  rw [(linkUnitPayload_fields linked).1] at member
  obtain ⟨item, itemMember, same⟩ := List.mem_map.mp member
  obtain ⟨original, retained, kind, checked⟩ := checkUnitHelpers_sources helperEq item itemMember
  exact ⟨original, domains, headers, summaries, retained, kind, headerEq, same ▸ checked⟩

end Zkc.Source.Structured
