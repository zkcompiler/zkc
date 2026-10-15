module

public import Zkc.Source.Structured.Frame

@[expose] public section

/-! Checked declaration linking and invocation. Ordering is a candidate-producing
algorithm; `Payload.linked` is the independently checked semantic interface.
A resolved call may still stop in its body. These laws remove only the missing
or mismatched helper fallback, not legitimate guards or domain failures. -/

namespace Zkc.Source.Structured

/-- Split a checked table at a declaration boundary. Available signatures are
stored in reverse order, matching the meaning table's prepend discipline. -/
theorem DeclarationsLinked.append (available : List Helper)
    (before suffix : List CheckedDefinition) :
    DeclarationsLinked available (before ++ suffix) ↔
      DeclarationsLinked available before ∧
      DeclarationsLinked (before.reverse.map CheckedDefinition.helper ++ available) suffix := by
  induction before generalizing available with
  | nil => simp [DeclarationsLinked]
  | cons definition rest ih =>
    simp only [List.cons_append, DeclarationsLinked, ih, List.reverse_cons,
      List.map_append, List.map_cons, List.map_nil, List.append_assoc, List.cons_append,
      List.nil_append]
    simp only [and_assoc]

theorem DeclarationsLinked.fresh {available : List Helper}
    {definitions : List CheckedDefinition} (linked : DeclarationsLinked available definitions)
    {helper : Helper} (present : helper ∈ available)
    {definition : CheckedDefinition} (member : definition ∈ definitions) :
    definition.name ≠ helper.name := by
  induction definitions generalizing available with
  | nil => simp at member
  | cons head rest ih =>
    rcases List.mem_cons.mp member with same | member
    · subst definition
      intro sameName
      exact linked.1 (List.mem_map.mpr ⟨helper, present, sameName.symm⟩)
    · exact ih linked.2.2 (List.mem_cons_of_mem _ present) member

theorem DeclarationsLinked.nodup {available : List Helper}
    {definitions : List CheckedDefinition} (linked : DeclarationsLinked available definitions) :
    (definitions.map (·.name)).Nodup := by
  induction definitions generalizing available with
  | nil => simp
  | cons definition rest ih =>
    simp only [List.map_cons, List.nodup_cons]
    constructor
    · intro member
      obtain ⟨other, member, same⟩ := List.mem_map.mp member
      exact linked.2.2.fresh (List.mem_cons_self : definition.helper ∈
        definition.helper :: available) member same
    · exact ih linked.2.2

variable {F : Type} [CommRing F] [DecidableEq F]

/-- Adding a declaration with a different name leaves an existing lookup intact. -/
theorem invoke_extend_other (table : Meanings F) (definition : CheckedDefinition)
    (helper : Helper) (different : definition.name ≠ helper.name) :
    invoke (extendMeanings table definition) helper = invoke table helper := by
  simp [invoke, extendMeanings, CheckedDefinition.helper, different]

theorem invoke_foldl_other (table : Meanings F) (definitions : List CheckedDefinition)
    (helper : Helper) (different : ∀ definition ∈ definitions, definition.name ≠ helper.name) :
    invoke (definitions.foldl extendMeanings table) helper = invoke table helper := by
  induction definitions generalizing table with
  | nil => rfl
  | cons definition rest ih =>
    rw [List.foldl_cons, ih _ (fun d member => different d (List.mem_cons_of_mem _ member))]
    exact invoke_extend_other table definition helper (different _ List.mem_cons_self)

private theorem find_foldl_other (table : Meanings F) (definitions : List CheckedDefinition)
    (name : String) (different : ∀ definition ∈ definitions, definition.name ≠ name) :
    (definitions.foldl extendMeanings table).find? (fun entry => entry.helper.name == name) =
      table.find? (fun entry => entry.helper.name == name) := by
  induction definitions generalizing table with
  | nil => rfl
  | cons definition rest ih =>
    rw [List.foldl_cons, ih _ (fun d member => different d (List.mem_cons_of_mem _ member))]
    simp [extendMeanings, CheckedDefinition.helper, different _ List.mem_cons_self]

/-- Successful exact-signature lookup in the table built from a checked prefix.
The returned implementation may still stop when its body is evaluated. -/
theorem linked_lookup {definitions : List CheckedDefinition}
    (linked : DeclarationsLinked [] definitions) (helper : Helper)
    (present : helper ∈ definitions.map CheckedDefinition.helper) :
    ∃ entry : DenotedDefinition F,
      (definitions.foldl extendMeanings []).find? (fun entry => entry.helper.name == helper.name) =
        some entry ∧ entry.helper = helper := by
  obtain ⟨definition, member, same⟩ := List.mem_map.mp present
  obtain ⟨before, after, split⟩ := List.mem_iff_append.mp member
  rw [split] at linked ⊢
  have tail := (DeclarationsLinked.append [] before (definition :: after)).mp linked |>.2
  have different : ∀ other ∈ after, other.name ≠ definition.helper.name := by
    intro other member
    exact tail.2.2.fresh List.mem_cons_self member
  subst helper
  simp only [List.foldl_append, List.foldl_cons]
  rw [find_foldl_other _ after definition.helper.name different]
  exact ⟨⟨definition.helper, fun args => definition.body.denote
    (meaning F (before.foldl extendMeanings [])) args.get⟩, by simp [extendMeanings], rfl⟩

/-- Resolve a declaration in its full checked table to its body interpreted in
its own prefix. Later declarations cannot shadow or change that closure. -/
theorem Payload.invoke_declaration (payload : Payload)
    (before : List CheckedDefinition) (definition : CheckedDefinition)
    (suffix : List CheckedDefinition)
    (split : payload.definitions = before ++ definition :: suffix)
    (arguments : Values (scalarAssignment F) definition.inputs) :
    invoke (payload.meanings F) definition.helper arguments =
      definition.body.denote (meaning F (before.foldl extendMeanings [])) arguments.get := by
  have linked := payload.linked
  rw [split] at linked
  have tail := (DeclarationsLinked.append [] before (definition :: suffix)).mp linked |>.2
  have different : ∀ other ∈ suffix, other.name ≠ definition.helper.name := by
    intro other member
    exact tail.2.2.fresh List.mem_cons_self member
  simp only [Payload.meanings, split, List.foldl_append, List.foldl_cons]
  rw [invoke_foldl_other _ suffix definition.helper different]
  exact invoke_extended _ definition arguments

/-- Admission validates every helper's exact signature, including those in
nested callbacks. Clients need not evaluate the checker to use the property. -/
theorem Payload.declaration_helpers (payload : Payload)
    (before : List CheckedDefinition) (definition : CheckedDefinition)
    (suffix : List CheckedDefinition)
    (split : payload.definitions = before ++ definition :: suffix) :
    ∀ helper ∈ definition.helpers, helper ∈ before.map CheckedDefinition.helper := by
  have linked := payload.linked
  rw [split] at linked
  have tail := (DeclarationsLinked.append [] before (definition :: suffix)).mp linked |>.2
  simpa using tail.2.1

/-- Every helper referenced by a declaration resolves in that declaration's
captured prefix. This is the precise exclusion of the linking fallback. -/
theorem Payload.reference_resolves (payload : Payload)
    (before : List CheckedDefinition) (definition : CheckedDefinition)
    (after : List CheckedDefinition)
    (split : payload.definitions = before ++ definition :: after)
    (helper : Helper) (used : helper ∈ definition.helpers) :
    ∃ entry : DenotedDefinition F,
      (before.foldl extendMeanings []).find? (fun entry => entry.helper.name == helper.name) =
        some entry ∧ entry.helper = helper := by
  have linked := payload.linked
  rw [split] at linked
  exact linked_lookup ((DeclarationsLinked.append [] before (definition :: after)).mp linked).1
    helper (payload.declaration_helpers before definition after split helper used)

/-- Extending a checked prefix preserves every helper already defined there. -/
theorem Payload.prefix_agrees (payload : Payload)
    (before after : List CheckedDefinition)
    (split : payload.definitions = before ++ after)
    (helper : Helper) (present : helper ∈ before.map CheckedDefinition.helper) :
    invoke (before.foldl extendMeanings ([] : Meanings F)) helper =
      invoke (payload.meanings F) helper := by
  have linked := payload.linked
  rw [split] at linked
  have tail := (DeclarationsLinked.append [] before after).mp linked |>.2
  have available : helper ∈ before.reverse.map CheckedDefinition.helper ++ [] := by
    simpa using present
  have different : ∀ definition ∈ after, definition.name ≠ helper.name := by
    intro definition member
    exact tail.fresh available member
  simp only [Payload.meanings, split, List.foldl_append]
  exact (invoke_foldl_other _ after helper different).symm

/-- A declaration body can be reasoned about in the complete checked table.
Its original closure still uses its strict prefix; framing proves they agree
on every referenced helper. This removes ordering details from proof clients. -/
theorem Payload.invoke_body (payload : Payload) (definition : CheckedDefinition)
    (member : definition ∈ payload.definitions)
    (arguments : Values (scalarAssignment F) definition.inputs) :
    invoke (payload.meanings F) definition.helper arguments =
      definition.body.denote (meaning F (payload.meanings F)) arguments.get := by
  obtain ⟨before, after, split⟩ := List.mem_iff_append.mp member
  rw [payload.invoke_declaration before definition after split]
  refine congrFun (region_denote_table_congr
    (before.foldl extendMeanings []) (payload.meanings F) definition.body ?_) arguments.get
  intro helper used
  have present := payload.declaration_helpers before definition after split helper
    (by simpa only [definition.helpers_eq_body] using used)
  exact payload.prefix_agrees before (definition :: after) split helper present

/-- Combine name-independent membership with an exact body view. -/
theorem Payload.invoke_body_view (payload : Payload) (definition : CheckedDefinition)
    (member : definition ∈ payload.definitions)
    (body : Region dialect definition.inputs definition.outputs)
    (exactRaw : definition.raw = body.erase)
    (arguments : Values (scalarAssignment F) definition.inputs) :
    invoke (payload.meanings F) definition.helper arguments =
      body.denote (meaning F (payload.meanings F)) arguments.get := by
  rw [payload.invoke_body definition member arguments, definition.body_eq_of_raw body exactRaw]

/-- Expose the entry in the complete table, whose unrelated declarations are
ignored by the helper-table frame law. -/
theorem Payload.denote_body_view (payload : Payload)
    (body : Region dialect payload.entry.inputs payload.entry.outputs)
    (exactRaw : payload.entry.raw = body.erase)
    (arguments : Values (scalarAssignment F) payload.entry.inputs) :
    payload.denote F arguments = body.denote (meaning F (payload.meanings F)) arguments.get :=
  payload.invoke_body_view payload.entry (List.get_mem _ _) body exactRaw arguments

/-- The entry's body is interpreted against precisely the declarations before it. -/
theorem Payload.denote_entry (payload : Payload)
    (arguments : Values (scalarAssignment F) payload.entry.inputs) :
    payload.denote F arguments = payload.entry.body.denote
      (meaning F ((payload.definitions.take payload.entryIndex.val).foldl extendMeanings []))
      arguments.get := by
  apply payload.invoke_declaration (payload.definitions.take payload.entryIndex.val)
    payload.entry (payload.definitions.drop (payload.entryIndex.val + 1))
  simp [Payload.entry, List.get_eq_getElem, List.getElem_cons_drop]

/-- A source client supplies only the exact raw body equation. It need not unfold
formation, ordering or the complete table to expose the computation. -/
theorem Payload.denote_body (payload : Payload)
    (body : Region dialect payload.entry.inputs payload.entry.outputs)
    (exactRaw : payload.entry.raw = body.erase)
    (arguments : Values (scalarAssignment F) payload.entry.inputs) :
    payload.denote F arguments = body.denote
      (meaning F ((payload.definitions.take payload.entryIndex.val).foldl extendMeanings []))
      arguments.get := by
  rw [payload.denote_entry, payload.entry.body_eq_of_raw body exactRaw]

end Zkc.Source.Structured
