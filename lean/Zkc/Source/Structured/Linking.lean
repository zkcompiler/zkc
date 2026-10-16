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

namespace Evaluation

variable {F G : Type} {interface : PIR.Signature}
variable [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]
variable (observations : SiteObservations interface)

/-- Adding a declaration with a different name leaves an existing lookup intact. -/
theorem invoke_extend_other (table : HelperTable (assignment F G) interface) (definition : CheckedDefinition)
    (helper : Helper) (different : definition.name ≠ helper.name) :
    invoke (extendMeanings observations table definition) helper = invoke table helper := by
  simp [invoke, extendMeanings, CheckedDefinition.helper, different]

theorem invoke_foldl_other (table : HelperTable (assignment F G) interface) (definitions : List CheckedDefinition)
    (helper : Helper) (different : ∀ definition ∈ definitions, definition.name ≠ helper.name) :
    invoke (definitions.foldl (extendMeanings observations) table) helper = invoke table helper := by
  induction definitions generalizing table with
  | nil => rfl
  | cons definition rest ih =>
    rw [List.foldl_cons, ih _ (fun d member => different d (List.mem_cons_of_mem _ member))]
    exact invoke_extend_other observations table definition helper (different _ List.mem_cons_self)

private theorem find_foldl_other (table : HelperTable (assignment F G) interface) (definitions : List CheckedDefinition)
    (name : String) (different : ∀ definition ∈ definitions, definition.name ≠ name) :
    (definitions.foldl (extendMeanings observations) table).find? (fun entry => entry.helper.name == name) =
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
    ∃ entry : HelperDefinition (assignment F G) interface,
      (definitions.foldl (extendMeanings observations) []).find? (fun entry => entry.helper.name == helper.name) =
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
  rw [find_foldl_other observations _ after definition.helper.name different]
  exact ⟨⟨definition.helper, fun args => definition.body.denote
    (meaning observations (before.foldl (extendMeanings observations) [])) args.get⟩, by simp [extendMeanings], rfl⟩

/-- Resolve a declaration in its full checked table to its body interpreted in
its own prefix. Later declarations cannot shadow or change that closure. -/
theorem payload_invoke_declaration (payload : Payload)
    (before : List CheckedDefinition) (definition : CheckedDefinition)
    (suffix : List CheckedDefinition)
    (split : payload.definitions = before ++ definition :: suffix)
    (arguments : Values (assignment F G) definition.inputs) :
    invoke (payloadMeanings observations payload) definition.helper arguments =
      definition.body.denote (meaning observations (before.foldl (extendMeanings observations) [])) arguments.get := by
  have linked := payload.linked
  rw [split] at linked
  have tail := (DeclarationsLinked.append [] before (definition :: suffix)).mp linked |>.2
  have different : ∀ other ∈ suffix, other.name ≠ definition.helper.name := by
    intro other member
    exact tail.2.2.fresh List.mem_cons_self member
  simp only [payloadMeanings, split, List.foldl_append, List.foldl_cons]
  rw [invoke_foldl_other observations _ suffix definition.helper different]
  exact invoke_extended observations _ definition arguments

/-- Every helper referenced by a declaration resolves in that declaration's
captured prefix. This is the precise exclusion of the linking fallback. -/
theorem payload_reference_resolves (payload : Payload)
    (before : List CheckedDefinition) (definition : CheckedDefinition)
    (after : List CheckedDefinition)
    (split : payload.definitions = before ++ definition :: after)
    (helper : Helper) (used : helper ∈ definition.helpers) :
    ∃ entry : HelperDefinition (assignment F G) interface,
      (before.foldl (extendMeanings observations) []).find? (fun entry => entry.helper.name == helper.name) =
        some entry ∧ entry.helper = helper := by
  have linked := payload.linked
  rw [split] at linked
  exact linked_lookup observations ((DeclarationsLinked.append [] before (definition :: after)).mp linked).1
    helper (payload.declaration_helpers before definition after split helper used)

/-- Extending a checked prefix preserves every helper already defined there. -/
theorem payload_prefix_agrees (payload : Payload)
    (before after : List CheckedDefinition)
    (split : payload.definitions = before ++ after)
    (helper : Helper) (present : helper ∈ before.map CheckedDefinition.helper) :
    invoke (before.foldl (extendMeanings observations) ([] : HelperTable (assignment F G) interface)) helper =
      invoke (payloadMeanings observations payload) helper := by
  have linked := payload.linked
  rw [split] at linked
  have tail := (DeclarationsLinked.append [] before after).mp linked |>.2
  have available : helper ∈ before.reverse.map CheckedDefinition.helper ++ [] := by
    simpa using present
  have different : ∀ definition ∈ after, definition.name ≠ helper.name := by
    intro definition member
    exact tail.fresh available member
  simp only [payloadMeanings, split, List.foldl_append]
  exact (invoke_foldl_other observations _ after helper different).symm

/-- A declaration body can be reasoned about in the complete checked table.
Its original closure still uses its strict prefix; framing proves they agree
on every referenced helper. This removes ordering details from proof clients. -/
theorem payload_invoke_body (payload : Payload) (definition : CheckedDefinition)
    (member : definition ∈ payload.definitions)
    (arguments : Values (assignment F G) definition.inputs) :
    invoke (payloadMeanings observations payload) definition.helper arguments =
      definition.body.denote (meaning observations (payloadMeanings observations payload)) arguments.get := by
  obtain ⟨before, after, split⟩ := List.mem_iff_append.mp member
  rw [payload_invoke_declaration observations payload before definition after split]
  refine congrFun (region_denote_table_congr observations
    (before.foldl (extendMeanings observations) []) (payloadMeanings observations payload) definition.body ?_) arguments.get
  intro helper used
  have present := payload.declaration_helpers before definition after split helper
    (by simpa only [definition.helpers_eq_body] using used)
  exact payload_prefix_agrees observations payload before (definition :: after) split helper present

/-- Combine name-independent membership with an exact body view. -/
theorem payload_invoke_body_view (payload : Payload) (definition : CheckedDefinition)
    (member : definition ∈ payload.definitions)
    (body : Region dialect definition.inputs definition.outputs)
    (exactRaw : definition.raw = body.erase)
    (arguments : Values (assignment F G) definition.inputs) :
    invoke (payloadMeanings observations payload) definition.helper arguments =
      body.denote (meaning observations (payloadMeanings observations payload)) arguments.get := by
  rw [payload_invoke_body observations payload definition member arguments, definition.body_eq_of_raw body exactRaw]

/-- The checked closed root is interpreted directly in the complete helper table. -/
theorem payload_denote_entry (payload : Payload)
    (arguments : Values (assignment F G) payload.entry.inputs) :
    payloadDenote observations payload arguments = payload.entry.body.denote
      (meaning observations (payloadMeanings observations payload)) arguments.get := rfl

theorem payload_denote_body_view (payload : Payload)
    (body : Region dialect payload.entry.inputs payload.entry.outputs)
    (exactRaw : payload.entry.raw = body.erase)
    (arguments : Values (assignment F G) payload.entry.inputs) :
    payloadDenote observations payload arguments =
      body.denote (meaning observations (payloadMeanings observations payload)) arguments.get := by
  rw [payload_denote_entry, payload.entry.body_eq_of_raw body exactRaw]

theorem payload_denote_body (payload : Payload)
    (body : Region dialect payload.entry.inputs payload.entry.outputs)
    (exactRaw : payload.entry.raw = body.erase)
    (arguments : Values (assignment F G) payload.entry.inputs) :
    payloadDenote observations payload arguments =
      body.denote (meaning observations (payloadMeanings observations payload)) arguments.get :=
  payload_denote_body_view observations payload body exactRaw arguments

end Evaluation

end Zkc.Source.Structured
