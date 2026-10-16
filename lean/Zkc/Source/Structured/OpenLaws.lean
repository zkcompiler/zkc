module

public import Zkc.Source.Structured.OpenMeaning
public import Zkc.Source.Structured.ComponentLinking

@[expose] public section

/-! Full-table equations for the whole-unit participant subject. Protocol roots
remain outside the helper inventory. Successful lookup establishes an exact
signature, not that evaluating the resolved body terminates successfully. -/

namespace Zkc.Source.Structured

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

theorem UnitPayload.declaration_helpers (payload : UnitPayload)
    (before : List CheckedDefinition) (definition : CheckedDefinition)
    (after : List CheckedDefinition)
    (split : payload.definitions = before ++ definition :: after) :
    ∀ helper ∈ definition.helpers, helper ∈ before.map CheckedDefinition.helper := by
  have linked := payload.linked
  rw [split] at linked
  have tail := (DeclarationsLinked.append [] before (definition :: after)).mp linked |>.2
  simpa using tail.2.1

theorem UnitPayload.tables_closed (payload : UnitPayload) :
    (payload.tables F G).closed =
      payload.definitions.foldl (Evaluation.extendMeanings (observedSites F G)) [] :=
  Evaluation.ComponentTables.closed_fold (observedSites F G) _ _

theorem UnitPayload.closed_lookup (payload : UnitPayload) (helper : Helper)
    (present : helper ∈ payload.definitions.map CheckedDefinition.helper) :
    ∃ entry : HelperDefinition (assignment F G) (observedInterface F G),
      (payload.tables F G).closed.find? (fun entry => entry.helper.name == helper.name) =
        some entry ∧ entry.helper = helper := by
  rw [payload.tables_closed]
  exact Evaluation.linked_lookup (observedSites F G) payload.linked helper present

theorem UnitPayload.component_lookup (payload : UnitPayload) (helper : Helper)
    (present : helper ∈ payload.definitions.map CheckedDefinition.helper) :
    ∃ entry : HelperDefinition (Component (assignment F G)) (observedInterface F G),
      (payload.tables F G).components.find? (fun entry => entry.helper.name == helper.name) =
        some entry ∧ entry.helper = helper :=
  Evaluation.component_linked_lookup (observedSites F G) payload.linked helper present

theorem UnitPayload.root_closed_reference_resolves (payload : UnitPayload)
    (root : CheckedProtocol) (member : root ∈ payload.protocols)
    (helper : Helper) (used : helper ∈ root.helpers) :
    ∃ entry : HelperDefinition (assignment F G) (observedInterface F G),
      (payload.tables F G).closed.find? (fun entry => entry.helper.name == helper.name) =
        some entry ∧ entry.helper = helper :=
  payload.closed_lookup helper (payload.rootsLinked root member helper used)

theorem UnitPayload.root_component_reference_resolves (payload : UnitPayload)
    (root : CheckedProtocol) (member : root ∈ payload.protocols)
    (helper : Helper) (used : helper ∈ root.helpers) :
    ∃ entry : HelperDefinition (Component (assignment F G)) (observedInterface F G),
      (payload.tables F G).components.find? (fun entry => entry.helper.name == helper.name) =
        some entry ∧ entry.helper = helper :=
  payload.component_lookup helper (payload.rootsLinked root member helper used)

theorem UnitPayload.entry_mem (payload : UnitPayload) : payload.entry ∈ payload.protocols :=
  List.get_mem _ _

theorem UnitPayload.entry_helpers (payload : UnitPayload) :
    ∀ helper ∈ payload.entry.helpers, helper ∈ payload.definitions.map CheckedDefinition.helper :=
  payload.rootsLinked payload.entry payload.entry_mem

theorem UnitPayload.closed_reference_resolves (payload : UnitPayload)
    (before : List CheckedDefinition) (definition : CheckedDefinition)
    (after : List CheckedDefinition) (split : payload.definitions = before ++ definition :: after)
    (helper : Helper) (used : helper ∈ definition.helpers) :
    ∃ entry : HelperDefinition (assignment F G) (observedInterface F G),
      (before.foldl (Evaluation.extendMeanings (observedSites F G)) []).find?
        (fun entry => entry.helper.name == helper.name) = some entry ∧ entry.helper = helper := by
  have linked := payload.linked
  rw [split] at linked
  exact Evaluation.linked_lookup (observedSites F G)
    ((DeclarationsLinked.append [] before (definition :: after)).mp linked).1
    helper (payload.declaration_helpers before definition after split helper used)

theorem UnitPayload.component_reference_resolves (payload : UnitPayload)
    (before : List CheckedDefinition) (definition : CheckedDefinition)
    (after : List CheckedDefinition) (split : payload.definitions = before ++ definition :: after)
    (helper : Helper) (used : helper ∈ definition.helpers) :
    ∃ entry : HelperDefinition (Component (assignment F G)) (observedInterface F G),
      (before.foldl (Evaluation.ComponentTables.extend (observedSites F G))
        (⟨[], []⟩ : OpenTables F G)).components.find?
        (fun entry => entry.helper.name == helper.name) = some entry ∧ entry.helper = helper := by
  have linked := payload.linked
  rw [split] at linked
  exact Evaluation.component_linked_lookup (observedSites F G)
    ((DeclarationsLinked.append [] before (definition :: after)).mp linked).1
    helper (payload.declaration_helpers before definition after split helper used)

theorem UnitPayload.closed_prefix_agrees (payload : UnitPayload)
    (before after : List CheckedDefinition) (split : payload.definitions = before ++ after)
    (helper : Helper) (present : helper ∈ before.map CheckedDefinition.helper) :
    invoke (before.foldl (Evaluation.extendMeanings (observedSites F G)) []) helper =
      invoke (payload.tables F G).closed helper := by
  have linked := payload.linked
  rw [split] at linked
  have tail := (DeclarationsLinked.append [] before after).mp linked |>.2
  have available : helper ∈ before.reverse.map CheckedDefinition.helper ++ [] := by
    simpa using present
  have different : ∀ definition ∈ after, definition.name ≠ helper.name := by
    intro definition member
    exact tail.fresh available member
  rw [payload.tables_closed, split, List.foldl_append]
  exact (Evaluation.invoke_foldl_other (observedSites F G) _ after helper different).symm

theorem UnitPayload.component_prefix_agrees (payload : UnitPayload)
    (before after : List CheckedDefinition) (split : payload.definitions = before ++ after)
    (helper : Helper) (present : helper ∈ before.map CheckedDefinition.helper) :
    invoke (before.foldl (Evaluation.ComponentTables.extend (observedSites F G))
      (⟨[], []⟩ : OpenTables F G)).components helper =
      invoke (payload.tables F G).components helper := by
  have linked := payload.linked
  rw [split] at linked
  have tail := (DeclarationsLinked.append [] before after).mp linked |>.2
  have available : helper ∈ before.reverse.map CheckedDefinition.helper ++ [] := by
    simpa using present
  have different : ∀ definition ∈ after, definition.name ≠ helper.name := by
    intro definition member
    exact tail.fresh available member
  simp only [UnitPayload.tables, split, List.foldl_append]
  exact (Evaluation.component_invoke_foldl_other (observedSites F G) _ after helper different).symm

theorem UnitPayload.closed_invoke_declaration (payload : UnitPayload)
    (before : List CheckedDefinition) (definition : CheckedDefinition)
    (after : List CheckedDefinition) (split : payload.definitions = before ++ definition :: after)
    (args : Values (assignment F G) definition.inputs) :
    invoke (payload.tables F G).closed definition.helper args =
      definition.body.denote (Evaluation.meaning (observedSites F G)
        (before.foldl (Evaluation.extendMeanings (observedSites F G)) [])) args.get := by
  have linked := payload.linked
  rw [split] at linked
  have tail := (DeclarationsLinked.append [] before (definition :: after)).mp linked |>.2
  have different : ∀ other ∈ after, other.name ≠ definition.helper.name := by
    intro other member
    exact tail.2.2.fresh List.mem_cons_self member
  rw [payload.tables_closed, split, List.foldl_append, List.foldl_cons,
    Evaluation.invoke_foldl_other (observedSites F G) _ after definition.helper different]
  exact Evaluation.invoke_extended (observedSites F G) _ definition args

theorem UnitPayload.component_invoke_declaration (payload : UnitPayload)
    (before : List CheckedDefinition) (definition : CheckedDefinition)
    (after : List CheckedDefinition) (split : payload.definitions = before ++ definition :: after)
    (args : Values (Component (assignment F G)) definition.inputs) :
    invoke (payload.tables F G).components definition.helper args =
      let captured := before.foldl (Evaluation.ComponentTables.extend (observedSites F G))
        (⟨[], []⟩ : OpenTables F G)
      definition.body.component (Evaluation.meaning (observedSites F G) captured.closed)
        (Evaluation.componentOperation (observedSites F G) captured) args.get := by
  have linked := payload.linked
  rw [split] at linked
  have tail := (DeclarationsLinked.append [] before (definition :: after)).mp linked |>.2
  have different : ∀ other ∈ after, other.name ≠ definition.helper.name := by
    intro other member
    exact tail.2.2.fresh List.mem_cons_self member
  simp only [UnitPayload.tables, split, List.foldl_append, List.foldl_cons]
  rw [Evaluation.component_invoke_foldl_other (observedSites F G) _ after definition.helper different]
  exact Evaluation.component_invoke_extended (observedSites F G) _ definition args

/-- Full-table closed invocation, with framing of the actual captured prefix. -/
theorem UnitPayload.closed_invoke_body (payload : UnitPayload) (definition : CheckedDefinition)
    (member : definition ∈ payload.definitions) (args : Values (assignment F G) definition.inputs) :
    invoke (payload.tables F G).closed definition.helper args =
      definition.body.denote (Evaluation.meaning (observedSites F G)
        (payload.tables F G).closed) args.get := by
  obtain ⟨before, after, split⟩ := List.mem_iff_append.mp member
  rw [payload.closed_invoke_declaration before definition after split]
  refine congrFun (Evaluation.region_denote_table_congr (observedSites F G)
    (before.foldl (Evaluation.extendMeanings (observedSites F G)) [])
    (payload.tables F G).closed definition.body ?_) args.get
  intro helper used
  exact payload.closed_prefix_agrees before (definition :: after) split helper
    (payload.declaration_helpers before definition after split helper
      (by simpa only [definition.helpers_eq_body] using used))

/-- Full-table optional invocation frames both the closed and component tables. -/
theorem UnitPayload.component_invoke_body (payload : UnitPayload) (definition : CheckedDefinition)
    (member : definition ∈ payload.definitions)
    (args : Values (Component (assignment F G)) definition.inputs) :
    invoke (payload.tables F G).components definition.helper args =
      definition.body.component (Evaluation.meaning (observedSites F G) (payload.tables F G).closed)
        (Evaluation.componentOperation (observedSites F G) (payload.tables F G)) args.get := by
  obtain ⟨before, after, split⟩ := List.mem_iff_append.mp member
  rw [payload.component_invoke_declaration before definition after split]
  refine congrFun (Evaluation.region_component_table_congr (observedSites F G)
    (before.foldl (Evaluation.ComponentTables.extend (observedSites F G)) ⟨[], []⟩)
    (payload.tables F G) definition.body ?_ ?_) args.get
  · intro helper used
    rw [Evaluation.ComponentTables.closed_fold]
    exact payload.closed_prefix_agrees before (definition :: after) split helper
      (payload.declaration_helpers before definition after split helper
        (by simpa only [definition.helpers_eq_body] using used))
  · intro helper used
    exact payload.component_prefix_agrees before (definition :: after) split helper
      (payload.declaration_helpers before definition after split helper
        (by simpa only [definition.helpers_eq_body] using used))

theorem UnitPayload.closed_body_view (payload : UnitPayload) (definition : CheckedDefinition)
    (member : definition ∈ payload.definitions) (body : Region dialect definition.inputs definition.outputs)
    (exactRaw : definition.raw = body.erase) (args : Values (assignment F G) definition.inputs) :
    invoke (payload.tables F G).closed definition.helper args =
      body.denote (Evaluation.meaning (observedSites F G) (payload.tables F G).closed) args.get := by
  rw [payload.closed_invoke_body definition member args, definition.body_eq_of_raw body exactRaw]

theorem UnitPayload.component_body_view (payload : UnitPayload) (definition : CheckedDefinition)
    (member : definition ∈ payload.definitions) (body : Region dialect definition.inputs definition.outputs)
    (exactRaw : definition.raw = body.erase)
    (args : Values (Component (assignment F G)) definition.inputs) :
    invoke (payload.tables F G).components definition.helper args =
      body.component (Evaluation.meaning (observedSites F G) (payload.tables F G).closed)
        (Evaluation.componentOperation (observedSites F G) (payload.tables F G)) args.get := by
  rw [payload.component_invoke_body definition member args, definition.body_eq_of_raw body exactRaw]

/-- Use an explicit helper ABI and named signature evidence, avoiding repeated
normalization of a concrete admission computation during downstream elaboration. -/
theorem UnitPayload.closed_body_view_as (payload : UnitPayload) (definition : CheckedDefinition)
    (member : definition ∈ payload.definitions) (helper : Helper)
    (signature : definition.helper = helper)
    (body : Region dialect helper.inputs helper.outputs) (exactRaw : definition.raw = body.erase)
    (args : Values (assignment F G) helper.inputs) :
    invoke (payload.tables F G).closed helper args =
      body.denote (Evaluation.meaning (observedSites F G) (payload.tables F G).closed) args.get := by
  subst helper
  exact payload.closed_body_view definition member body exactRaw args

/-- The same explicit-ABI transport preserves optional component semantics. -/
theorem UnitPayload.component_body_view_as (payload : UnitPayload) (definition : CheckedDefinition)
    (member : definition ∈ payload.definitions) (helper : Helper)
    (signature : definition.helper = helper)
    (body : Region dialect helper.inputs helper.outputs) (exactRaw : definition.raw = body.erase)
    (args : Values (Component (assignment F G)) helper.inputs) :
    invoke (payload.tables F G).components helper args =
      body.component (Evaluation.meaning (observedSites F G) (payload.tables F G).closed)
        (Evaluation.componentOperation (observedSites F G) (payload.tables F G)) args.get := by
  subst helper
  exact payload.component_body_view definition member body exactRaw args

theorem CheckedProtocol.observed_body_view (root : CheckedProtocol)
    (body : Region protocolDialect root.inputs root.outputs) (same : root.raw = body.erase)
    (tables : OpenTables F G) (self : Nat)
    (inputs : Values (Component (assignment F G)) root.inputs) :
    root.observed tables self inputs =
      (body.denote (participantMeaning tables self) (maskValues self root.inputScopes inputs).get).bind
        fun results => .done (maskValues self root.outputScopes results) := by
  simp only [CheckedProtocol.observed, root.body_eq_of_raw body same]

theorem Program.observed_body_view (program : Program)
    (body : Region protocolDialect program.payload.entry.inputs program.payload.entry.outputs)
    (same : program.payload.entry.raw = body.erase) (self : Nat)
    (inputs : Values (Component (assignment F G)) program.payload.entry.inputs) :
    program.observed F G self inputs =
      (body.denote (participantMeaning (program.payload.tables F G) self)
        (maskValues self program.payload.entry.inputScopes inputs).get).bind
        fun results => .done (maskValues self program.payload.entry.outputScopes results) :=
  program.payload.entry.observed_body_view body same _ self inputs

theorem Program.participant_body_view (program : Program)
    (body : Region protocolDialect program.payload.entry.inputs program.payload.entry.outputs)
    (same : program.payload.entry.raw = body.erase) (self : Nat)
    (inputs : Values (Component (assignment F G)) program.payload.entry.inputs) :
    program.participant F G self inputs =
      ((body.denote (participantMeaning (program.payload.tables F G) self)
        (maskValues self program.payload.entry.inputScopes inputs).get).bind
        fun results => .done (maskValues self program.payload.entry.outputScopes results)).interpret forgetSites :=
  congrArg (fun process => process.interpret forgetSites)
    (program.observed_body_view body same self inputs)

end Zkc.Source.Structured
