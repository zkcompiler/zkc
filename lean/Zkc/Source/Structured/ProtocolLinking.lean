module

public import Zkc.Source.Structured.OpenMeaning
public import Zkc.Source.Structured.ComponentLinking

@[expose] public section

namespace Zkc.Source.Structured

/-- The actual checked role substitution preserves a valid root-coordinate context. -/
theorem resolved_application_context_valid {snapshot : Snapshot}
    {headers : List ProtocolSignature} {caller : ProtocolInterface}
    {name : String} {roles : List String} {signature : ProtocolSignature} {indices : List Nat}
    (accepted : resolveProtocolApplication snapshot headers caller name roles = .ok (signature, indices))
    {rootRoles : List String} {context : ProtocolContext}
    (valid : ProtocolContext.Valid rootRoles caller.roles context) (site : String) :
    ProtocolContext.Valid rootRoles signature.roles (context.enter site indices) :=
  valid.enter (resolveProtocolApplication_roles accepted) site

/-- Prefix inventories are reversed by the closure table's prepend discipline. -/
theorem ProtocolDeclarationsLinked.append (helpers : List Helper)
    (available : List ProtocolSignature) (before after : List CheckedProtocol) :
    ProtocolDeclarationsLinked helpers available (before ++ after) ↔
      ProtocolDeclarationsLinked helpers available before ∧
      ProtocolDeclarationsLinked helpers
        (before.reverse.map CheckedProtocol.signature ++ available) after := by
  induction before generalizing available with
  | nil => simp [ProtocolDeclarationsLinked]
  | cons definition rest ih =>
    simp only [List.cons_append, ProtocolDeclarationsLinked, ih, List.reverse_cons,
      List.map_append, List.map_cons, List.map_nil, List.append_assoc, List.cons_append,
      List.nil_append, and_assoc]

theorem ProtocolDeclarationsLinked.fresh {helpers : List Helper}
    {available : List ProtocolSignature} {definitions : List CheckedProtocol}
    (linked : ProtocolDeclarationsLinked helpers available definitions)
    {signature : ProtocolSignature} (present : signature ∈ available)
    {definition : CheckedProtocol} (member : definition ∈ definitions) :
    definition.name ≠ signature.name := by
  induction definitions generalizing available with
  | nil => simp at member
  | cons head rest ih =>
    rcases List.mem_cons.mp member with same | member
    · subst definition
      intro sameName
      exact linked.1 (List.mem_map.mpr ⟨signature, present, sameName.symm⟩)
    · exact ih linked.2.2.2 (List.mem_cons_of_mem _ present) member

theorem ProtocolDeclarationsLinked.nodup {helpers : List Helper}
    {available : List ProtocolSignature} {definitions : List CheckedProtocol}
    (linked : ProtocolDeclarationsLinked helpers available definitions) :
    (definitions.map (·.name)).Nodup := by
  induction definitions generalizing available with
  | nil => simp
  | cons definition rest ih =>
    simp only [List.map_cons, List.nodup_cons]
    constructor
    · intro member
      obtain ⟨other, member, same⟩ := List.mem_map.mp member
      exact linked.2.2.2.fresh (List.mem_cons_self : definition.signature ∈
        definition.signature :: available) member same
    · exact ih linked.2.2.2

theorem UnitPayload.declaration_protocols (payload : UnitPayload)
    (before : List CheckedProtocol) (definition : CheckedProtocol) (after : List CheckedProtocol)
    (split : payload.protocols = before ++ definition :: after) :
    ∀ signature ∈ definition.protocols, signature ∈ before.map CheckedProtocol.signature := by
  have linked := payload.protocolsLinked
  rw [split] at linked
  have tail := (ProtocolDeclarationsLinked.append _ [] before (definition :: after)).mp linked |>.2
  simpa using tail.2.2.1

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

/-- Framing quantifies over entire closures, hence over every nested context. -/
theorem protocolOperation_table_congr {I : PIR.Signature}
    (observations : SiteObservations I)
    (actions : PIR.OperationInterpretation (participantInterface F G) I)
    (left right : Evaluation.ComponentTables F G I)
    (leftProtocols rightProtocols : ProtocolTable (assignment F G) I)
    (self : Nat) (context : ProtocolContext) (op : ProtocolOp)
    (closedAgree : ∀ helper ∈ op.helpers, invoke left.closed helper = invoke right.closed helper)
    (componentAgree : ∀ helper ∈ op.helpers,
      invoke left.components helper = invoke right.components helper)
    (protocolAgree : ∀ signature ∈ op.protocols,
      invokeProtocol leftProtocols signature = invokeProtocol rightProtocols signature) :
    (fun args callbacks => protocolOperationWith observations actions left self op args callbacks leftProtocols context) =
      (fun args callbacks => protocolOperationWith observations actions right self op args callbacks rightProtocols context) := by
  funext args callbacks
  cases op with
  | calculate op allowed =>
    exact congrFun (congrFun
      (Evaluation.componentOperation_table_congr observations left right op closedAgree componentAgree) args)
      (op.calculationRegions allowed)
  | localCall helper kind owner site =>
    simp only [protocolOperationWith, closedAgree helper (by simp [ProtocolOp.helpers])]
  | protocolApply signature roles site =>
    simp only [protocolOperationWith, protocolAgree signature (by simp [ProtocolOp.protocols])]
  | guard | exchange | restrict =>
    cases args with
    | cons value rest => cases rest; rfl
  | mark => cases args; rfl
  | draw | statement => rfl

theorem protocol_region_table_congr {I : PIR.Signature}
    (observations : SiteObservations I)
    (actions : PIR.OperationInterpretation (participantInterface F G) I)
    (left right : Evaluation.ComponentTables F G I)
    (leftProtocols rightProtocols : ProtocolTable (assignment F G) I)
    (self : Nat) (context : ProtocolContext) {inputs outputs : List Ty}
    (body : Region protocolDialect inputs outputs)
    (closedAgree : ∀ helper ∈ body.erase.operations.flatMap ProtocolOp.helpers,
      invoke left.closed helper = invoke right.closed helper)
    (componentAgree : ∀ helper ∈ body.erase.operations.flatMap ProtocolOp.helpers,
      invoke left.components helper = invoke right.components helper)
    (protocolAgree : ∀ signature ∈ body.erase.operations.flatMap ProtocolOp.protocols,
      invokeProtocol leftProtocols signature = invokeProtocol rightProtocols signature) :
    body.denote (participantMeaningWith observations actions left self leftProtocols context) =
      body.denote (participantMeaningWith observations actions right self rightProtocols context) := by
  apply Region.denote_congr
  intro op member
  apply protocolOperation_table_congr
  · intro helper used
    exact closedAgree helper (List.mem_flatMap.mpr ⟨op, member, used⟩)
  · intro helper used
    exact componentAgree helper (List.mem_flatMap.mpr ⟨op, member, used⟩)
  · intro signature used
    exact protocolAgree signature (List.mem_flatMap.mpr ⟨op, member, used⟩)

theorem protocol_regions_table_congr {I : PIR.Signature}
    (observations : SiteObservations I)
    (actions : PIR.OperationInterpretation (participantInterface F G) I)
    (left right : Evaluation.ComponentTables F G I)
    (leftProtocols rightProtocols : ProtocolTable (assignment F G) I)
    (self : Nat) (context : ProtocolContext) {signatures : List (List Ty × List Ty)}
    (bodies : Regions protocolDialect signatures)
    (closedAgree : ∀ helper ∈ bodies.erase.operations.flatMap ProtocolOp.helpers,
      invoke left.closed helper = invoke right.closed helper)
    (componentAgree : ∀ helper ∈ bodies.erase.operations.flatMap ProtocolOp.helpers,
      invoke left.components helper = invoke right.components helper)
    (protocolAgree : ∀ signature ∈ bodies.erase.operations.flatMap ProtocolOp.protocols,
      invokeProtocol leftProtocols signature = invokeProtocol rightProtocols signature) :
    bodies.denote (participantMeaningWith observations actions left self leftProtocols context) =
      bodies.denote (participantMeaningWith observations actions right self rightProtocols context) := by
  apply Regions.denote_congr
  intro op member
  apply protocolOperation_table_congr
  · intro helper used
    exact closedAgree helper (List.mem_flatMap.mpr ⟨op, member, used⟩)
  · intro helper used
    exact componentAgree helper (List.mem_flatMap.mpr ⟨op, member, used⟩)
  · intro signature used
    exact protocolAgree signature (List.mem_flatMap.mpr ⟨op, member, used⟩)

section GenericLinking

variable {I : PIR.Signature} (observations : SiteObservations I)
  (actions : PIR.OperationInterpretation (participantInterface F G) I)
  (helpers : Evaluation.ComponentTables F G I)

theorem protocol_invoke_extended (table : ProtocolTable (assignment F G) I)
    (definition : CheckedProtocol) :
    invokeProtocol (extendProtocolTable observations actions helpers table definition) definition.signature =
      definition.denoteWith observations actions helpers table :=
  invokeProtocol_cons_same _ _

theorem protocol_invoke_extend_other (table : ProtocolTable (assignment F G) I)
    (definition : CheckedProtocol) (signature : ProtocolSignature)
    (different : definition.name ≠ signature.name) :
    invokeProtocol (extendProtocolTable observations actions helpers table definition) signature =
      invokeProtocol table signature :=
  invokeProtocol_cons_other _ _ _ different

theorem protocol_invoke_foldl_other (table : ProtocolTable (assignment F G) I)
    (definitions : List CheckedProtocol) (signature : ProtocolSignature)
    (different : ∀ definition ∈ definitions, definition.name ≠ signature.name) :
    invokeProtocol (definitions.foldl (extendProtocolTable observations actions helpers) table) signature =
      invokeProtocol table signature := by
  induction definitions generalizing table with
  | nil => rfl
  | cons definition rest ih =>
    rw [List.foldl_cons, ih _ (fun d member => different d (List.mem_cons_of_mem _ member))]
    exact protocol_invoke_extend_other observations actions helpers table definition signature
      (different _ List.mem_cons_self)

private theorem protocol_find_foldl_other (table : ProtocolTable (assignment F G) I)
    (definitions : List CheckedProtocol) (name : String)
    (different : ∀ definition ∈ definitions, definition.name ≠ name) :
    (definitions.foldl (extendProtocolTable observations actions helpers) table).find?
        (fun entry => entry.signature.name == name) =
      table.find? (fun entry => entry.signature.name == name) := by
  induction definitions generalizing table with
  | nil => rfl
  | cons definition rest ih =>
    rw [List.foldl_cons, ih _ (fun d member => different d (List.mem_cons_of_mem _ member))]
    simp [extendProtocolTable, CheckedProtocol.signature, different _ List.mem_cons_self]

theorem protocol_linked_lookup {inventory : List Helper} {definitions : List CheckedProtocol}
    (linked : ProtocolDeclarationsLinked inventory [] definitions) (signature : ProtocolSignature)
    (present : signature ∈ definitions.map CheckedProtocol.signature) :
    ∃ entry : ProtocolDefinition (assignment F G) I,
      (definitions.foldl (extendProtocolTable observations actions helpers) []).find?
        (fun entry => entry.signature.name == signature.name) = some entry ∧ entry.signature = signature := by
  obtain ⟨definition, member, same⟩ := List.mem_map.mp present
  obtain ⟨before, after, split⟩ := List.mem_iff_append.mp member
  rw [split] at linked ⊢
  have tail := (ProtocolDeclarationsLinked.append _ [] before (definition :: after)).mp linked |>.2
  have different : ∀ other ∈ after, other.name ≠ definition.signature.name := by
    intro other member
    exact tail.2.2.2.fresh List.mem_cons_self member
  subst signature
  simp only [List.foldl_append, List.foldl_cons]
  rw [protocol_find_foldl_other observations actions helpers _ after definition.signature.name different]
  exact ⟨⟨definition.signature, definition.denoteWith observations actions helpers
    (before.foldl (extendProtocolTable observations actions helpers) [])⟩,
    by simp [extendProtocolTable], rfl⟩

theorem protocol_invoke_declaration {inventory : List Helper} (definitions : List CheckedProtocol)
    (linked : ProtocolDeclarationsLinked inventory [] definitions)
    (before : List CheckedProtocol) (definition : CheckedProtocol) (after : List CheckedProtocol)
    (split : definitions = before ++ definition :: after) :
    invokeProtocol (definitions.foldl (extendProtocolTable observations actions helpers) []) definition.signature =
      definition.denoteWith observations actions helpers
        (before.foldl (extendProtocolTable observations actions helpers) []) := by
  rw [split] at linked ⊢
  have tail := (ProtocolDeclarationsLinked.append _ [] before (definition :: after)).mp linked |>.2
  have different : ∀ other ∈ after, other.name ≠ definition.signature.name := by
    intro other member
    exact tail.2.2.2.fresh List.mem_cons_self member
  simp only [List.foldl_append, List.foldl_cons]
  rw [protocol_invoke_foldl_other observations actions helpers _ after definition.signature different]
  exact protocol_invoke_extended observations actions helpers _ definition

theorem protocol_prefix_agrees {inventory : List Helper} (definitions : List CheckedProtocol)
    (linked : ProtocolDeclarationsLinked inventory [] definitions)
    (before after : List CheckedProtocol) (split : definitions = before ++ after)
    (signature : ProtocolSignature) (present : signature ∈ before.map CheckedProtocol.signature) :
    invokeProtocol (before.foldl (extendProtocolTable observations actions helpers) []) signature =
      invokeProtocol (definitions.foldl (extendProtocolTable observations actions helpers) []) signature := by
  rw [split] at linked ⊢
  have tail := (ProtocolDeclarationsLinked.append _ [] before after).mp linked |>.2
  have available : signature ∈ before.reverse.map CheckedProtocol.signature ++ [] := by
    simpa using present
  have different : ∀ definition ∈ after, definition.name ≠ signature.name := by
    intro definition member
    exact tail.fresh available member
  rw [List.foldl_append, protocol_invoke_foldl_other observations actions helpers _ after signature different]

theorem protocol_invoke_body {inventory : List Helper} (definitions : List CheckedProtocol)
    (linked : ProtocolDeclarationsLinked inventory [] definitions)
    (definition : CheckedProtocol) (member : definition ∈ definitions)
    (context : ProtocolContext) (self : Nat)
    (args : Values (Component (assignment F G)) definition.inputs) :
    invokeProtocol (definitions.foldl (extendProtocolTable observations actions helpers) [])
        definition.signature context self args =
      definition.denoteWith observations actions helpers
        (definitions.foldl (extendProtocolTable observations actions helpers) []) context self args := by
  obtain ⟨before, after, split⟩ := List.mem_iff_append.mp member
  rw [protocol_invoke_declaration observations actions helpers definitions linked before definition after split]
  unfold CheckedProtocol.denoteWith
  congr 1
  apply congrFun
  apply protocol_region_table_congr
  · intros; rfl
  · intros; rfl
  · intro signature used
    have allLinked := linked
    rw [split] at allLinked
    have tail := (ProtocolDeclarationsLinked.append _ [] before (definition :: after)).mp allLinked |>.2
    have usedRaw : signature ∈ definition.protocols := by
      simpa only [CheckedProtocol.protocols, ← definition.exactBody] using used
    have present : signature ∈ before.map CheckedProtocol.signature := by
      simpa using tail.2.2.1 signature usedRaw
    exact protocol_prefix_agrees observations actions helpers definitions linked before
      (definition :: after) split signature present

theorem protocol_invoke_body_view {inventory : List Helper} (definitions : List CheckedProtocol)
    (linked : ProtocolDeclarationsLinked inventory [] definitions)
    (definition : CheckedProtocol) (member : definition ∈ definitions)
    (body : Region protocolDialect definition.inputs definition.outputs)
    (exactRaw : definition.raw = body.erase) (context : ProtocolContext) (self : Nat)
    (args : Values (Component (assignment F G)) definition.inputs) :
    invokeProtocol (definitions.foldl (extendProtocolTable observations actions helpers) [])
        definition.signature context self args =
      (body.denote (participantMeaningWith observations actions helpers self
        (definitions.foldl (extendProtocolTable observations actions helpers) []) context)
        (maskValues self (context.mapScopes definition.inputScopes) args).get).bind
          (fun results => .done (maskValues self (context.mapScopes definition.outputScopes) results)) := by
  rw [protocol_invoke_body observations actions helpers definitions linked definition member]
  simp only [CheckedProtocol.denoteWith, definition.body_eq_of_raw body exactRaw]
  rfl

end GenericLinking

/-- Explicit full-signature transport avoids normalization of whole-unit admission. -/
theorem UnitPayload.protocol_body_view_as (payload : UnitPayload)
    (definition : CheckedProtocol) (member : definition ∈ payload.protocols)
    (signature : ProtocolSignature) (sameSignature : definition.signature = signature)
    (body : Region protocolDialect signature.inputs signature.outputs)
    (exactRaw : definition.raw = body.erase) (context : ProtocolContext) (self : Nat)
    (args : Values (Component (assignment F G)) signature.inputs) :
    invokeProtocol (payload.protocolTable F G) signature context self args =
      (body.denote (participantMeaning (payload.tables F G) self
        (payload.protocolTable F G) context)
        (maskValues self (context.mapScopes signature.inputScopes) args).get).bind
          (fun results => .done (maskValues self (context.mapScopes signature.outputScopes) results)) := by
  subst signature
  exact protocol_invoke_body_view (observedSites F G) observeAction (payload.tables F G)
    payload.protocols payload.protocolsLinked definition member body exactRaw context self args

end Zkc.Source.Structured
