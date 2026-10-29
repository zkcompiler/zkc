module

public import Zkc.Source.Structured.ProtocolLinking
public import Zkc.Source.Structured.NormalForm.Observation
public import Zkc.Source.Structured.OpenLaws

@[expose] public section

/-! Declaration closure laws over arbitrary carriers and effects, followed by
nominal-domain body and normalized-root laws. A declaration stores the actual
earlier table. Linking proves that extending it does not change any dependency
used by its body. Neither helper outcomes nor root process equations are assumed.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Zkc.Source.Structured

namespace ProtocolClosure
variable {V : Ty → Type} {I : PIR.Signature}
  (implementation : (definition : CheckedProtocol) → ProtocolTable V I →
    ProtocolFunction V I definition.signature)

def extend (captured : ProtocolTable V I) (definition : CheckedProtocol) : ProtocolTable V I :=
  ⟨definition.signature, implementation definition captured⟩ :: captured

theorem invoke_fold_other (table : ProtocolTable V I) (definitions : List CheckedProtocol)
    (signature : ProtocolSignature)
    (different : ∀ definition ∈ definitions, definition.name ≠ signature.name) :
    invokeProtocol (definitions.foldl (extend implementation) table) signature =
      invokeProtocol table signature := by
  induction definitions generalizing table with
  | nil => rfl
  | cons definition rest ih =>
    rw [List.foldl_cons, ih _ (fun d member => different d (List.mem_cons_of_mem _ member))]
    exact invokeProtocol_cons_other _ _ _ (different _ List.mem_cons_self)

theorem find_fold_other (table : ProtocolTable V I) (definitions : List CheckedProtocol)
    (name : String) (different : ∀ definition ∈ definitions, definition.name ≠ name) :
    (definitions.foldl (extend implementation) table).find?
        (fun entry => entry.signature.name == name) =
      table.find? (fun entry => entry.signature.name == name) := by
  induction definitions generalizing table with
  | nil => rfl
  | cons definition rest ih =>
    rw [List.foldl_cons, ih _ (fun d member => different d (List.mem_cons_of_mem _ member))]
    simp [extend, CheckedProtocol.signature, different _ List.mem_cons_self]

/-- Lookup retains the full signature and the exact captured implementation. -/
theorem declaration {inventory : List Helper} {definitions : List CheckedProtocol}
    (linked : ProtocolDeclarationsLinked inventory [] definitions)
    (before : List CheckedProtocol) (definition : CheckedProtocol) (after : List CheckedProtocol)
    (split : definitions = before ++ definition :: after) :
    (definitions.foldl (extend implementation) []).find?
        (fun entry => entry.signature.name == definition.name) =
      some ⟨definition.signature,
        implementation definition (before.foldl (extend implementation) [])⟩ := by
  rw [split] at linked ⊢
  have tail := (ProtocolDeclarationsLinked.append _ [] before (definition :: after)).mp linked |>.2
  have different : ∀ other ∈ after, other.name ≠ definition.name := by
    intro other member
    exact tail.2.2.2.fresh List.mem_cons_self member
  simp only [List.foldl_append, List.foldl_cons]
  rw [find_fold_other implementation _ after definition.name different]
  simp [extend, CheckedProtocol.signature]

theorem invoke_declaration {inventory : List Helper} {definitions : List CheckedProtocol}
    (linked : ProtocolDeclarationsLinked inventory [] definitions)
    (before : List CheckedProtocol) (definition : CheckedProtocol) (after : List CheckedProtocol)
    (split : definitions = before ++ definition :: after) :
    invokeProtocol (definitions.foldl (extend implementation) []) definition.signature =
      implementation definition (before.foldl (extend implementation) []) := by
  rw [split] at linked ⊢
  have tail := (ProtocolDeclarationsLinked.append _ [] before (definition :: after)).mp linked |>.2
  have different : ∀ other ∈ after, other.name ≠ definition.signature.name := by
    intro other member
    exact tail.2.2.2.fresh List.mem_cons_self member
  simp only [List.foldl_append, List.foldl_cons]
  rw [invoke_fold_other implementation _ after definition.signature different]
  exact invokeProtocol_cons_same _ _

theorem prefix_agrees {inventory : List Helper} {definitions : List CheckedProtocol}
    (linked : ProtocolDeclarationsLinked inventory [] definitions)
    (before after : List CheckedProtocol) (split : definitions = before ++ after)
    (signature : ProtocolSignature) (present : signature ∈ before.map CheckedProtocol.signature) :
    invokeProtocol (before.foldl (extend implementation) []) signature =
      invokeProtocol (definitions.foldl (extend implementation) []) signature := by
  rw [split] at linked ⊢
  have tail := (ProtocolDeclarationsLinked.append _ [] before after).mp linked |>.2
  have available : signature ∈ before.reverse.map CheckedProtocol.signature ++ [] := by
    simpa using present
  rw [List.foldl_append, invoke_fold_other implementation _ after signature
    (fun _ member => tail.fresh available member)]
end ProtocolClosure

section Domain
variable (model : DomainModel) {I : PIR.Signature}
  (observations : SiteObservations I)
  (actions : PIR.OperationInterpretation (participantInterfaceOn model.toCarriers) I)
  (helpers : Evaluation.ComponentTablesOn model.toCarriers I)
  (iterations : IterationObservations I)

/-- Only protocol dependencies change here; both sides use the same actual
closed/component helper table and the same iteration observations. -/
theorem protocol_region_protocols_congrOn
    (left right : ProtocolTable model.Value I) (self : Nat) (context : ProtocolContext)
    {inputs outputs : List Ty} (body : Region protocolDialect inputs outputs)
    (agree : ∀ signature ∈ body.erase.operations.flatMap ProtocolOp.protocols,
      invokeProtocol left signature = invokeProtocol right signature) :
    body.denote (participantMeaningWithOn model observations actions helpers self left context iterations) =
      body.denote (participantMeaningWithOn model observations actions helpers self right context iterations) := by
  apply Region.denote_congr
  intro op member
  funext args callbacks
  cases op with
  | protocolApply signature roles site =>
    simp only [protocolOperationWithOn, agree signature
      (List.mem_flatMap.mpr ⟨_, member, by simp [ProtocolOp.protocols]⟩)]
  | calculate | localCall | draw | statement | assemble => rfl
  | guard | exchange | restrict =>
    cases args with | cons value rest => cases rest; rfl
  | mark => cases args; rfl
  | «repeat» spec site =>
    cases args with | cons count values => rfl

/-- Full-signature invocation selects exactly the earlier declarations captured
when this declaration was installed, for any iteration interpretation. -/
theorem protocol_invoke_declarationOn {inventory : List Helper} (definitions : List CheckedProtocol)
    (linked : ProtocolDeclarationsLinked inventory [] definitions)
    (before : List CheckedProtocol) (definition : CheckedProtocol) (after : List CheckedProtocol)
    (split : definitions = before ++ definition :: after) :
    invokeProtocol (definitions.foldl
      (fun table definition => extendProtocolTableOn model observations actions helpers table definition iterations) [])
      definition.signature =
    definition.denoteWithOn model observations actions helpers
      (before.foldl (fun table definition =>
        extendProtocolTableOn model observations actions helpers table definition iterations) []) iterations :=
  ProtocolClosure.invoke_declaration
    (fun definition table => definition.denoteWithOn model observations actions helpers table iterations)
    linked before definition after split

/-- Linking lets the captured body use the complete immutable table because
all of its dependencies precede it. No recursive or arbitrary closure is added. -/
theorem protocol_invoke_bodyOn {inventory : List Helper} (definitions : List CheckedProtocol)
    (linked : ProtocolDeclarationsLinked inventory [] definitions)
    (definition : CheckedProtocol) (member : definition ∈ definitions)
    (context : ProtocolContext) (self : Nat)
    (args : Values (Component model.Value) definition.inputs) :
    invokeProtocol (definitions.foldl
      (fun table definition => extendProtocolTableOn model observations actions helpers table definition iterations) [])
      definition.signature context self args =
    definition.denoteWithOn model observations actions helpers
      (definitions.foldl (fun table definition =>
        extendProtocolTableOn model observations actions helpers table definition iterations) [])
      iterations context self args := by
  obtain ⟨before, after, split⟩ := List.mem_iff_append.mp member
  rw [protocol_invoke_declarationOn model observations actions helpers iterations definitions linked
    before definition after split]
  unfold CheckedProtocol.denoteWithOn
  congr 1
  apply congrFun
  apply protocol_region_protocols_congrOn
  intro signature used
  have allLinked := linked
  rw [split] at allLinked
  have tail := (ProtocolDeclarationsLinked.append _ [] before (definition :: after)).mp allLinked |>.2
  have usedRaw : signature ∈ definition.protocols := by
    simpa only [CheckedProtocol.protocols, ← definition.exactBody] using used
  have present : signature ∈ before.map CheckedProtocol.signature := by
    simpa using tail.2.2.1 signature usedRaw
  exact ProtocolClosure.prefix_agrees
    (fun definition table => definition.denoteWithOn model observations actions helpers table iterations)
    linked before (definition :: after) split signature present

end Domain

namespace Occurrence
/-- The actual helper closure fold used by `Occurrence.table`. -/
def helpers (model : DomainModel) (payload : UnitPayload) :
    Evaluation.ComponentTablesOn model.toCarriers (signature model.toCarriers) :=
  payload.definitions.foldl (Evaluation.ComponentTablesOn.extend model (.silent _)) ⟨[], []⟩

theorem invoke_body (model : DomainModel) (payload : UnitPayload)
    (definition : CheckedProtocol) (member : definition ∈ payload.protocols)
    (context : ProtocolContext) (self : Nat)
    (args : Values (Component model.Value) definition.inputs) :
    invokeProtocol (table model payload) definition.signature context self args =
      definition.denoteWithOn model (.silent _) actions (helpers model payload)
        (table model payload) iterations context self args :=
  protocol_invoke_bodyOn model (.silent _) actions (helpers model payload) iterations
    payload.protocols payload.protocolsLinked definition member context self args
end Occurrence

namespace NormalForm
/-- Normalize the actual program root, including both visibility masks. Helper
and callee equations remain explicit, input-pinned premises of normalization;
the root equation itself follows from admitted declaration lookup. -/
theorem normalize_program_occurrence {model : DomainModel}
    (program : Program) (sig : Signature) (role : Nat)
    (pattern : InputPattern program.payload.entry.inputs)
    (form : Form sig.laws sig.callees pattern.scope program.payload.entry.outputs)
    (normalized : normalize sig program.payload.entry.body role
      program.payload.entry.roles.length pattern = .ok form)
    (matched : form.CallsMatch) (distinct : RosterDistinct {} role program.payload.entry.roles.length)
    (results : LawResults model sig.laws)
    (processes : CalleeProcesses model sig.callees (Occurrence.signature model.toCarriers))
    (inputs : Values (Component model.Value) program.payload.entry.inputs)
    (binders : Binders model pattern.scope)
    (environment : maskValues role program.payload.entry.inputScopes inputs = pattern.environment model binders)
    (lawsHold : LawsHold (Occurrence.helpers model program.payload) results (pattern.environment model binders))
    (calleesHold : CalleesHold (Occurrence.table model program.payload) processes (pattern.environment model binders)) :
    Occurrence.participant model program role inputs =
      (form.denoteOn model Occurrence.actions (Occurrence.helpers model program.payload) results {}
        (runsAtOn model Occurrence.actions Occurrence.iterations (Occurrence.helpers model program.payload)
          (Occurrence.table model program.payload) {} role) processes binders).bind fun values =>
            .done (maskValues role program.payload.entry.outputScopes values) := by
  rw [Occurrence.participant, Occurrence.invoke_body model program.payload _ program.payload.entry_mem]
  simpa only [ProtocolContext.mapScopes_root, id_eq] using
    normalize_checkedProtocol_soundOn Occurrence.actions Occurrence.iterations
    (Occurrence.helpers model program.payload) (Occurrence.table model program.payload) {}
    program.payload.entry sig role pattern form normalized matched distinct results processes inputs binders
    (by simpa [ProtocolContext.mapScopes] using environment) lawsHold calleesHold
end NormalForm

end Zkc.Source.Structured
