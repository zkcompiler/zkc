module

public import Zkc.Construction.ConnectionApplications
public import Zkc.Source.Structured.InputVisibility

@[expose] public section

/-! Finite source templates for linked component applications. A template owns
an exact declaration index, complete nominal signature, role, input pattern and
pins. Each checked body may refer only to the earlier finite library. Helper
calls use the payload's unchanged tables. No entry contains a process equation
or a semantic callback. Target placement remains a separate connection check.
-/
set_option autoImplicit false
namespace Zkc.Construction.ConnectionLibrary
open Zkc.Source Zkc.Source.Structured NormalForm InputVisibility

/-- The actual source body is normalized once against the earlier library.
Only finite syntax checks and declaration membership are stored. -/
structure SourceTemplate (payload : UnitPayload) (callees : List CalleeKey) where
  declaration : Fin payload.protocols.length
  role : Nat
  roleValid : role < payload.protocols[declaration].roles.length
  pattern : InputPattern payload.protocols[declaration].inputs
  pins : List (Option Nat)
  visible : patternVisible role pattern payload.protocols[declaration].inputScopes = true
  inputScopes : scopesBounded payload.protocols[declaration].roles.length
    payload.protocols[declaration].inputScopes = true
  outputScopes : scopesBounded payload.protocols[declaration].roles.length
    payload.protocols[declaration].outputScopes = true
  form : Form [] callees pattern.scope payload.protocols[declaration].outputs
  normalized : normalize
      { strict := true, names := true, kept := payload.definitions.map CheckedDefinition.helper,
        callees := callees }
      payload.protocols[declaration].body role payload.protocols[declaration].roles.length pattern = .ok form
  matched : form.CallsMatch

abbrev SourceTemplate.source {payload : UnitPayload} {callees : List CalleeKey}
    (template : SourceTemplate payload callees) : CheckedProtocol := payload.protocols[template.declaration]

abbrev SourceTemplate.key {payload : UnitPayload} {callees : List CalleeKey}
    (template : SourceTemplate payload callees) : CalleeKey :=
  ⟨template.source.signature, template.role, template.pattern, template.pins⟩

/-- Build only from finite declaration and normalization checks. The source
index fixes the body and full signature before any target placement is tried. -/
def SourceTemplate.build (payload : UnitPayload) (callees : List CalleeKey)
    (declaration : Fin payload.protocols.length) (role : Nat)
    (pattern : InputPattern payload.protocols[declaration].inputs) (pins : List (Option Nat) := []) :
    Except String (SourceTemplate payload callees) := by
  by_cases roleValid : role < payload.protocols[declaration].roles.length
  · by_cases visible : patternVisible role pattern payload.protocols[declaration].inputScopes = true
    · by_cases inputScopes : scopesBounded payload.protocols[declaration].roles.length
          payload.protocols[declaration].inputScopes = true
      · by_cases outputScopes : scopesBounded payload.protocols[declaration].roles.length
            payload.protocols[declaration].outputScopes = true
        · cases normalized : normalize
              { laws := [], strict := true, names := true,
                kept := payload.definitions.map CheckedDefinition.helper, callees := callees }
              payload.protocols[declaration].body role payload.protocols[declaration].roles.length pattern with
          | error reason => exact .error reason
          | ok form =>
            by_cases matched : form.CallsMatch
            · exact .ok {
                declaration := declaration
                role := role
                roleValid := roleValid
                pattern := pattern
                pins := pins
                visible := visible
                inputScopes := inputScopes
                outputScopes := outputScopes
                form := form
                normalized := normalized
                matched := matched }
            · exact .error "connection-library-call-signature"
        · exact .error "connection-library-output-scopes"
      · exact .error "connection-library-input-scopes"
    · exact .error "connection-library-input-visibility"
  · exact .error "connection-library-role"

/-- Extension is finite and acyclic. Multiple application sites refer to the
same key and checked body; runtime repeat counts never extend the library. -/
inductive Library (payload : UnitPayload) : List CalleeKey → Type 1 where
  | empty : Library payload []
  | extend {callees : List CalleeKey} (earlier : Library payload callees)
      (template : SourceTemplate payload callees) : Library payload (template.key :: callees)

/-- Presented bodies, using the exact shared helper and protocol tables. -/
def Library.processes {payload : UnitPayload} {callees : List CalleeKey}
    (library : Library payload callees) (model : DomainModel) :
    CalleeProcesses model callees (Occurrence.signature model.toCarriers) :=
  match library with
  | .empty => noCallees model _
  | .extend earlier template => fun callee context binders =>
      Fin.cases
        (fun binders => template.form.denoteOn model Occurrence.actions (Occurrence.helpers model payload)
          (LawResults.empty model) context
          (runsAtOn model Occurrence.actions Occurrence.iterations (Occurrence.helpers model payload)
            (Occurrence.table model payload) context template.role)
          (earlier.processes model) binders)
        (fun index binders => earlier.processes model index context binders) callee binders

/-- A finite selection retains the checked body and its exact earlier library
by reference. It does not carry a denotation or a semantic callback. -/
structure Entry (payload : UnitPayload) (key : CalleeKey) where
  earlierKeys : List CalleeKey
  earlier : Library payload earlierKeys
  template : SourceTemplate payload earlierKeys
  key_eq : template.key = key

def Library.entry {payload : UnitPayload} {callees : List CalleeKey}
    (library : Library payload callees) : (callee : Fin callees.length) →
    Entry payload (calleeAt callees callee) :=
  match library with
  | .empty => fun callee => callee.elim0
  | .extend earlier template => fun callee =>
      Fin.cases ⟨_, earlier, template, rfl⟩ (fun index => earlier.entry index) callee

/-- Meaning obtained from the selected syntax and its earlier checked table. -/
def Entry.process {payload : UnitPayload} {key : CalleeKey} (entry : Entry payload key)
    (model : DomainModel) (context : ProtocolContext)
    (binders : Binders model key.pattern.scope) :
    PIR.Process (Occurrence.signature model.toCarriers) (Values (Component model.Value) key.signature.outputs) := by
  rcases entry with ⟨keys, earlier, template, same⟩
  cases same
  exact (Library.extend earlier template).processes model 0 context binders

/-- The selected checked form, transported along the exact nominal key. -/
def Entry.form {payload : UnitPayload} {key : CalleeKey} (entry : Entry payload key) :
    Form [] entry.earlierKeys key.pattern.scope key.signature.outputs := by
  rcases entry with ⟨keys, earlier, template, same⟩
  cases same
  exact template.form

theorem Entry.process_form {payload : UnitPayload} {key : CalleeKey} (entry : Entry payload key)
    (model : DomainModel) (context : ProtocolContext) (binders : Binders model key.pattern.scope) :
    entry.process model context binders = entry.form.denoteOn model Occurrence.actions
      (Occurrence.helpers model payload) (LawResults.empty model) context
      (runsAtOn model Occurrence.actions Occurrence.iterations (Occurrence.helpers model payload)
        (Occurrence.table model payload) context key.role) (entry.earlier.processes model) binders := by
  rcases entry with ⟨keys, earlier, template, same⟩
  cases same
  rfl

/-- Lookup shares exactly the same template body and helper/protocol tables as
the full library. Every call site therefore uses one checked reference. -/
theorem Library.processes_entry {payload : UnitPayload} {callees : List CalleeKey}
    (library : Library payload callees) (callee : Fin callees.length)
    (model : DomainModel) (context : ProtocolContext)
    (binders : Binders model (calleeAt callees callee).pattern.scope) :
    library.processes model callee context binders = (library.entry callee).process model context binders := by
  induction library with
  | empty => exact callee.elim0
  | extend earlier template ih =>
    refine Fin.cases ?_ (fun index => ?_) callee binders
    · intro binders
      rfl
    · intro binders
      exact ih index binders

/-- Linking and the checked templates discharge CalleesHold for every caller
input tuple and every permitted pin assignment, including inside repeats. -/
theorem Library.holds {payload : UnitPayload} {callees : List CalleeKey}
    (library : Library payload callees) (model : DomainModel) {types : List Ty}
    (inputs : Values (Component model.Value) types) :
    CalleesHold (Occurrence.table model payload) (library.processes model) inputs := by
  induction library generalizing types with
  | empty => exact noCallees_hold _ _
  | @extend callees earlier template ih =>
    intro callee
    refine Fin.cases ?_ (fun index => ?_) callee
    · intro context binders others _pinned distinct
      change Binders model template.pattern.scope at binders
      change Values (Component model.Value) template.pattern.absentTypes at others
      change RosterDistinct context template.role template.source.roles.length at distinct
      change invokeProtocol (Occurrence.table model payload) template.source.signature context
        (context.roles template.role) (template.pattern.fill model binders others) = _
      have linked := Occurrence.invoke_body model payload template.source (List.getElem_mem _)
        context (context.roles template.role) (template.pattern.fill model binders others)
      have inputMask : maskValues (context.roles template.role) (context.mapScopes template.source.inputScopes)
          (template.pattern.fill model binders others) = template.pattern.environment model binders :=
        (mask_context distinct _ template.inputScopes _).trans
          (mask_fill model _ _ _ template.visible binders others)
      have body := normalize_checkedProtocol_soundOn Occurrence.actions Occurrence.iterations
        (Occurrence.helpers model payload) (Occurrence.table model payload) context template.source
        {strict := true, names := true, kept := payload.definitions.map CheckedDefinition.helper, callees := callees}
        template.role template.pattern template.form template.normalized template.matched distinct
        (LawResults.empty model) (earlier.processes model) _ binders inputMask (LawsHold.empty _ _) (ih _)
      apply linked.trans
      apply body.trans
      congr 1
      funext values
      congr 1
      exact (mask_context distinct _ template.outputScopes values).trans
        (staticMask_identity _ _ values).symm
    · exact ih inputs index

/-- A finite source-keyed selection. An unselected signature can participate in
normalization but cannot be applied by the structural engine. -/
inductive Selection (definitions : List CheckedDefinition) (callees : List CalleeKey) where
  | unselected
  | selected (payload : UnitPayload) (same : payload.definitions = definitions)
      (library : Library payload callees)

/-- Internal interpretation of a finite selection. Actual roots discharge this
by reflexivity from their admitted payload and library, never by a callback. -/
def Selection.Meaning {definitions : List CheckedDefinition} {callees : List CalleeKey}
    (selection : Selection definitions callees) (model : DomainModel)
    (tables : Tables model (Occurrence.signature model.toCarriers))
    (protocols : ProtocolTable model.Value (Occurrence.signature model.toCarriers))
    (processes : CalleeProcesses model callees (Occurrence.signature model.toCarriers)) : Prop :=
  match selection with
  | .unselected => True
  | .selected payload _ library => tables = Occurrence.helpers model payload ∧
      protocols = Occurrence.table model payload ∧ processes = library.processes model

structure Bundle (payload : UnitPayload) where
  keys : List CalleeKey
  library : Library payload keys

def Bundle.empty (payload : UnitPayload) : Bundle payload := ⟨[], .empty⟩

end Zkc.Construction.ConnectionLibrary
