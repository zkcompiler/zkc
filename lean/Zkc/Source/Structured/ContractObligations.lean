module

public import Zkc.Source.Structured.ContractApplication
public import Zkc.Source.Structured.ContractCalls

@[expose] public section

/-! Property-neutral selected requests. Clause kinds do not choose hypotheses,
quantifiers, security notions or bad events. Local mathematical facts and formula
domains feed exact source association; call requests cover the actual tree.
An inventory alone proves no execution, probability or security property. -/
set_option autoImplicit false
namespace Zkc.Source.Structured

variable {snapshot : Snapshot} {imported : Imported snapshot} {owner : ContractBinding imported}
  {F G : Type} [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]
  {environment : RelationEnvironment imported F G} {invocation : InvocationCoordinate}

abbrev ContractBoundaryValues (owner : ContractBinding imported) (F G : Type) :=
  BoundaryValuation (assignment F G) owner.protocol.inputs owner.protocol.outputs

/-- Selection is from the retained owner and clause, including the exact
residual application when selected. A missing residual cannot be fabricated. -/
inductive ClauseApplication (owner : ContractBinding imported) where
  | subject (index : Fin owner.contract.clauses.length)
  | residual (index : Fin owner.contract.clauses.length) (application : RelationApplication)
      (selected : (owner.clause index).residual = some application)

def ClauseApplication.application (selection : ClauseApplication owner) : RelationApplication :=
  match selection with
  | .subject index => (owner.clause index).subject
  | .residual _ application _ => application

structure SelectedApplication (owner : ContractBinding imported) (F G : Type)
    [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]
    (environment : RelationEnvironment imported F G) where
  selection : ClauseApplication owner
  interpreted : InterpretedApplication owner selection.application F G environment

def ContractInterpretation.select (interpretation : ContractInterpretation owner F G environment)
    (selection : ClauseApplication owner) : SelectedApplication owner F G environment :=
  match selection with
  | .subject index => ⟨.subject index, interpretation.subjects index⟩
  | .residual index application selected =>
    ⟨.residual index application selected, interpretation.residuals index application selected⟩

/-- An exact ordered read, using one shared owner/invocation assignment. This is
a local mathematical use; process consumers instantiate its boundary with the
actual ComponentInput.boundary inside their returned observation. -/
structure ApplicationUse (selected : SelectedApplication owner F G environment)
    (context : ProtocolContext) (boundary : ContractBoundaryValues owner F G)
    (assignments : LogicalAssignments (assignment F G) owner invocation) where
  arguments : Values (assignment F G) selected.interpreted.binding.relation.declaration.inputs
  read : selected.interpreted.binding.read context boundary assignments = some arguments

namespace ApplicationUse
variable {selected : SelectedApplication owner F G environment} {context : ProtocolContext}
  {boundary : ContractBoundaryValues owner F G}
  {assignments : LogicalAssignments (assignment F G) owner invocation}

def Predicate (use : ApplicationUse selected context boundary assignments) : Prop :=
  selected.interpreted.interpretation.Predicate use.arguments

/-- Both fields are used by equivalence. A false domain cannot translate any
actual use. Opaque uses retrieve their one experiment-owned interpretation. -/
structure Translation (use : ApplicationUse selected context boundary assignments) : Prop where
  law : selected.interpreted.interpretation.FormulaLaw
  domain : selected.interpreted.interpretation.Domain use.arguments

theorem equivalence (use : ApplicationUse selected context boundary assignments)
    (translation : use.Translation) :
    selected.interpreted.Holds context boundary assignments ↔ use.Predicate := by
  constructor
  · rintro ⟨arguments, read, holds⟩
    have same : arguments = use.arguments := Option.some.inj (read.symm.trans use.read)
    subst arguments
    exact (selected.interpreted.interpretation.holds_iff_predicate translation.law _ translation.domain).mp holds
  · intro fact
    exact ⟨use.arguments, use.read,
      (selected.interpreted.interpretation.holds_iff_predicate translation.law _ translation.domain).mpr fact⟩

end ApplicationUse

/-- An external terminal names typed parameter/witness/boundary sources and
actual output selectors. Its meaning is explicit and is never called a retained
source clause. Nonempty outputs prevent a terminal with no observation. Choosing
`meaning := fun _ _ => True` proves only availability of the selected reads;
neither this record nor its inventory asserts a security property. -/
structure ExternalTerminal (owner : ContractBinding imported) (F G : Type) where
  parameterTypes : List Ty
  parameters : Values (AssignmentSource (assignment F G) owner) parameterTypes
  outputTypes : List Ty
  nonempty : outputTypes ≠ []
  outputs : Values (fun type => { selector : BoundarySelector owner.protocol.signature type //
    selector.port.direction = .output }) outputTypes
  meaning : Values (assignment F G) parameterTypes → Values (assignment F G) outputTypes → Prop

namespace ExternalTerminal

def readParameters (context : ProtocolContext) (boundary : ContractBoundaryValues owner F G)
    (assignments : LogicalAssignments (assignment F G) owner invocation) :
    {types : List Ty} → Values (AssignmentSource (assignment F G) owner) types → Values (Component (assignment F G)) types
  | _, .nil => .nil
  | _, .cons source rest => .cons (source.read context boundary assignments)
      (readParameters context boundary assignments rest)

def readOutputs (context : ProtocolContext) (boundary : ContractBoundaryValues owner F G) :
    {types : List Ty} → Values (fun type => { selector : BoundarySelector owner.protocol.signature type //
      selector.port.direction = .output }) types → Values (Component (assignment F G)) types
  | _, .nil => .nil
  | _, .cons selector rest => .cons (selector.val.read context boundary) (readOutputs context boundary rest)

def Holds (terminal : ExternalTerminal owner F G) (context : ProtocolContext)
    (boundary : ContractBoundaryValues owner F G)
    (assignments : LogicalAssignments (assignment F G) owner invocation) : Prop :=
  ∃ parameters outputs,
    RoleFamily.sequence (readParameters context boundary assignments terminal.parameters) = some parameters ∧
    RoleFamily.sequence (readOutputs context boundary terminal.outputs) = some outputs ∧
    terminal.meaning parameters outputs

omit [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- A terminal must observe at least one actual output. No interpretation or
logical assignment can close it on a stopped application outcome. -/
theorem not_holds_stopped (terminal : ExternalTerminal owner F G) {Γ : List Ty}
    (call : CheckedApplication owner Γ) (context : ProtocolContext) (self : Nat)
    (environment : Environment (Component (assignment F G)) Γ) (reason : PIR.Stop)
    (assignments : LogicalAssignments (assignment F G) owner invocation) :
    ¬ terminal.Holds (context.enter call.site call.roles)
      (call.boundaryOfOutcome context self environment (.stopped reason)) assignments := by
  rcases terminal with ⟨parameterTypes, parameters, outputTypes, nonempty, outputs, meaning⟩
  cases outputs with
  | nil => exact False.elim (nonempty rfl)
  | cons selector rest =>
    rintro ⟨_, _, _, outputRead, _⟩
    have absent : selector.val.read (context.enter call.site call.roles)
        (call.boundaryOfOutcome context self environment (.stopped reason)) = none := by
      cases selected : selector.val.port with
      | input ref =>
        have output := selector.property
        rw [selected] at output
        cases output
      | output ref =>
        exact call.boundaryOfOutcome_stopped_output context self environment reason selector.val ref selected
    simp only [readOutputs, absent, RoleFamily.sequence] at outputRead
    cases outputRead

end ExternalTerminal

/-- Polarity belongs to the property request. In particular an input clause may
be refuted in a false-claim experiment instead of assumed as a hypothesis. -/
inductive RequestPolarity where
  | assertion | refutation

def RequestPolarity.apply : RequestPolarity → Prop → Prop
  | .assertion, proposition => proposition
  | .refutation, proposition => ¬ proposition

inductive ContractRequest (owner : ContractBinding imported) (F G : Type)
    [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]
    (environment : RelationEnvironment imported F G) (invocation : InvocationCoordinate)
    (context : ProtocolContext) (boundary : ContractBoundaryValues owner F G)
    (assignments : LogicalAssignments (assignment F G) owner invocation) where
  | relation (selected : SelectedApplication owner F G environment)
      (use : ApplicationUse selected context boundary assignments) (polarity : RequestPolarity)
  | terminal (terminal : ExternalTerminal owner F G)

namespace ContractRequest
variable {context : ProtocolContext} {boundary : ContractBoundaryValues owner F G}
  {assignments : LogicalAssignments (assignment F G) owner invocation}

def Proof : ContractRequest owner F G environment invocation context boundary assignments → Prop
  | .relation _ use polarity => use.Translation ∧ polarity.apply use.Predicate
  | .terminal external => external.Holds context boundary assignments

def Meaning : ContractRequest owner F G environment invocation context boundary assignments → Prop
  | .relation selected _ polarity => polarity.apply (selected.interpreted.Holds context boundary assignments)
  | .terminal external => external.Holds context boundary assignments

/-- Local mathematical evidence is translated through the actual formula
invocation/read. No final whole-process theorem is accepted by this rule. -/
theorem resolve (request : ContractRequest owner F G environment invocation context boundary assignments)
    (proof : request.Proof) : request.Meaning := by
  cases request with
  | relation selected use polarity =>
    rcases proof with ⟨translation, fact⟩
    cases polarity with
    | assertion => exact (use.equivalence translation).mpr fact
    | refutation => exact fun holds => fact ((use.equivalence translation).mp holds)
  | terminal => exact proof

end ContractRequest

/-- A nonempty selected request tree. There is no auto-true terminal or empty
property constructor. Additional residual/terminal requests remain explicit. -/
inductive ContractRequests (owner : ContractBinding imported) (F G : Type)
    [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]
    (environment : RelationEnvironment imported F G) (invocation : InvocationCoordinate)
    (context : ProtocolContext) (boundary : ContractBoundaryValues owner F G)
    (assignments : LogicalAssignments (assignment F G) owner invocation) where
  | one (request : ContractRequest owner F G environment invocation context boundary assignments)
  | both (left right : ContractRequests owner F G environment invocation context boundary assignments)

namespace ContractRequests
variable {context : ProtocolContext} {boundary : ContractBoundaryValues owner F G}
  {assignments : LogicalAssignments (assignment F G) owner invocation}

def Proof : ContractRequests owner F G environment invocation context boundary assignments → Prop
  | .one request => request.Proof
  | .both left right => left.Proof ∧ right.Proof

def Meaning : ContractRequests owner F G environment invocation context boundary assignments → Prop
  | .one request => request.Meaning
  | .both left right => left.Meaning ∧ right.Meaning

theorem resolve (requests : ContractRequests owner F G environment invocation context boundary assignments)
    (proof : requests.Proof) : requests.Meaning := by
  induction requests with
  | one request => exact request.resolve proof
  | both left right ihLeft ihRight => exact ⟨ihLeft proof.1, ihRight proof.2⟩

end ContractRequests

/-- Selected local leaves and exhaustive lexical call obligations are separate.
The consumer supplies local call requests; enumeration never proves them. This
record does not certify a security property or assert undeclared intentions. -/
structure SelectedObligations {context : ProtocolContext} {boundary : ContractBoundaryValues owner F G}
    {assignments : LogicalAssignments (assignment F G) owner invocation}
    (requests : ContractRequests owner F G environment invocation context boundary assignments)
    (CallRequest : CallOccurrence owner.protocol.body → Sort _) where
  localRequests : requests.Proof
  calls : CallObligations owner.protocol.body CallRequest

end Zkc.Source.Structured
