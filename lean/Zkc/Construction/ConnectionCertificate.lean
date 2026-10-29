module

public import Zkc.Construction.ConnectionLibrary
public import Zkc.Construction.ConnectionTargetExtent
public import Zkc.Construction.ConnectionApplicationFrame
public import Zkc.Construction.ConnectionProjectedLoops
public import Zkc.Construction.ConnectionProjectedContinuation
public import Zkc.Construction.ConnectionRepeatSupport
public import Zkc.Construction.ConnectionComputation
public import Zkc.Construction.ConnectionPresence
public import Zkc.Construction.ConnectionHelpers
public import Zkc.Construction.ConnectionHelperProjection
public import Zkc.Construction.ConnectionHelperCalculation
public import Zkc.Construction.ConnectionObservationPrefix
public import Zkc.Construction.ConnectionActionSupport
public import Zkc.Construction.ConnectionContext
public import Zkc.Construction.ConnectionMasking
public import Zkc.Construction.OriginalFrameRelations

@[expose] public section

/-! A finite, intrinsically checked alignment derivation for
connections across both profiles and roles. Indices fix the actual source form and actual Domain.View block.
Constructors contain only finite static checks and smaller derivations. There
is no root semantic equation, Simulation, helper law or successful-value premise
in a constructor. Helpers carry finite exact declaration bindings. Symbolic
source stacks, public and private queries, delivery and observation share the
same derivation. Symbolic repeats check one normalized body independently of
the runtime count and retain ordered occurrence coordinates and reached history.
Their carried state supports source-owned private projections. Finite selected-library
applications compose their checked flat callee slice with the caller continuation.

The output location row is fixed before proposal and includes every component.
The root's role/profile schema and reached-source route coverage are separate
obligations; this module neither weakens nor replaces them. -/
set_option autoImplicit false
namespace Zkc.Construction.ConnectionCertificate
open Zkc.Source Zkc.Source.Structured NormalForm ConnectionFrame ConnectionComputation

abbrev Block := (model : DomainModel) → Domain.View.Block model.toCarriers

def receiveLayout {scope : Scope} (layout : Layout scope) (ty : Ty) : Layout (.value ty :: scope) :=
  layout.map (Cell.rename .there) ++ [.data (.present (.var .here))]

/-- The source guard's exact nominal equality operation. -/
def equalityCalculation {ty : Ty} : Equality ty → Calculation
  | .field domain => .fieldEqual domain
  | .group domain => .groupEqual domain
  | .index => .indexEqual
  | .boolean => .booleanEqual

def equalityTerm {scope : Scope} {ty : Ty} (equality : Equality ty)
    (left right : Term [] scope ty) : Term [] scope .boolean :=
  match equality with
  | .field domain => .calc (.fieldEqual domain) rfl (.cons left (.cons right .nil)) .here
  | .group domain => .calc (.groupEqual domain) rfl (.cons left (.cons right .nil)) .here
  | .index => .calc .indexEqual rfl (.cons left (.cons right .nil)) .here
  | .boolean => .calc .booleanEqual rfl (.cons left (.cons right .nil)) .here

theorem equalityTerm_eval (model : DomainModel) {scope : Scope} {ty : Ty} (equality : Equality ty)
    (left right : Term [] scope ty) (binders : Binders model scope) :
    (equalityTerm equality left right).eval (LawResults.empty model) binders =
      @decide (left.eval (LawResults.empty model) binders = right.eval (LawResults.empty model) binders)
        (equality.decide model _ _) := by
  cases equality with
  | field => rfl
  | group => rfl
  | index => rfl
  | boolean =>
    change (left.eval (LawResults.empty model) binders == right.eval (LawResults.empty model) binders) = _
    cases left.eval (LawResults.empty model) binders <;>
      cases right.eval (LawResults.empty model) binders <;> rfl

/-- Finite guard operands: either a nominal comparison, or the original
Boolean condition normalized as equality to true. -/
inductive GuardReadback {scope : Scope} (layout : Layout scope) :
    {ty : Ty} → Equality ty → Term [] scope ty → Term [] scope ty → Nat → Type where
  | comparison {ty : Ty} (equality : Equality ty) (left right : Term [] scope ty) (reference : Nat)
      (checked : Readback layout (.cons (.present (equalityTerm equality left right)) .nil) [.data reference]) :
      GuardReadback layout equality left right reference
  | boolean (condition : Term [] scope .boolean) (reference : Nat)
      (checked : Readback layout (.cons (.present condition) .nil) [.data reference]) :
      GuardReadback layout .boolean condition (.bool true) reference

theorem read_boolean {model : DomainModel} {scope : Scope} {layout : Layout scope}
    {binders : Binders model scope} {history : Domain.History model.toCarriers}
    {environment : Domain.Environment model.toCarriers} {term : Term [] scope .boolean} {reference : Nat}
    (checked : Readback layout (.cons (.present term) .nil) [.data reference])
    (related : Holds model binders history layout environment) :
    environment[reference]? = some (.data (.boolean (term.eval (LawResults.empty model) binders))) := by
  obtain ⟨actual, physical, present, encoded, read⟩ := checked.component related
  have same := Option.some.inj present
  rw [← same] at encoded
  exact read.trans (congrArg some (Option.some.inj encoded).symm)

theorem GuardReadback.read {model : DomainModel} {scope : Scope} {layout : Layout scope}
    {binders : Binders model scope} {history : Domain.History model.toCarriers}
    {environment : Domain.Environment model.toCarriers} {ty : Ty} {equality : Equality ty}
    {left right : Term [] scope ty} {reference : Nat}
    (checked : GuardReadback layout equality left right reference)
    (related : Holds model binders history layout environment) :
    environment[reference]? = some (.data (.boolean
      (@decide (left.eval (LawResults.empty model) binders = right.eval (LawResults.empty model) binders)
        (equality.decide model _ _)))) := by
  cases checked with
  | comparison equality left right reference checked =>
    rw [← equalityTerm_eval model equality left right binders]
    exact read_boolean checked related
  | boolean condition reference checked =>
    have read := read_boolean checked related
    have same : condition.eval (LawResults.empty model) binders =
        decide (condition.eval (LawResults.empty model) binders = true) := by
      cases condition.eval (LawResults.empty model) binders <;> rfl
    exact read.trans (congrArg (fun value => some (Domain.Value.data (carriers := model.toCarriers) (.boolean value))) same)

/-- The guard retains the exact expression whose physical cell it checked. -/
def GuardReadback.component {scope : Scope} {layout : Layout scope} {ty : Ty}
    {equality : Equality ty} {left right : Term [] scope ty} {reference : Nat} :
    GuardReadback layout equality left right reference → Comp [] scope .boolean
  | .comparison equality left right _ _ => .present (equalityTerm equality left right)
  | .boolean condition _ _ => .present condition

/-- Successful guards establish a second alias for the same physical Boolean.
The old expression remains available to later calculations and output readback. -/
def GuardReadback.refine {scope : Scope} {layout : Layout scope} {ty : Ty}
    {equality : Equality ty} {left right : Term [] scope ty} {reference : Nat}
    (checked : GuardReadback layout equality left right reference) : Layout scope :=
  layout.set reference (.guarded checked.component)

theorem GuardReadback.refined {model : DomainModel} {scope : Scope} {layout : Layout scope}
    {binders : Binders model scope} {history : Domain.History model.toCarriers}
    {environment : Domain.Environment model.toCarriers} {ty : Ty} {equality : Equality ty}
    {left right : Term [] scope ty} {reference : Nat}
    (checked : GuardReadback layout equality left right reference)
    (related : Holds model binders history layout environment)
    (success : left.eval (LawResults.empty model) binders = right.eval (LawResults.empty model) binders) :
    Holds model binders history checked.refine environment := by
  have physical : environment[reference]? = some (.data (.boolean true)) := by
    simpa only [success, decide_true] using checked.read related
  apply related.set reference (.guarded checked.component) physical
  refine ⟨?_, rfl⟩
  cases checked with
  | comparison equality left right reference read =>
    obtain ⟨actual, value, present, encoded, found⟩ := read.component related
    have same := Option.some.inj (found.symm.trans physical)
    exact ⟨actual, present, encoded.trans (congrArg some same)⟩
  | boolean condition reference read =>
    obtain ⟨actual, value, present, encoded, found⟩ := read.component related
    have same := Option.some.inj (found.symm.trans physical)
    exact ⟨actual, present, encoded.trans (congrArg some same)⟩

def historyPolicy (profile : Profile) (selector : Option Nat) : Bool :=
  match profile, selector with
  | .plain, none | .fiatShamir _, some _ => true
  | _, _ => false

inductive HistoryReadback {scope : Scope} (layout : Layout scope) (suite : String) : Option Nat → Type where
  | plain : HistoryReadback layout suite none
  | transcript (reference : Nat) (checked : layout[reference]? = some (.history suite)) :
      HistoryReadback layout suite (some reference)

def HistoryAt {model : DomainModel} (suite : String) (environment : Domain.Environment model.toCarriers)
    (history : Domain.History model.toCarriers) : Option Nat → Prop
  | none => True
  | some reference => environment[reference]? = some (.transcript suite history)

/-- A finite profile return row forces the exact history-location policy. -/
theorem historyLocation_of_profile {model : DomainModel} {context : Context}
    {data references : List Nat} {selector : Option Nat} {environment : Domain.Environment model.toCarriers}
    {history : Domain.History model.toCarriers}
    (profile : Original.profileReferences context data selector = some references)
    (read : HistoryAt context.suite environment history selector) :
    Original.HistoryLocation context selector environment history := by
  cases selected : context.profile with
  | plain =>
    cases selector with
    | none => simp [Original.HistoryLocation, selected]
    | some => simp [Original.profileReferences, selected] at profile
  | fiatShamir replacement =>
    cases selector with
    | none => simp [Original.profileReferences, selected] at profile
    | some reference =>
      simpa [HistoryAt, Original.HistoryLocation, Context.suite, Context.replacement?, selected] using read

set_option linter.unusedVariables false in
inductive Alignment (routing : Original.Routing) :
    (context : ProtocolContext) → (definitions : List CheckedDefinition) → (callees : List CalleeKey) →
    {selection : ConnectionLibrary.Selection definitions callees} →
    (out : List Ty) → (role : Nat) → (scopes : List (List Nat)) →
    (outputs : List Original.Location) → (history : Option Nat) →
    {scope : Scope} → ScopedFrames scope → Layout scope → Form [] callees scope out → Block → Type 1 where
  | done {context : ProtocolContext} {definitions : List CheckedDefinition}
      {callees : List CalleeKey} {selection : ConnectionLibrary.Selection definitions callees} {out : List Ty} {role : Nat} {scopes : List (List Nat)}
      {outputs : List Original.Location} {history : Option Nat} {scope : Scope} {frames : ScopedFrames scope} {layout : Layout scope} {values : Values (Comp [] scope) out}
      (readback : Readback layout (mask role scopes values) outputs)
      (historyRead : HistoryReadback layout routing.context.suite history) :
      Alignment routing context definitions callees (selection := selection) out role scopes outputs history frames layout (.done values) (fun _ => Domain.View.empty)
  | halt {context : ProtocolContext} {definitions : List CheckedDefinition}
      {callees : List CalleeKey} {selection : ConnectionLibrary.Selection definitions callees} {out : List Ty} {role : Nat} {scopes : List (List Nat)}
      {outputs : List Original.Location} {history : Option Nat} {scope : Scope} {frames : ScopedFrames scope} {layout : Layout scope} (reason : PIR.Stop) :
      Alignment routing context definitions callees (selection := selection) out role scopes outputs history frames layout (.halt reason) (fun _ _ => .halt reason)
  | split {context : ProtocolContext} {definitions : List CheckedDefinition}
      {callees : List CalleeKey} {selection : ConnectionLibrary.Selection definitions callees} {out : List Ty} {role : Nat} {scopes : List (List Nat)}
      {outputs : List Original.Location} {history : Option Nat} {scope : Scope} {frames : ScopedFrames scope} {layout : Layout scope} {ty : Ty}
      (subject : Subject scope ty) {absent : Form [] callees scope out}
      {present : Form [] callees (.value ty :: scope) out} {target : Block}
      (absentBranch : Alignment routing context definitions callees (selection := selection) out role scopes outputs history frames
        (layout.map (Cell.absentAt subject)) absent target)
      (presentBranch : Alignment routing context definitions callees (selection := selection) out role scopes outputs history (frames.rename .there)
        (layout.map (Cell.presentAt subject)) present target) :
      Alignment routing context definitions callees (selection := selection) out role scopes outputs history frames layout
        (.split subject.comp absent present) target
  | splitAbsent {context : ProtocolContext} {definitions : List CheckedDefinition}
      {callees : List CalleeKey} {selection : ConnectionLibrary.Selection definitions callees} {out : List Ty} {role : Nat} {scopes : List (List Nat)}
      {outputs : List Original.Location} {history : Option Nat} {scope : Scope}
      {frames : ScopedFrames scope} {layout : Layout scope} {ty : Ty}
      {absent : Form [] callees scope out} {present : Form [] callees (.value ty :: scope) out} {target : Block}
      (presentMatched : present.CallsMatch)
      (tail : Alignment routing context definitions callees (selection := selection) out role scopes outputs history frames layout absent target) :
      Alignment routing context definitions callees (selection := selection) out role scopes outputs history frames layout
        (.split (.absent (ty := ty)) absent present) target
  | splitValue {context : ProtocolContext} {definitions : List CheckedDefinition}
      {callees : List CalleeKey} {selection : ConnectionLibrary.Selection definitions callees} {out : List Ty} {role : Nat} {scopes : List (List Nat)}
      {outputs : List Original.Location} {history : Option Nat} {scope : Scope}
      {frames : ScopedFrames scope} {layout : Layout scope} {ty : Ty}
      (value : Term [] scope ty)
      {absent : Form [] callees scope out} {present : Form [] callees (.value ty :: scope) out} {target : Block}
      (absentMatched : absent.CallsMatch)
      (tail : Alignment routing context definitions callees (selection := selection) out role scopes outputs history frames layout
        (ConnectionSubstitution.form present (ConnectionSubstitution.valueHead value)) target) :
      Alignment routing context definitions callees (selection := selection) out role scopes outputs history frames layout
        (.split (.present value) absent present) target
  | splitPresent {context : ProtocolContext} {definitions : List CheckedDefinition}
      {callees : List CalleeKey} {selection : ConnectionLibrary.Selection definitions callees} {out : List Ty} {role : Nat} {scopes : List (List Nat)}
      {outputs : List Original.Location} {history : Option Nat} {scope : Scope} {frames : ScopedFrames scope} {layout : Layout scope} {ty : Ty}
      (subject : Subject scope ty) {absent : Form [] callees scope out}
      {present : Form [] callees (.value ty :: scope) out} {target : Block}
      (reference : Nat) (checked : layout[reference]? = some (.data subject.comp))
      (absentMatch : absent.CallsMatch)
      (tail : Alignment routing context definitions callees (selection := selection) out role scopes outputs history (frames.rename .there)
        (layout.map (Cell.presentAt subject)) present target) :
      Alignment routing context definitions callees (selection := selection) out role scopes outputs history frames layout
        (.split subject.comp absent present) target
  | compute {context : ProtocolContext} {definitions : List CheckedDefinition}
      {callees : List CalleeKey} {selection : ConnectionLibrary.Selection definitions callees} {out : List Ty} {role : Nat} {scopes : List (List Nat)}
      {outputs : List Original.Location} {history : Option Nat} {scope : Scope} {frames : ScopedFrames scope} {layout : Layout scope}
      (operation : Calculation) (terms : Terms [] scope operation.op.arguments)
      {next : Form [] callees (.results operation.op.results :: scope) out} {rest : Block}
      (references : List Nat)
      (inputsData : operation.op.arguments.all Domain.dataType = true)
      (outputsData : operation.op.results.all Domain.dataType = true)
      (readback : Readback layout (components terms) (references.map Original.Location.data))
      (tail : Alignment routing context definitions callees (selection := selection) out role scopes outputs history (frames.rename .there)
        (resultsLayout layout operation.op.results) next rest) :
      Alignment routing context definitions callees (selection := selection) out role scopes outputs history frames layout
        (.compute operation.op (ConnectionCalculations.calculation_allowed operation) terms next)
        (fun model => Domain.View.sequence
          (Domain.View.calculation model operation references (operation.op.results.map ValueSort.data)) (rest model))
  | strictHelper {context : ProtocolContext} {definitions : List CheckedDefinition}
      {callees : List CalleeKey} {selection : ConnectionLibrary.Selection definitions callees} {out : List Ty} {role : Nat} {scopes : List (List Nat)}
      {outputs : List Original.Location} {history : Option Nat} {scope : Scope} {frames : ScopedFrames scope} {layout : Layout scope}
      (program : Program) (helper : Helper)
      (binding : ConnectionHelpers.Binding definitions helper program)
      (arguments : Terms [] scope helper.inputs)
      {next : Form [] callees (.results helper.outputs :: scope) out} {rest : Block}
      (references : List Nat)
      (inputsData : helper.inputs.all Domain.dataType = true)
      (outputsData : helper.outputs.all Domain.dataType = true)
      (readback : Readback layout (components arguments) (references.map Original.Location.data))
      (tail : Alignment routing context definitions callees (selection := selection) out role scopes outputs history (frames.rename .there)
        (resultsLayout layout helper.outputs) next rest) :
      Alignment routing context definitions callees (selection := selection) out role scopes outputs history frames layout (.strict helper arguments next)
        (fun model => Domain.View.sequence
          (Domain.View.helper model program helper.name references (helper.outputs.map ValueSort.data)) (rest model))
  | ownedHelper {context : ProtocolContext} {definitions : List CheckedDefinition}
      {callees : List CalleeKey} {selection : ConnectionLibrary.Selection definitions callees} {out : List Ty} {role : Nat} {scopes : List (List Nat)}
      {outputs : List Original.Location} {history : Option Nat} {scope : Scope} {frames : ScopedFrames scope} {layout : Layout scope}
      (owner : Nat) (program : Program) (helper : Helper)
      (binding : ConnectionHelpers.Binding definitions helper program)
      (arguments : Values (Comp [] scope) helper.inputs)
      {next : Form [] callees (.tuple helper.outputs :: scope) out} {rest : Block}
      (references : List Nat)
      (inputsData : helper.inputs.all Domain.dataType = true)
      (outputsData : helper.outputs.all Domain.dataType = true)
      (readback : Readback layout arguments (references.map Original.Location.data))
      (tail : Alignment routing context definitions callees (selection := selection) out role scopes outputs history (frames.rename .there)
        (tupleLayout layout helper.outputs) next rest) :
      Alignment routing context definitions callees (selection := selection) out role scopes outputs history frames layout (.owned owner helper arguments next)
        (fun model => Domain.View.sequence
          (Domain.View.helper model program helper.name references (helper.outputs.map ValueSort.data)) (rest model))
  | mathHelper {context : ProtocolContext} {definitions : List CheckedDefinition}
      {callees : List CalleeKey} {selection : ConnectionLibrary.Selection definitions callees} {out : List Ty} {role : Nat} {scopes : List (List Nat)}
      {outputs : List Original.Location} {history : Option Nat} {scope : Scope} {frames : ScopedFrames scope} {layout : Layout scope}
      (program : Program) (helper : Helper) (math : helper.kind = .math)
      (binding : ConnectionHelpers.Binding definitions helper program)
      (arguments : Values (Comp [] scope) helper.inputs)
      {next : Form [] callees (.tuple helper.outputs :: scope) out} {rest : Block}
      (references : List Nat)
      (inputsData : helper.inputs.all Domain.dataType = true)
      (outputsData : helper.outputs.all Domain.dataType = true)
      (readback : Readback layout arguments (references.map Original.Location.data))
      (tail : Alignment routing context definitions callees (selection := selection) out role scopes outputs history (frames.rename .there)
        (tupleLayout layout helper.outputs) next rest) :
      Alignment routing context definitions callees (selection := selection) out role scopes outputs history frames layout (.math helper arguments next)
        (fun model => Domain.View.sequence
          (Domain.View.helper model program helper.name references (helper.outputs.map ValueSort.data)) (rest model))
  | projectionHelper {context : ProtocolContext} {definitions : List CheckedDefinition}
      {callees : List CalleeKey} {selection : ConnectionLibrary.Selection definitions callees} {out : List Ty} {role : Nat} {scopes : List (List Nat)}
      {outputs : List Original.Location} {history : Option Nat} {scope : Scope} {frames : ScopedFrames scope} {layout : Layout scope}
      (definition : CheckedDefinition) (projection : ConnectionHelpers.Projection definitions definition)
      (arguments : Values (Comp [] scope) definition.inputs)
      {next : Form [] callees (.tuple definition.outputs :: scope) out} {target : Block}
      (nextMatched : next.CallsMatch)
      (tail : Alignment routing context definitions callees (selection := selection) out role scopes outputs history frames layout
        (ConnectionSubstitution.form next (ConnectionSubstitution.tupleHead (lookup arguments projection.positions))) target) :
      Alignment routing context definitions callees (selection := selection) out role scopes outputs history frames layout
        (.math definition.helper arguments next) target
  | inlineCalculation {context : ProtocolContext} {definitions : List CheckedDefinition}
      {callees : List CalleeKey} {selection : ConnectionLibrary.Selection definitions callees}
      {out : List Ty} {role : Nat} {scopes : List (List Nat)}
      {outputs : List Original.Location} {history : Option Nat} {scope : Scope}
      {frames : ScopedFrames scope} {layout : Layout scope}
      (definition : CheckedDefinition) (calculation : ConnectionHelpers.CalculationBody definitions definition)
      (arguments : Terms [] scope definition.inputs)
      {next : Form [] callees (.tuple definition.outputs :: scope) out} {target : Block}
      (nextMatched : next.CallsMatch)
      (tail : Alignment routing context definitions callees (selection := selection) out role scopes outputs history frames layout
        (ConnectionSubstitution.form next (ConnectionSubstitution.tupleHead (calculation.result arguments))) target) :
      Alignment routing context definitions callees (selection := selection) out role scopes outputs history frames layout
        (.math definition.helper (components arguments) next) target
  | inlineMissingCalculation {context : ProtocolContext} {definitions : List CheckedDefinition}
      {callees : List CalleeKey} {selection : ConnectionLibrary.Selection definitions callees}
      {out : List Ty} {role : Nat} {scopes : List (List Nat)}
      {outputs : List Original.Location} {history : Option Nat} {scope : Scope}
      {frames : ScopedFrames scope} {layout : Layout scope}
      (definition : CheckedDefinition) (calculation : ConnectionHelpers.CalculationBody definitions definition)
      (arguments : Values (Comp [] scope) definition.inputs)
      (missing : anyAbsent (lookup arguments calculation.inputs) = true)
      {next : Form [] callees (.tuple definition.outputs :: scope) out} {target : Block}
      (nextMatched : next.CallsMatch)
      (tail : Alignment routing context definitions callees (selection := selection) out role scopes outputs history frames layout
        (ConnectionSubstitution.form next (ConnectionSubstitution.tupleHead (calculation.missingResult arguments))) target) :
      Alignment routing context definitions callees (selection := selection) out role scopes outputs history frames layout
        (.math definition.helper arguments next) target
  | calculation {context : ProtocolContext} {definitions : List CheckedDefinition}
      {callees : List CalleeKey} {selection : ConnectionLibrary.Selection definitions callees} {out : List Ty} {role : Nat} {scopes : List (List Nat)}
      {outputs : List Original.Location} {history : Option Nat} {scope : Scope} {frames : ScopedFrames scope} {layout : Layout scope} {form : Form [] callees scope out}
      (operation : Calculation) (total : operation.op.total = true)
      (terms : Terms [] scope operation.op.arguments) (references : List Nat)
      (inputsData : operation.op.arguments.all Domain.dataType = true)
      (outputsData : operation.op.results.all Domain.dataType = true)
      (readback : Readback layout (components terms) (references.map Original.Location.data))
      {rest : Block}
      (tail : Alignment routing context definitions callees (selection := selection) out role scopes outputs history frames
        (layout ++ cells (NormalForm.calculation operation.op total terms)) form rest) :
      Alignment routing context definitions callees (selection := selection) out role scopes outputs history frames layout form
        (fun model => Domain.View.sequence
          (Domain.View.calculation model operation references (operation.op.results.map ValueSort.data)) (rest model))
  | receive {context : ProtocolContext} {definitions : List CheckedDefinition}
      {callees : List CalleeKey} {selection : ConnectionLibrary.Selection definitions callees} {out : List Ty} {role : Nat} {scopes : List (List Nat)}
      {outputs : List Original.Location} {history : Option Nat} {scope : Scope} {frames : ScopedFrames scope} {layout : Layout scope} (ty : Ty) (site : String) (peer : Nat)
      {next : Form [] callees (.value ty :: scope) out} {rest : Block}
      (plain : routing.context.profile = .plain) (template : Template)
      (route : OccurrenceResolution.resolveStatic routing.snapshot routing.context
        (routing.context.message (qualifyProtocolSite context.applicationPrefix site)
          (context.roles peer) routing.self) frames.sites routing.messages = some template)
      (data : ty.isService = false)
      (tail : Alignment routing context definitions callees (selection := selection) out role scopes outputs history (frames.rename .there) (receiveLayout layout ty) next rest) :
      Alignment routing context definitions callees (selection := selection) out role scopes outputs history frames layout (.receive ty site peer next)
        (fun model => Domain.View.sequence
          (Domain.View.receive (qualifyProtocolSite context.applicationPrefix site)
            (qualifyProtocolSite context.applicationPrefix site) (routing.context.role (context.roles peer))
            ty [.data ty]) (rest model))
  | send {context : ProtocolContext} {definitions : List CheckedDefinition}
      {callees : List CalleeKey} {selection : ConnectionLibrary.Selection definitions callees} {out : List Ty} {role : Nat} {scopes : List (List Nat)}
      {outputs : List Original.Location} {history : Option Nat} {scope : Scope} {frames : ScopedFrames scope} {layout : Layout scope} (ty : Ty) (site : String) (peer : Nat)
      (value : Term [] scope ty) {next : Form [] callees scope out} {rest : Block}
      (reference : Nat) (readback : Readback layout (.cons (.present value) .nil) [.data reference])
      (plain : routing.context.profile = .plain) (template : Template)
      (route : OccurrenceResolution.resolveStatic routing.snapshot routing.context
        (routing.context.message (qualifyProtocolSite context.applicationPrefix site)
          routing.self (context.roles peer)) frames.sites routing.messages = some template)
      (tail : Alignment routing context definitions callees (selection := selection) out role scopes outputs history frames layout next rest) :
      Alignment routing context definitions callees (selection := selection) out role scopes outputs history frames layout (.send ty site peer value next)
        (fun model => Domain.View.sequence
          (Domain.View.send (qualifyProtocolSite context.applicationPrefix site)
            (qualifyProtocolSite context.applicationPrefix site) (routing.context.role (context.roles peer))
            reference []) (rest model))
  | observedSend {context : ProtocolContext} {definitions : List CheckedDefinition}
      {callees : List CalleeKey} {selection : ConnectionLibrary.Selection definitions callees} {out : List Ty} {role : Nat} {scopes : List (List Nat)}
      {outputs : List Original.Location} {history : Option Nat} {scope : Scope} {frames : ScopedFrames scope} {layout : Layout scope}
      (ty : Ty) (site : String) (peer : Nat) (value : Term [] scope ty)
      {next : Form [] callees scope out} {rest : Block}
      (replacement : Replacement) (profile : routing.context.profile = .fiatShamir replacement)
      {prepared : Layout scope} {preparation : Block}
      (preparationProof : CoordinatePrefix layout prepared preparation)
      (reference stateRef pathRef : Nat)
      (readback : Readback layout (.cons (.present value) .nil) [.data reference])
      (preparedReadback : Readback prepared (.cons (.present value) .nil) [.data reference])
      (stateRead : prepared[stateRef]? = some (.history routing.context.suite))
      (pathRead : prepared[pathRef]? = some (.coordinates frames.coordinates))
      (template : Template)
      (route : OccurrenceResolution.resolveStatic routing.snapshot routing.context
        (routing.context.message (qualifyProtocolSite context.applicationPrefix site)
          routing.self (context.roles peer)) frames.sites routing.messages = some template)
      (tail : Alignment routing context definitions callees (selection := selection) out role scopes outputs history frames
        (observedLayout prepared routing.context.suite) next rest) :
      Alignment routing context definitions callees (selection := selection) out role scopes outputs history frames layout (.send ty site peer value next)
        (fun model => match routing.mode with
          | .producer => Domain.View.sequence
              (Domain.View.send (qualifyProtocolSite context.applicationPrefix site)
                (qualifyProtocolSite context.applicationPrefix site) (routing.context.role (context.roles peer)) reference [])
              (preparationProof.prepend (fun model => Domain.View.sequence
                (Domain.View.observe routing.context routing.context.suite template stateRef reference pathRef
                  [.transcript routing.context.suite]) (rest model)) model)
          | .validator => preparationProof.prepend (fun model => Domain.View.sequence
              (Domain.View.observe routing.context routing.context.suite template stateRef reference pathRef
                [.transcript routing.context.suite]) (rest model)) model)
  | observedReceive {context : ProtocolContext} {definitions : List CheckedDefinition}
      {callees : List CalleeKey} {selection : ConnectionLibrary.Selection definitions callees} {out : List Ty} {role : Nat} {scopes : List (List Nat)}
      {outputs : List Original.Location} {history : Option Nat} {scope : Scope} {frames : ScopedFrames scope} {layout : Layout scope}
      (ty : Ty) (site : String) (peer : Nat)
      {next : Form [] callees (.value ty :: scope) out} {rest : Block}
      (replacement : Replacement) (profile : routing.context.profile = .fiatShamir replacement)
      (mode : routing.mode = .validator) (data : ty.isService = false)
      {prepared : Layout (.value ty :: scope)} {preparation : Block}
      (preparationProof : CoordinatePrefix (receiveLayout layout ty) prepared preparation)
      (stateRef pathRef : Nat)
      (valueRead : prepared[layout.length]? = some (.data (.present (.var .here))))
      (stateRead : prepared[stateRef]? = some (.history routing.context.suite))
      (pathRead : prepared[pathRef]? = some (.coordinates (frames.rename .there).coordinates))
      (template : Template)
      (route : OccurrenceResolution.resolveStatic routing.snapshot routing.context
        (routing.context.message (qualifyProtocolSite context.applicationPrefix site)
          (context.roles peer) routing.context.validator) frames.sites routing.messages = some template)
      (tail : Alignment routing context definitions callees (selection := selection) out role scopes outputs history (frames.rename .there)
        (observedLayout prepared routing.context.suite) next rest) :
      Alignment routing context definitions callees (selection := selection) out role scopes outputs history frames layout (.receive ty site peer next)
        (fun model => Domain.View.sequence
          (Domain.View.receive (qualifyProtocolSite context.applicationPrefix site)
            (qualifyProtocolSite context.applicationPrefix site) (routing.context.role (context.roles peer)) ty [.data ty])
          (preparationProof.prepend (fun model => Domain.View.sequence
            (Domain.View.observe routing.context routing.context.suite template stateRef layout.length pathRef
              [.transcript routing.context.suite]) (rest model)) model))
  | delivery {context : ProtocolContext} {definitions : List CheckedDefinition}
      {callees : List CalleeKey} {selection : ConnectionLibrary.Selection definitions callees} {out : List Ty} {role : Nat} {scopes : List (List Nat)}
      {outputs : List Original.Location} {history : Option Nat} {scope : Scope} {frames : ScopedFrames scope} {layout : Layout scope}
      (site field : String) (peer : Nat)
      {next : Form [] callees (.value (.field field) :: scope) out} {rest : Block}
      (replacement : Replacement) (profile : routing.context.profile = .fiatShamir replacement)
      (mode : routing.mode = .producer) (draw message : Template)
      (binding : ConnectionStaticRoutes.Delivery routing frames.sites
        (qualifyProtocolSite context.applicationPrefix site) field (context.roles peer) draw message)
      (contract : routing.context.contract = "random." ++ field ++ "/0")
      (request : routing.context.request = some (.draw field))
      (stateRef pathRef : Nat)
      (stateRead : layout[stateRef]? = some (.history routing.context.suite))
      (pathRead : layout[pathRef]? = some (.coordinates frames.coordinates))
      {prepared : Layout (.value (.field field) :: scope)} {preparation : Block}
      (preparationProof : CoordinatePrefix (queryLayout layout field routing.context.suite) prepared preparation)
      (observeStateRef observePathRef : Nat)
      (valueRead : prepared[layout.length]? = some (.data (.present (.var .here))))
      (observeStateRead : prepared[observeStateRef]? = some (.history routing.context.suite))
      (observePathRead : prepared[observePathRef]? = some (.coordinates (frames.rename .there).coordinates))
      (tail : Alignment routing context definitions callees (selection := selection) out role scopes outputs history (frames.rename .there)
        (observedLayout prepared routing.context.suite) next rest) :
      Alignment routing context definitions callees (selection := selection) out role scopes outputs history frames layout (.receive (.field field) site peer next)
        (fun model => Domain.View.sequence
          (Domain.View.challenge routing.context routing.context.suite field draw stateRef pathRef
            [.data (.field field), .transcript routing.context.suite])
          (preparationProof.prepend (fun model => Domain.View.sequence
            (Domain.View.observe routing.context routing.context.suite message observeStateRef layout.length observePathRef
              [.transcript routing.context.suite]) (rest model)) model))
  | indicesEmpty {context : ProtocolContext} {definitions : List CheckedDefinition}
      {callees : List CalleeKey} {selection : ConnectionLibrary.Selection definitions callees} {out : List Ty} {role : Nat} {scopes : List (List Nat)}
      {outputs : List Original.Location} {history : Option Nat} {scope : Scope} {frames : ScopedFrames scope} {layout : Layout scope}
      {form : Form [] callees scope out} {rest : Block}
      (tail : Alignment routing context definitions callees (selection := selection) out role scopes outputs history frames
        (layout ++ [.coordinates []]) form rest) :
      Alignment routing context definitions callees (selection := selection) out role scopes outputs history frames layout form
        (fun model => Domain.View.sequence (Domain.View.indicesEmpty [.indices]) (rest model))
  | indicesAppend {context : ProtocolContext} {definitions : List CheckedDefinition}
      {callees : List CalleeKey} {selection : ConnectionLibrary.Selection definitions callees} {out : List Ty} {role : Nat} {scopes : List (List Nat)}
      {outputs : List Original.Location} {history : Option Nat} {scope : Scope} {frames : ScopedFrames scope} {layout : Layout scope}
      {form : Form [] callees scope out} {rest : Block}
      (terms : List (Term [] scope .index)) (term : Term [] scope .index)
      (coordinateRef indexRef : Nat)
      (coordinates : layout[coordinateRef]? = some (.coordinates terms))
      (index : layout[indexRef]? = some (.data (.present term)))
      (tail : Alignment routing context definitions callees (selection := selection) out role scopes outputs history frames
        (layout ++ [.coordinates (terms ++ [term])]) form rest) :
      Alignment routing context definitions callees (selection := selection) out role scopes outputs history frames layout form
        (fun model => Domain.View.sequence (Domain.View.indicesAppend coordinateRef indexRef [.indices]) (rest model))
  | publicQuery {context : ProtocolContext} {definitions : List CheckedDefinition}
      {callees : List CalleeKey} {selection : ConnectionLibrary.Selection definitions callees} {out : List Ty} {role : Nat} {scopes : List (List Nat)}
      {outputs : List Original.Location} {history : Option Nat} {scope : Scope} {frames : ScopedFrames scope} {layout : Layout scope}
      (site field : String) (handle : Nat) (selected : handle = routing.selectedHandle) {next : Form [] callees (.value (.field field) :: scope) out} {rest : Block}
      (mode : routing.mode = .validator) (publicService : routing.context.service.isSome = true)
      (contract : routing.context.contract = "random." ++ field ++ "/0")
      (request : routing.context.request = some (.draw field))
      (template : Template)
      (route : OccurrenceResolution.resolveStatic routing.snapshot routing.context
        (routing.context.query (qualifyProtocolSite context.applicationPrefix site) (.draw field))
        frames.sites routing.draws = some template)
      (stateRef pathRef : Nat)
      (stateRead : layout[stateRef]? = some (.history routing.context.suite))
      (pathRead : layout[pathRef]? = some (.coordinates frames.coordinates))
      (tail : Alignment routing context definitions callees (selection := selection) out role scopes outputs history (frames.rename .there)
        (queryLayout layout field routing.context.suite) next rest) :
      Alignment routing context definitions callees (selection := selection) out role scopes outputs history frames layout
        (.query site field (.cons (.capability ("random." ++ field ++ "/0") handle) .nil) next)
        (fun model => Domain.View.sequence
          (Domain.View.challenge routing.context routing.context.suite field template stateRef pathRef
            [.data (.field field), .transcript routing.context.suite]) (rest model))
  | localQuery {context : ProtocolContext} {definitions : List CheckedDefinition}
      {callees : List CalleeKey} {selection : ConnectionLibrary.Selection definitions callees} {out : List Ty} {role : Nat} {scopes : List (List Nat)}
      {outputs : List Original.Location} {history : Option Nat} {scope : Scope} {frames : ScopedFrames scope} {layout : Layout scope}
      (site field : String) (handle : Nat) {next : Form [] callees (.value (.field field) :: scope) out} {rest : Block}
      (port : ServicePort) (template : Template)
      (mode : ConnectionStaticRoutes.LocalMode routing frames.sites
        (qualifyProtocolSite context.applicationPrefix site) field handle)
      (binding : ConnectionStaticRoutes.Local routing frames.sites
        (qualifyProtocolSite context.applicationPrefix site) field handle port template)
      (contract : port.contract = "random." ++ field ++ "/0")
      (coordinates : List Nat) (readback : IndexReadback layout frames.coordinates coordinates)
      (tail : Alignment routing context definitions callees (selection := selection) out role scopes outputs history (frames.rename .there)
        (receiveLayout layout (.field field)) next rest) :
      Alignment routing context definitions callees (selection := selection) out role scopes outputs history frames layout
        (.query site field (.cons (.capability ("random." ++ field ++ "/0") handle) .nil) next)
        (fun model => Domain.View.sequence
          (Domain.View.localService routing.context port (.draw field) template coordinates [] [.data (.field field)]) (rest model))
  | repeat {context : ProtocolContext} {definitions : List CheckedDefinition}
      {callees : List CalleeKey} {selection : ConnectionLibrary.Selection definitions callees} {out : List Ty} {role : Nat} {scopes : List (List Nat)}
      {outputs : List Original.Location} {history : Option Nat}
      {scope : Scope} {frames : ScopedFrames scope} {layout : Layout scope}
      (spec : RepeatSpec) (site : String)
      (callback : Region protocolDialect (.index :: (spec.state ++ spec.captures)) spec.state)
      (count : Term [] scope .index) (initial : Values (Comp [] scope) spec.state)
      (captures : Values (Comp [] scope) spec.captures)
      {next : Form [] callees (.tuple spec.state :: scope) out} {body rest : Block}
      (roster : Nat) (distinct : RosterDistinct context role roster)
      (active : (spec.roles.map context.roles).contains (context.roles role) = true)
      (visible : visibleState role spec.stateScopes spec.state = true)
      (mappedVisible : visibleState (context.roles role) (context.mapScopes spec.stateScopes) spec.state = true)
      (countReference : Nat) (countRead : layout[countReference]? = some (.data (.present count)))
      (stateReferences initialReferences yieldData yielded : List Nat) (initialHistory bodyHistory : Option Nat)
      (initialRead : Readback layout initial (stateReferences.map Original.Location.data))
      (historyRead : HistoryReadback layout routing.context.suite initialHistory)
      (initialProfile : Original.profileReferences routing.context stateReferences initialHistory = some initialReferences)
      (bodyProfile : Original.profileReferences routing.context yieldData bodyHistory = some yielded)
      (yieldLocations : Original.outputReferences role spec.stateScopes (yieldData.map Original.Location.data) = some yieldData)
      (bodyForm : Form [] callees (RepeatScope spec.state scope) spec.state)
      (normalized : normalizeRegion {strict := true, callees := callees} role roster callback
        ⟨repeatInputs captures, repeatInputs captures⟩ = .ok bodyForm)
      (bodyCertificate : Alignment routing context definitions callees (selection := selection) spec.state role spec.stateScopes
        (yieldData.map Original.Location.data) bodyHistory
        (repeatFrames frames (qualifyProtocolSite context.applicationPrefix site))
        (repeatLayout routing.context layout spec.state) bodyForm body)
      (tail : Alignment routing context definitions callees (selection := selection) out role scopes outputs history
        (frames.rename .there) (repeatExitLayout routing.context layout spec.state) next rest) :
      Alignment routing context definitions callees (selection := selection) out role scopes outputs history frames layout
        (.repeat spec site callback (.present count) initial captures next)
        (fun model => Domain.View.sequence
          (Domain.View.loop spec.maximum yielded countReference initialReferences
            (Original.profileOutputSorts routing.context (spec.state.map ValueSort.data)) (body model)) (rest model))
  | projectedRepeat {context : ProtocolContext} {definitions : List CheckedDefinition}
      {callees : List CalleeKey} {selection : ConnectionLibrary.Selection definitions callees} {out : List Ty} {role : Nat} {scopes : List (List Nat)}
      {outputs : List Original.Location} {history : Option Nat}
      {scope : Scope} {frames : ScopedFrames scope} {layout : Layout scope}
      (spec : RepeatSpec) (site : String)
      (callback : Region protocolDialect (.index :: (spec.state ++ spec.captures)) spec.state)
      (count : Term [] scope .index) (initial : Values (Comp [] scope) spec.state)
      (captures : Values (Comp [] scope) spec.captures)
      {next : Form [] callees (.tuple spec.state :: scope) out} {body rest : Block}
      (roster : Nat) (distinct : RosterDistinct context role roster)
      (active : (spec.roles.map context.roles).contains (context.roles role) = true)
      (visibility : ConnectionFrame.visibility role spec.stateScopes =
        ConnectionFrame.visibility (context.roles role) (context.mapScopes spec.stateScopes))
      (stateSorts : List ValueSort)
      (schema : Original.roleOutputSorts (context.roles role) (context.mapScopes spec.stateScopes) spec.state = some stateSorts)
      (countReference : Nat) (countRead : layout[countReference]? = some (.data (.present count)))
      (initialLocations yieldLocations : List Original.Location)
      (stateReferences initialReferences yieldData yielded : List Nat) (initialHistory bodyHistory : Option Nat)
      (initialRead : Readback layout initial initialLocations)
      (initialProjection : Original.outputReferences role spec.stateScopes initialLocations = some stateReferences)
      (yieldProjection : Original.outputReferences role spec.stateScopes yieldLocations = some yieldData)
      (historyRead : HistoryReadback layout routing.context.suite initialHistory)
      (initialProfile : Original.profileReferences routing.context stateReferences initialHistory = some initialReferences)
      (bodyProfile : Original.profileReferences routing.context yieldData bodyHistory = some yielded)
      (bodyForm : Form [] callees (RepeatScope spec.state scope) spec.state)
      (normalized : normalizeRegion {strict := true, callees := callees} role roster callback
        ⟨projectedInputs role captures, projectedInputs role captures⟩ = .ok bodyForm)
      (bodyCertificate : Alignment routing context definitions callees (selection := selection) spec.state role spec.stateScopes
        yieldLocations bodyHistory (repeatFrames frames (qualifyProtocolSite context.applicationPrefix site))
        (projectedLayout routing.context role spec.stateScopes layout spec.state) bodyForm body)
      (nextMatched : next.CallsMatch)
      (tail : Alignment routing context definitions callees (selection := selection) out role scopes outputs history
        (frames.rename .there) (projectedExitLayout routing.context role spec.stateScopes layout spec.state)
        (ConnectionSubstitution.maskNext role spec.stateScopes next) rest) :
      Alignment routing context definitions callees (selection := selection) out role scopes outputs history frames layout
        (.repeat spec site callback (.present count) initial captures next)
        (fun model => Domain.View.sequence
          (Domain.View.loop spec.maximum yielded countReference initialReferences
            (Original.profileOutputSorts routing.context stateSorts) (body model)) (rest model))
  /-- A selected checked callee followed by its caller continuation. The body
  reference owns its source normalization; the flat target spine and full exit
  frame remain finite structural admission, including all unused SSA cells. -/
  | application {context : ProtocolContext} {definitions : List CheckedDefinition}
      {callees : List CalleeKey} {out : List Ty} {role : Nat} {scopes : List (List Nat)}
      {outputs : List Original.Location} {history : Option Nat} {scope : Scope}
      {frames : ScopedFrames scope} {layout : Layout scope}
      (payload : UnitPayload) (same : payload.definitions = definitions)
      (library : ConnectionLibrary.Library payload callees) (callee : Fin callees.length)
      (signature : ProtocolSignature) (signatureMatch : (calleeAt callees callee).signature = signature)
      (roles : List Nat) (site : String)
      (arguments : Values (Argument [] scope) (calleeAt callees callee).pattern.scope)
      (calleeOutputs : List Original.Location) (calleeHistory : Option Nat)
      (spine : ConnectionTargetPrefix.Prefix) (extent : Nat)
      (physicalExtent : ConnectionTargetExtent.Extent layout.length extent spine.block)
      (admission : applicationAdmitted layout.length extent calleeOutputs calleeHistory)
      (bodyCertificate : Alignment routing (context.enter site roles) definitions
        (library.entry callee).earlierKeys
        (selection := .selected payload same (library.entry callee).earlier)
        (calleeAt callees callee).signature.outputs (calleeAt callees callee).role
        (calleeAt callees callee).signature.outputScopes calleeOutputs calleeHistory frames layout
        (ConnectionSubstitution.form (library.entry callee).form (fun binder => entryAt arguments binder)) spine.block)
      (next : Form [] callees (.tuple (calleeAt callees callee).signature.outputs :: scope) out)
      (rest : Block)
      (tail : Alignment routing context definitions callees (selection := .selected payload same library)
        out role scopes outputs history (frames.rename .there)
        (applicationLayout layout extent (calleeAt callees callee).role
          (calleeAt callees callee).signature.outputScopes (calleeAt callees callee).signature.outputs
          calleeOutputs calleeHistory routing.context.suite) next rest) :
      Alignment routing context definitions callees (selection := .selected payload same library)
        out role scopes outputs history frames layout (.apply callee signature roles site arguments next)
        (spine.plug rest)
  | guard {context : ProtocolContext} {definitions : List CheckedDefinition}
      {callees : List CalleeKey} {selection : ConnectionLibrary.Selection definitions callees} {out : List Ty} {role : Nat} {scopes : List (List Nat)}
      {outputs : List Original.Location} {history : Option Nat} {scope : Scope} {frames : ScopedFrames scope} {layout : Layout scope} {ty : Ty}
      (equality : Equality ty) (left right : Term [] scope ty)
      {next : Form [] callees scope out} {rest : Block}
      (reference : Nat)
      (readback : GuardReadback layout equality left right reference)
      (tail : Alignment routing context definitions callees (selection := selection) out role scopes outputs history frames readback.refine next rest) :
      Alignment routing context definitions callees (selection := selection) out role scopes outputs history frames layout (.guard equality left right next)
        (fun model => Domain.View.sequence (Domain.View.guard reference []) (rest model))
  | trueGuard {context : ProtocolContext} {definitions : List CheckedDefinition}
      {callees : List CalleeKey} {selection : ConnectionLibrary.Selection definitions callees} {out : List Ty} {role : Nat} {scopes : List (List Nat)}
      {outputs : List Original.Location} {history : Option Nat} {scope : Scope} {frames : ScopedFrames scope} {layout : Layout scope} {form : Form [] callees scope out}
      (reference : Nat) (readback : Readback layout (.cons (.present (.bool true)) .nil) [.data reference])
      {rest : Block} (tail : Alignment routing context definitions callees (selection := selection) out role scopes outputs history frames layout form rest) :
      Alignment routing context definitions callees (selection := selection) out role scopes outputs history frames layout form
        (fun model => Domain.View.sequence (Domain.View.guard reference []) (rest model))
  | falseGuard {context : ProtocolContext} {definitions : List CheckedDefinition}
      {callees : List CalleeKey} {selection : ConnectionLibrary.Selection definitions callees} {out : List Ty} {role : Nat} {scopes : List (List Nat)}
      {outputs : List Original.Location} {history : Option Nat} {scope : Scope} {frames : ScopedFrames scope} {layout : Layout scope}
      (reference : Nat) (readback : Readback layout (.cons (.present (.bool false)) .nil) [.data reference])
      (rest : Block) :
      Alignment routing context definitions callees (selection := selection) out role scopes outputs history frames layout (.halt .reject)
        (fun model => Domain.View.sequence (Domain.View.guard reference []) (rest model))

/-- Public alignment type; omitted selections support only callee-free paths. -/
abbrev Derivation (routing : Original.Routing) (context : ProtocolContext)
    (definitions : List CheckedDefinition) (callees : List CalleeKey)
    (out : List Ty) (role : Nat) (scopes : List (List Nat))
    (outputs : List Original.Location) (history : Option Nat)
    {scope : Scope} (frames : ScopedFrames scope) (layout : Layout scope)
    (form : Form [] callees scope out) (target : Block)
    (selection : ConnectionLibrary.Selection definitions callees := .unselected) :=
  Alignment routing context definitions callees (selection := selection)
    out role scopes outputs history frames layout form target

namespace Derivation
abbrev done := @Alignment.done
abbrev halt := @Alignment.halt
abbrev split := @Alignment.split
abbrev splitAbsent := @Alignment.splitAbsent
abbrev splitValue := @Alignment.splitValue
abbrev splitPresent := @Alignment.splitPresent
abbrev compute := @Alignment.compute
abbrev strictHelper := @Alignment.strictHelper
abbrev ownedHelper := @Alignment.ownedHelper
abbrev mathHelper := @Alignment.mathHelper
abbrev projectionHelper := @Alignment.projectionHelper
abbrev inlineCalculation := @Alignment.inlineCalculation
abbrev inlineMissingCalculation := @Alignment.inlineMissingCalculation
abbrev calculation := @Alignment.calculation
abbrev receive := @Alignment.receive
abbrev send := @Alignment.send
abbrev observedSend := @Alignment.observedSend
abbrev observedReceive := @Alignment.observedReceive
abbrev delivery := @Alignment.delivery
abbrev indicesEmpty := @Alignment.indicesEmpty
abbrev indicesAppend := @Alignment.indicesAppend
abbrev publicQuery := @Alignment.publicQuery
abbrev localQuery := @Alignment.localQuery
abbrev «repeat» := @Alignment.repeat
abbrev projectedRepeat := @Alignment.projectedRepeat
abbrev application := @Alignment.application
abbrev guard := @Alignment.guard
abbrev trueGuard := @Alignment.trueGuard
abbrev falseGuard := @Alignment.falseGuard
end Derivation

/-- Certificate size follows syntax, independently of values and replies. -/
def Alignment.size {routing : Original.Routing} {context : ProtocolContext} {definitions : List CheckedDefinition}
    {callees : List CalleeKey} {selection : ConnectionLibrary.Selection definitions callees} {out : List Ty} {role : Nat} {scopes : List (List Nat)}
    {outputs : List Original.Location} {history : Option Nat}
    {scope : Scope} {frames : ScopedFrames scope} {layout : Layout scope} {form : Form [] callees scope out} {target : Block} :
    Derivation routing context definitions callees (selection := selection) out role scopes outputs history frames layout form target → Nat
  | .done .. | .halt _ | .falseGuard .. => 1
  | .split _ absent present => 1 + absent.size + present.size
  | .splitAbsent _ tail => 1 + tail.size
  | .splitValue _ _ tail => 1 + tail.size
  | .splitPresent _ _ _ _ tail => 1 + tail.size
  | .compute _ _ _ _ _ _ tail => 1 + tail.size
  | .strictHelper _ _ _ _ _ _ _ _ tail => 1 + tail.size
  | .ownedHelper _ _ _ _ _ _ _ _ _ tail => 1 + tail.size
  | .mathHelper _ _ _ _ _ _ _ _ _ tail => 1 + tail.size
  | .projectionHelper _ _ _ _ tail => 1 + tail.size
  | .inlineCalculation _ _ _ _ tail => 1 + tail.size
  | .inlineMissingCalculation _ _ _ _ _ tail => 1 + tail.size
  | .calculation _ _ _ _ _ _ _ tail => 1 + tail.size
  | .receive _ _ _ _ _ _ _ tail => 1 + tail.size
  | .send _ _ _ _ _ _ _ _ _ tail => 1 + tail.size
  | .observedSend (tail := tail) .. => 1 + tail.size
  | .observedReceive (tail := tail) .. => 1 + tail.size
  | .delivery (tail := tail) .. => 1 + tail.size
  | .indicesEmpty tail => 1 + tail.size
  | .indicesAppend _ _ _ _ _ _ tail => 1 + tail.size
  | .publicQuery (tail := tail) .. => 1 + tail.size
  | .localQuery _ _ _ _ _ _ _ _ _ _ tail => 1 + tail.size
  | .repeat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ body tail =>
      1 + body.size + tail.size
  | .projectedRepeat (bodyCertificate := body) (tail := tail) .. => 1 + body.size + tail.size
  | .application (bodyCertificate := body) (tail := tail) .. => 1 + body.size + tail.size
  | .guard _ _ _ _ _ tail => 1 + tail.size
  | .trueGuard _ _ tail => 1 + tail.size

/-- Structural helper bindings introduce no normalizer laws or callee calls. -/
theorem Alignment.callsMatch {routing : Original.Routing} {context : ProtocolContext} {definitions : List CheckedDefinition}
    {callees : List CalleeKey} {selection : ConnectionLibrary.Selection definitions callees} {out : List Ty} {role : Nat} {scopes : List (List Nat)}
    {outputs : List Original.Location} {history : Option Nat}
    {scope : Scope} {frames : ScopedFrames scope} {layout : Layout scope} {form : Form [] callees scope out} {target : Block}
    (derivation : Derivation routing context definitions callees (selection := selection) out role scopes outputs history frames layout form target) : form.CallsMatch := by
  induction derivation
  case splitValue value absentMatched tail ih =>
    have presentMatched := (ConnectionSubstitution.form_callsMatch _ _).mp ih
    simp_all only [Form.CallsMatch, Form.lawCalls, Form.calleeCalls, List.map_append, Prod.mk.injEq]
  all_goals simp_all only [Form.CallsMatch, Form.lawCalls, Form.calleeCalls, List.map_append, List.map_cons, Prod.mk.injEq]
  all_goals first | assumption | exact ⟨rfl, rfl⟩

abbrev Derivation.size := @Alignment.size
abbrev Derivation.callsMatch := @Alignment.callsMatch

/-- Full source-owned visibility, exact reached stack and transcript, and retained inputs. -/
def Returns {model : DomainModel} {out : List Ty} (routing : Original.Routing)
    (role : Nat) (scopes : List (List Nat)) (outputs : List Original.Location) (history : Option Nat)
    (frames : Original.Frames) (captured : Domain.Environment model.toCarriers)
    (source : Values (Component model.Value) out × Original.State model.toCarriers)
    (target : Domain.Environment model.toCarriers) : Prop :=
  Original.ValuesHolds target outputs (maskValues role scopes source.1) ∧
    source.2.frames = frames ∧
    (match history with
     | none => True
     | some reference => target[reference]? = some (.transcript routing.context.suite source.2.history)) ∧
    ArtifactBinding.Captures captured target

/-- Internal structural induction for the public certificate boundary. All models, source binders and
physical environments satisfying the fixed frame relation are quantified.
The source is the actual occurrence-aware denotation folded by Original.fold;
the target is the actual indexed Domain.View block, including its checkpoints.
Input sorts, complete input readback and bounds are fixed ABI obligations.
RouteCoverage and CompleteReturns remain available as independent root gates. -/
private noncomputable def sound
    {routing : Original.Routing} {context : ProtocolContext} {definitions : List CheckedDefinition}
    {callees : List CalleeKey} {selection : ConnectionLibrary.Selection definitions callees} {out : List Ty} {role : Nat} {scopes : List (List Nat)}
    {outputs : List Original.Location} {history : Option Nat}
    {scope : Scope} {frames : ScopedFrames scope} {layout : Layout scope} {form : Form [] callees scope out} {target : Block}
    (derivation : Derivation routing context definitions callees (selection := selection) out role scopes outputs history frames layout form target)
    (model : DomainModel) (tables : Tables model (Occurrence.signature model.toCarriers))
    (bindings : ConnectionHelpers.TablesMatch model definitions tables)
    (runs : Runs model (Occurrence.signature model.toCarriers))
    (protocols : ProtocolTable model.Value (Occurrence.signature model.toCarriers))
    (_runBinding : runs = runsAtOn model Occurrence.actions Occurrence.iterations tables protocols context role)
    (processes : CalleeProcesses model callees (Occurrence.signature model.toCarriers))
    (calleesHold : ∀ {types : List Ty} (inputs : Values (Component model.Value) types),
      CalleesHold protocols processes inputs)
    (selectionMeaning : selection.Meaning model tables protocols processes)
    (expectedFrames : Original.Frames) (state : Original.State model.toCarriers) (stack : state.frames = expectedFrames)
    (captured : Domain.Environment model.toCarriers)
    (binders : Binders model scope) (reachedStack : state.frames = frames.eval model binders) (environment : Domain.Environment model.toCarriers)
    (related : Holds model binders state.history layout environment)
    (retained : ArtifactBinding.Captures captured environment) :
    Original.Simulation (Returns routing role scopes outputs history expectedFrames captured)
      (fun _ frame => ArtifactBinding.Captures captured frame)
      (Original.fold routing (form.denoteOn model Occurrence.actions tables (LawResults.empty model)
        context runs processes binders) state) (target model environment) := by
  induction derivation generalizing model tables protocols runs expectedFrames state captured environment with
  | done readback historyRead =>
    refine .done ⟨readback.masked related, stack, ?_, retained⟩
    cases historyRead with
    | plain => trivial
    | transcript reference checked => exact related.readHistory checked
  | halt reason => exact .halt reason
  | split subject absentBranch presentBranch absentIH presentIH =>
    cases evaluated : subject.comp.eval (LawResults.empty model) binders with
    | none =>
      simpa only [Form.denoteOn, Form.denoteWithOn, evaluated] using
        absentIH model tables bindings runs protocols _runBinding processes calleesHold selectionMeaning expectedFrames state stack captured binders reachedStack environment (related.absentAt subject evaluated) retained
    | some value =>
      simpa only [Form.denoteOn, Form.denoteWithOn, evaluated] using
        presentIH model tables bindings runs protocols _runBinding processes calleesHold selectionMeaning expectedFrames state stack captured (.cons value binders) (reachedStack.trans (ScopedFrames.eval_rename .there binders _ (fun _ => rfl) _).symm) environment (related.presentAt subject value evaluated) retained
  | splitAbsent presentMatched tail ih =>
    simpa only [Form.denoteOn, Form.denoteWithOn, Comp.eval] using
      ih model tables bindings runs protocols _runBinding processes calleesHold selectionMeaning expectedFrames state stack captured binders reachedStack environment related retained
  | @splitValue context definitions callees selection out role scopes outputs history scope frames layout ty value absent present target absentMatched tail ih =>
    have aligned := ih model tables bindings runs protocols _runBinding processes calleesHold selectionMeaning expectedFrames state stack captured binders reachedStack environment related retained
    rw [ConnectionSubstitution.valueHead_denote] at aligned
    simpa only [Form.denoteOn, Form.denoteWithOn, Comp.eval] using aligned
  | splitPresent subject reference checked absentMatch tail ih =>
    cases evaluated : subject.comp.eval (LawResults.empty model) binders with
    | none => exact False.elim (related.not_absent checked evaluated)
    | some value =>
      simpa only [Form.denoteOn, Form.denoteWithOn, evaluated] using
        ih model tables bindings runs protocols _runBinding processes calleesHold selectionMeaning expectedFrames state stack captured (.cons value binders) (reachedStack.trans (ScopedFrames.eval_rename .there binders _ (fun _ => rfl) _).symm) environment (related.presentAt subject value evaluated) retained
  | @compute context definitions callees selection out role scopes outputs history scope frames layout operation terms next rest references inputsData outputsData readback tail ih =>
    rw [ConnectionCalculations.form_compute_closed model Occurrence.actions (LawResults.empty model)
      context runs processes tables operation terms next binders, Original.fold_bind]
    apply Original.Simulation.checkpoint environment retained
    apply (Original.Simulation.closedCalculationOn model routing operation
      (Terms.eval (LawResults.empty model) terms binders) inputsData outputsData state environment references
      (read_terms readback binders related)).bind
    · intro process frame same
      subst frame
      exact retained
    · intro source target returned
      apply Classical.choice
      obtain ⟨values, same, appended⟩ := returned
      rw [same, appended]
      have kept := ArtifactBinding.captures_trans retained (ArtifactBinding.captures_append
        environment (Original.encodeHelperResult values))
      exact ⟨.checkpoint _ kept
        (ih model tables bindings runs protocols _runBinding processes calleesHold selectionMeaning expectedFrames state stack captured (.cons values binders) (reachedStack.trans (ScopedFrames.eval_rename .there binders _ (fun _ => rfl) _).symm) _ (results_frame model outputsData values binders related) kept)⟩
  | @strictHelper context definitions callees selection out role scopes outputs history scope frames layout program helper binding arguments next rest references inputsData outputsData
      readback tail ih =>
    change Original.Simulation _ _ (Original.fold routing
      ((invoke tables.closed helper (Terms.eval (LawResults.empty model) arguments binders)).bind
        (fun values => next.denoteOn model Occurrence.actions tables (LawResults.empty model)
          context runs processes (.cons values binders))) state) _
    rw [Original.fold_bind]
    have sourceTables := binding.tables bindings
    have invoked : invoke tables.closed helper (Terms.eval (LawResults.empty model) arguments binders) =
        (invoke (Domain.helperTable model program) helper
          (Terms.eval (LawResults.empty model) arguments binders)).interpret
            (closedLift (I := Occurrence.signature model.toCarriers)) := by
      rw [sourceTables, Evaluation.closed_invoke_componentTablesOn]
      rfl
    rw [invoked]
    apply Original.Simulation.checkpoint environment retained
    apply (Original.Simulation.linkedDataHelperOn model program routing helper binding.present outputsData
      (Terms.eval (LawResults.empty model) arguments binders) environment references
      (read_terms readback binders related) state inputsData).bind
    · intro process frame same
      subst frame
      exact retained
    · intro source target returned
      apply Classical.choice
      obtain ⟨values, same, appended⟩ := returned
      rw [same, appended]
      have kept := ArtifactBinding.captures_trans retained (ArtifactBinding.captures_append
        environment (Original.encodeHelperResult values))
      exact ⟨.checkpoint _ kept
        (ih model tables bindings runs protocols _runBinding processes calleesHold selectionMeaning expectedFrames state stack captured (.cons values binders)
          (reachedStack.trans (ScopedFrames.eval_rename .there binders _ (fun _ => rfl) _).symm)
          _ (results_frame model outputsData values binders related) kept)⟩
  | @ownedHelper context definitions callees selection out role scopes outputs history scope frames layout owner program helper binding arguments next rest references inputsData outputsData
      readback tail ih =>
    apply Classical.choice
    obtain ⟨values, present, read⟩ := read_components readback binders related
    have sourceEq := ConnectionCalculations.form_owned_present_closed model Occurrence.actions
      (LawResults.empty model) context runs processes program.payload.definitions owner helper arguments values
      next binders present
    rw [← binding.tables bindings] at sourceEq
    rw [sourceEq, Original.fold_bind]
    refine ⟨Original.Simulation.checkpoint environment retained ?_⟩
    apply (Original.Simulation.linkedDataHelperOn model program routing helper binding.present outputsData
      values environment references read state inputsData).bind
    · intro process frame same
      subst frame
      exact retained
    · intro source target returned
      apply Classical.choice
      obtain ⟨values, same, appended⟩ := returned
      rw [same, appended]
      have kept := ArtifactBinding.captures_trans retained (ArtifactBinding.captures_append
        environment (Original.encodeHelperResult values))
      exact ⟨.checkpoint _ kept
        (ih model tables bindings runs protocols _runBinding processes calleesHold selectionMeaning expectedFrames state stack captured (.cons values.present binders)
          (reachedStack.trans (ScopedFrames.eval_rename .there binders _ (fun _ => rfl) _).symm)
          _ (tuple_frame model outputsData values binders related) kept)⟩
  | @mathHelper context definitions callees selection out role scopes outputs history scope frames layout program helper math binding arguments next rest references inputsData outputsData
      readback tail ih =>
    apply Classical.choice
    obtain ⟨values, present, read⟩ := read_components readback binders related
    have sourceEq := ConnectionCalculations.form_math_present_closed model Occurrence.actions
      (LawResults.empty model) context runs processes program.payload.definitions helper arguments values
      next binders present
    rw [← binding.tables bindings] at sourceEq
    rw [sourceEq, Original.fold_bind]
    refine ⟨Original.Simulation.checkpoint environment retained ?_⟩
    apply (Original.Simulation.linkedDataHelperOn model program routing helper binding.present outputsData
      values environment references read state inputsData).bind
    · intro process frame same
      subst frame
      exact retained
    · intro source target returned
      apply Classical.choice
      obtain ⟨values, same, appended⟩ := returned
      rw [same, appended]
      have kept := ArtifactBinding.captures_trans retained (ArtifactBinding.captures_append
        environment (Original.encodeHelperResult values))
      exact ⟨.checkpoint _ kept
        (ih model tables bindings runs protocols _runBinding processes calleesHold selectionMeaning expectedFrames state stack captured (.cons values.present binders) (reachedStack.trans (ScopedFrames.eval_rename .there binders _ (fun _ => rfl) _).symm) _ (tuple_frame model outputsData values binders related) kept)⟩
  | @projectionHelper context definitions callees selection out role scopes outputs history scope frames layout definition projection arguments next target nextMatched tail ih =>
    have tableEquality := bindings ⟨projection.before.length, by
      have length := congrArg List.length projection.declarations
      simp only [List.length_append, List.length_cons] at length
      omega⟩
    have invoked : invoke tables.components definition.helper (Comps.eval (LawResults.empty model) arguments binders) =
        .done (Comps.eval (LawResults.empty model) (lookup arguments projection.positions) binders) := by
      rw [tableEquality]
      exact (projection.invoke model (I := Occurrence.signature model.toCarriers)
        (Comps.eval (LawResults.empty model) arguments binders)).trans
          (congrArg PIR.Process.done
            ((congrArg (fun values => Comps.eval (LawResults.empty model) values binders)
              (lookup_eq_eval arguments projection.positions)).trans
                (comps_eval_operands (LawResults.empty model) arguments binders projection.positions)).symm)
    change Original.Simulation _ _ (Original.fold routing
      ((invoke tables.components definition.helper (Comps.eval (LawResults.empty model) arguments binders)).bind
        (fun values => _)) state) _
    rw [invoked, PIR.Process.bind]
    change Original.Simulation _ _ (Original.fold routing
      (next.denoteOn model Occurrence.actions tables (LawResults.empty model) context runs processes
        (.cons (Comps.eval (LawResults.empty model) (lookup arguments projection.positions) binders) binders)) state) _
    rw [← ConnectionSubstitution.tupleHead_denote (lookup arguments projection.positions)
      Occurrence.actions tables context runs processes next binders]
    exact ih model tables bindings runs protocols _runBinding processes calleesHold selectionMeaning expectedFrames state stack captured binders reachedStack environment related retained
  | @inlineCalculation context definitions callees selection out role scopes outputs history scope frames layout
      definition calculation arguments next target nextMatched tail ih =>
    have tableEquality := bindings ⟨calculation.before.length, by
      have length := congrArg List.length calculation.declarations
      simp only [List.length_append, List.length_cons] at length
      omega⟩
    have invoked : invoke tables.components definition.helper
        (Comps.eval (LawResults.empty model) (components arguments) binders) =
        .done (Comps.eval (LawResults.empty model) (calculation.result arguments) binders) := by
      rw [tableEquality]
      exact calculation.invoke model arguments binders
    change Original.Simulation _ _ (Original.fold routing
      ((invoke tables.components definition.helper
        (Comps.eval (LawResults.empty model) (components arguments) binders)).bind
        (fun values => _)) state) _
    rw [invoked, PIR.Process.bind]
    change Original.Simulation _ _ (Original.fold routing
      (next.denoteOn model Occurrence.actions tables (LawResults.empty model) context runs processes
        (.cons (Comps.eval (LawResults.empty model) (calculation.result arguments) binders) binders)) state) _
    rw [← ConnectionSubstitution.tupleHead_denote (calculation.result arguments)
      Occurrence.actions tables context runs processes next binders]
    exact ih model tables bindings runs protocols _runBinding processes calleesHold selectionMeaning
      expectedFrames state stack captured binders reachedStack environment related retained
  | @inlineMissingCalculation context definitions callees selection out role scopes outputs history scope frames layout
      definition calculation arguments missing next target nextMatched tail ih =>
    have tableEquality := bindings ⟨calculation.before.length, by
      have length := congrArg List.length calculation.declarations
      simp only [List.length_append, List.length_cons] at length
      omega⟩
    have invoked : invoke tables.components definition.helper
        (Comps.eval (LawResults.empty model) arguments binders) =
        .done (Comps.eval (LawResults.empty model) (calculation.missingResult arguments) binders) := by
      rw [tableEquality]
      exact calculation.invokeMissing model arguments missing binders
    change Original.Simulation _ _ (Original.fold routing
      ((invoke tables.components definition.helper
        (Comps.eval (LawResults.empty model) arguments binders)).bind
        (fun values => _)) state) _
    rw [invoked, PIR.Process.bind]
    change Original.Simulation _ _ (Original.fold routing
      (next.denoteOn model Occurrence.actions tables (LawResults.empty model) context runs processes
        (.cons (Comps.eval (LawResults.empty model) (calculation.missingResult arguments) binders) binders)) state) _
    rw [← ConnectionSubstitution.tupleHead_denote (calculation.missingResult arguments)
      Occurrence.actions tables context runs processes next binders]
    exact ih model tables bindings runs protocols _runBinding processes calleesHold selectionMeaning
      expectedFrames state stack captured binders reachedStack environment related retained
  | @calculation context definitions callees selection out role scopes outputs history scope frames layout form operation total terms references inputsData outputsData readback rest tail ih =>
    have step := ConnectionCalculations.view_calculation_total model operation total
      (Terms.eval (LawResults.empty model) terms binders) inputsData outputsData environment references
      (read_terms readback binders related)
    have extended := calculation_frame model operation total terms outputsData binders related
    have kept := ArtifactBinding.captures_trans retained (ArtifactBinding.captures_append environment
      (Original.encodeHelperResult (operation.op.evalTotal model total
        (Terms.eval (LawResults.empty model) terms binders))))
    apply Original.Simulation.checkpoint environment retained
    rw [step]
    exact .checkpoint _ kept (ih model tables bindings runs protocols _runBinding processes calleesHold selectionMeaning expectedFrames state stack captured binders reachedStack _ extended kept)
  | @receive context definitions callees selection out role scopes outputs history scope frames layout ty site peer next rest plain template route data tail ih =>
    let qualified := qualifyProtocolSite context.applicationPrefix site
    have folded : Original.fold routing (Occurrence.actions
        (.receive ty qualified (context.roles peer))) state =
        Original.receivePlain routing state ty qualified (context.roles peer) := by
      simp only [Original.fold, Occurrence.actions, PIR.Process.interpretState, Original.operations,
        plain]
      exact PIR.Process.bind_done _
    change Original.Simulation _ _
      (Original.fold routing ((Occurrence.actions (.receive ty qualified (context.roles peer))).bind
        (fun reply => next.denoteOn model Occurrence.actions tables (LawResults.empty model)
          context runs processes (.cons reply binders))) state) _
    rw [Original.fold_bind, folded]
    apply Original.Simulation.checkpoint environment retained
    apply (Original.Simulation.plainReceive routing state ty qualified (context.roles peer) _
      (by simpa only [qualified, reachedStack, Original.Routing.message] using frames.resolve binders route) data environment).bind
    · intro process frame same
      subst frame
      exact retained
    · intro source target returned
      apply Classical.choice
      have extended := returned.frame related
      obtain ⟨same, physical, encoded, appended⟩ := returned
      have kept : ArtifactBinding.Captures captured target := by
        rw [appended]
        exact ArtifactBinding.captures_trans retained (ArtifactBinding.captures_append _ _)
      cases source with
      | mk value final =>
        simp only at same
        subst final
        exact ⟨.checkpoint target kept (ih model tables bindings runs protocols _runBinding processes calleesHold selectionMeaning expectedFrames state stack captured (.cons value binders) (reachedStack.trans (ScopedFrames.eval_rename .there binders _ (fun _ => rfl) _).symm) target extended kept)⟩
  | @send context definitions callees selection out role scopes outputs history scope frames layout ty site peer value next rest reference readback plain template route tail ih =>
    apply Classical.choice
    obtain ⟨payload, payloadEq, read⟩ := readback.payload related
    refine ⟨?_⟩
    let qualified := qualifyProtocolSite context.applicationPrefix site
    have folded : Original.fold routing (Occurrence.actions
        (.send (ty := ty) qualified (context.roles peer) (value.eval (LawResults.empty model) binders))) state =
        Original.sendPlain routing state ty qualified (context.roles peer)
          (value.eval (LawResults.empty model) binders) := by
      simp only [Original.fold, Occurrence.actions, PIR.Process.interpretState, Original.operations,
        plain]
      exact PIR.Process.bind_done _
    change Original.Simulation _ _ (Original.fold routing
      ((Occurrence.actions (.send (ty := ty) qualified (context.roles peer)
        (value.eval (LawResults.empty model) binders))).bind
        (fun _ => next.denoteOn model Occurrence.actions tables (LawResults.empty model)
          context runs processes binders)) state) _
    rw [Original.fold_bind, folded]
    apply Original.Simulation.checkpoint environment retained
    apply (Original.Simulation.plainSend routing state ty qualified (context.roles peer)
      (value.eval (LawResults.empty model) binders) _
      (by simpa only [qualified, reachedStack, Original.Routing.message] using frames.resolve binders route) environment reference payload payloadEq
      read).bind
    · intro process frame same
      subst frame
      exact retained
    · intro source target returned
      rw [returned.1, returned.2]
      exact .checkpoint environment retained (ih model tables bindings runs protocols _runBinding processes calleesHold selectionMeaning expectedFrames state stack captured binders reachedStack environment related retained)
  | @observedSend context definitions callees selection out role scopes outputs history scope frames layout ty site peer value next rest replacement profile
      prepared preparation preparationProof reference stateRef pathRef readback preparedReadback stateRead pathRead template route tail ih =>
    apply Classical.choice
    obtain ⟨payload, encoded, read⟩ := readback.payload related
    refine ⟨?_⟩
    let qualified := qualifyProtocolSite context.applicationPrefix site
    let origin := Domain.atCoordinates (routing.context.message qualified routing.self (context.roles peer))
      ((frames.eval model binders).map (·.index))
    have sourceRoute : routing.message state.frames qualified routing.self (context.roles peer) = some origin := by
      rw [reachedStack]
      exact Original.Routing.message_of_static route _ (frames.sites_eval model binders)
    have message : origin.request = none := by unfold origin Domain.atCoordinates; split <;> rfl
    have resolved := template_reached frames binders route
    have folded : Original.fold routing (Occurrence.actions
        (.send (ty := ty) qualified (context.roles peer) (value.eval (LawResults.empty model) binders))) state =
        Original.send routing state ty qualified (context.roles peer) (value.eval (LawResults.empty model) binders) := by
      simp only [Original.fold, Occurrence.actions, PIR.Process.interpretState, Original.operations, profile]
      exact PIR.Process.bind_done _
    change Original.Simulation _ _ (Original.fold routing
      ((Occurrence.actions (.send (ty := ty) qualified (context.roles peer)
        (value.eval (LawResults.empty model) binders))).bind
        (fun _ => next.denoteOn model Occurrence.actions tables (LawResults.empty model)
          context runs processes binders)) state) _
    rw [Original.fold_bind, folded]
    have finish : Original.Simulation (Returns routing role scopes outputs history expectedFrames captured)
        (fun _ frame => ArtifactBinding.Captures captured frame)
        ((Original.record state origin payload).bind (fun source =>
          Original.fold routing (next.denoteOn model Occurrence.actions tables (LawResults.empty model)
            context runs processes binders) source.2))
        (preparationProof.prepend (fun model => Domain.View.sequence
          (Domain.View.observe routing.context routing.context.suite template stateRef reference pathRef
            [.transcript routing.context.suite]) (rest model)) model environment) := by
      rw [preparationProof.prepend_eq]
      apply preparationProof.simulation model binders state.history captured environment related retained
        _ _ _ _ (fun _ kept => kept)
      intro preparedEnvironment preparedRelated preparedRetained
      apply Original.Simulation.checkpoint _ preparedRetained
      have physicalRead := preparedReadback.payload preparedRelated
      have samePayload := Option.some.inj (encoded.symm.trans physicalRead.choose_spec.1)
      have preparedRead := physicalRead.choose_spec.2
      rw [← samePayload] at preparedRead
      apply (Original.Simulation.record state origin payload routing.context template stateRef reference pathRef
        preparedEnvironment _ (preparedRelated.readHistory stateRead) preparedRead (preparedRelated.reachedCoordinates frames pathRef pathRead)
        resolved message).bind
      · intro process frame same
        subst frame
        exact preparedRetained
      · intro source target returned
        obtain ⟨same, appended⟩ := returned
        rw [same, appended]
        have kept := ArtifactBinding.captures_trans preparedRetained (ArtifactBinding.captures_append preparedEnvironment
          [.transcript routing.context.suite (state.history ++ [.message origin payload])])
        exact .checkpoint _ kept (ih model tables bindings runs protocols _runBinding processes calleesHold selectionMeaning expectedFrames { state with history := state.history ++ [.message origin payload] } stack captured binders reachedStack _
          (Original.observation_frame preparedRelated routing.context.suite (.message origin payload)) kept)
    cases mode : routing.mode with
    | producer =>
      have sender : routing.self = routing.context.producer := by simp only [Original.Routing.self, mode]
      simp only [Original.send, mode, ← sender, sourceRoute, encoded, PIR.Process.bind]
      apply Original.Simulation.checkpoint environment retained
      rw [Domain.View.send_eq qualified (routing.context.role (context.roles peer)) reference environment payload read]
      apply Original.Simulation.call
      intro reply
      exact .checkpoint environment retained
        finish
    | validator =>
      have sender : routing.self = routing.context.validator := by simp only [Original.Routing.self, mode]
      simp only [Original.send, mode, ← sender, sourceRoute, encoded]
      exact finish
  | @observedReceive context definitions callees selection out role scopes outputs history scope frames layout ty site peer next rest replacement profile mode data
      prepared preparation preparationProof stateRef pathRef valueRead stateRead pathRead template route tail ih =>
    let qualified := qualifyProtocolSite context.applicationPrefix site
    let origin := Domain.atCoordinates (routing.context.message qualified (context.roles peer) routing.context.validator)
      ((frames.eval model binders).map (·.index))
    have sourceRoute : routing.message state.frames qualified (context.roles peer) routing.context.validator = some origin := by
      rw [reachedStack]
      exact Original.Routing.message_of_static route _ (frames.sites_eval model binders)
    have message : origin.request = none := by unfold origin Domain.atCoordinates; split <;> rfl
    have folded : Original.fold routing (Occurrence.actions (.receive ty qualified (context.roles peer))) state =
        Original.receive routing state ty qualified (context.roles peer) := by
      simp only [Original.fold, Occurrence.actions, PIR.Process.interpretState, Original.operations, profile]
      exact PIR.Process.bind_done _
    change Original.Simulation _ _ (Original.fold routing
      ((Occurrence.actions (.receive ty qualified (context.roles peer))).bind
        (fun reply => next.denoteOn model Occurrence.actions tables (LawResults.empty model)
          context runs processes (.cons reply binders))) state) _
    rw [Original.fold_bind, folded]
    simp only [Original.receive, mode, sourceRoute, PIR.Process.bind]
    apply Original.Simulation.checkpoint environment retained
    rw [Domain.View.receive_eq qualified (routing.context.role (context.roles peer)) ty environment
      (by simp only [Domain.dataType, data, Bool.not_false])]
    apply Original.Simulation.call
    intro value
    apply Classical.choice
    obtain ⟨physical, encoded⟩ := Domain.Value.encode_exists (carriers := model.toCarriers)
      (by simp only [Domain.dataType, data, Bool.not_false]) value
    obtain ⟨payload, payloadEq, read⟩ : ∃ payload,
        Domain.Payload.ofValue ty value = some payload ∧ physical = .data payload := by
      unfold Domain.Value.encode at encoded
      cases found : Domain.Payload.ofValue ty value with
      | none => simp only [found, Option.map_none] at encoded; cases encoded
      | some payload => exact ⟨payload, rfl, (Option.some.inj (by simpa only [found, Option.map_some] using encoded)).symm⟩
    subst physical
    refine ⟨?_⟩
    simp only [payloadEq, encoded, Domain.View.append,
      show Domain.sortsMatch [.data ty] [.data payload] = true from by
        simp only [Domain.sortsMatch, List.map_cons, List.map_nil, Domain.Value.encode_sort encoded, beq_self_eq_true],
      ↓reduceIte, PIR.Process.bind]
    have kept := ArtifactBinding.captures_trans retained (ArtifactBinding.captures_append environment [.data payload])
    apply Original.Simulation.checkpoint _ kept
    rw [preparationProof.prepend_eq]
    apply preparationProof.simulation model (.cons value binders) state.history captured _
      (related.bindData value encoded) kept _ _ _ _ (fun _ kept => kept)
    intro preparedEnvironment preparedRelated preparedRetained
    apply Original.Simulation.checkpoint _ preparedRetained
    rw [PIR.Process.bind_assoc]
    have valueReadback : Readback prepared (.cons (.present (.var .here)) .nil) [.data layout.length] :=
      .data _ valueRead .nil
    have physicalRead := valueReadback.payload preparedRelated
    have encodedSame := Option.some.inj (payloadEq.symm.trans physicalRead.choose_spec.1)
    apply (Original.Simulation.record state origin payload routing.context template stateRef layout.length pathRef
      preparedEnvironment _ (preparedRelated.readHistory stateRead)
      (by rw [encodedSame]; exact physicalRead.choose_spec.2)
      (preparedRelated.reachedCoordinates (frames.rename .there) pathRef pathRead)
      (by simpa only [ScopedFrames.eval_rename (target := .value ty :: scope) .there binders (.cons value binders) (fun _ => rfl) frames] using template_reached frames binders route) message).bind
    · intro process frame same
      subst frame
      exact preparedRetained
    · intro source target returned
      obtain ⟨same, appended⟩ := returned
      rw [same, appended]
      have kept := ArtifactBinding.captures_trans preparedRetained (ArtifactBinding.captures_append _
        [.transcript routing.context.suite (state.history ++ [.message origin payload])])
      exact .checkpoint _ kept
        (ih model tables bindings runs protocols _runBinding processes calleesHold selectionMeaning expectedFrames { state with history := state.history ++ [.message origin payload] } stack captured (.cons value binders)
          (reachedStack.trans (ScopedFrames.eval_rename .there binders _ (fun _ => rfl) frames).symm) _
          (Original.observation_frame preparedRelated routing.context.suite (.message origin payload)) kept)
  | @delivery context definitions callees selection out role scopes outputs history scope frames layout site field peer next rest replacement profile mode draw message binding
      contract request stateRef pathRef stateRead pathRead prepared preparation preparationProof
      observeStateRef observePathRef valueRead observeStateRead observePathRead tail ih =>
    let qualified := qualifyProtocolSite context.applicationPrefix site
    let queryOrigin := Domain.atCoordinates
      (routing.context.query (draw.qualify (draw.event[2]?.getD "")) (.draw field))
      ((frames.eval model binders).map (·.index))
    let messageOrigin := Domain.atCoordinates
      (routing.context.message qualified (context.roles peer) routing.context.producer)
      ((frames.eval model binders).map (·.index))
    have sourceRoute : routing.delivery state.frames qualified field (context.roles peer) =
        some (queryOrigin, messageOrigin) := by
      rw [reachedStack]
      exact binding.source _ (frames.sites_eval model binders)
    have asked : queryOrigin.request = some (.draw field) := by unfold queryOrigin Domain.atCoordinates; split <;> rfl
    have msg : messageOrigin.request = none := by unfold messageOrigin Domain.atCoordinates; split <;> rfl
    have queryTarget : Domain.queryOrigin routing.context routing.context.suite field draw
        ((frames.eval model binders).map (·.index)) = some queryOrigin := by
      rw [Domain.queryOrigin, ite_eq_left ⟨rfl, contract, request⟩,
        template_reached frames binders binding.drawRoute]
      change (if queryOrigin.request = some (.draw field) then some queryOrigin else none) = some queryOrigin
      exact ite_eq_left asked
    have folded : Original.fold routing (Occurrence.actions (.receive (.field field) qualified (context.roles peer))) state =
        Original.receive routing state (.field field) qualified (context.roles peer) := by
      simp only [Original.fold, Occurrence.actions, PIR.Process.interpretState, Original.operations, profile]
      exact PIR.Process.bind_done _
    change Original.Simulation _ _ (Original.fold routing
      ((Occurrence.actions (.receive (.field field) qualified (context.roles peer))).bind
        (fun reply => next.denoteOn model Occurrence.actions tables (LawResults.empty model)
          context runs processes (.cons reply binders))) state) _
    rw [Original.fold_bind, folded]
    simp only [Original.receive, mode, sourceRoute, PIR.Process.bind_assoc]
    apply Original.Simulation.checkpoint environment retained
    apply (Original.Simulation.queryField state queryOrigin field asked routing.context routing.context.suite
      draw stateRef pathRef environment _ (related.readHistory stateRead)
      (related.reachedCoordinates frames pathRef pathRead) queryTarget).bind
    · intro process frame same
      subst frame
      exact retained
    · intro source target returned
      rcases source with ⟨value, reached⟩
      obtain ⟨same, appended⟩ := returned
      dsimp only at same appended
      subst reached target
      have kept := ArtifactBinding.captures_trans retained (ArtifactBinding.captures_append environment
        [.data (.field field value), .transcript routing.context.suite (state.history ++ [.challenge queryOrigin])])
      apply Original.Simulation.checkpoint _ kept
      rw [preparationProof.prepend_eq]
      apply preparationProof.simulation model (.cons value binders) (state.history ++ [.challenge queryOrigin]) captured _
        (Original.query_frame related routing.context.suite field queryOrigin value) kept
        _ _ _ _ (fun _ kept => kept)
      intro preparedEnvironment preparedRelated preparedRetained
      apply Original.Simulation.checkpoint _ preparedRetained
      simp only [PIR.Process.bind]
      have valueReadback : Readback prepared (.cons (.present (.var .here)) .nil) [.data layout.length] :=
        .data _ valueRead .nil
      have physicalRead := valueReadback.payload preparedRelated
      have encodedSame : physicalRead.choose = .field field value := Option.some.inj physicalRead.choose_spec.1.symm
      have observed := Original.Simulation.record
        (carriers := model.toCarriers) ({ state with history := state.history ++ [.challenge queryOrigin] })
        messageOrigin (.field field value) routing.context message observeStateRef layout.length observePathRef
        preparedEnvironment ((frames.eval model binders).map (·.index))
        (preparedRelated.readHistory observeStateRead)
        (by rw [← encodedSame]; exact physicalRead.choose_spec.2)
        (by simpa only [ScopedFrames.eval_rename (target := .value (.field field) :: scope) .there binders (.cons value binders) (fun _ => rfl) frames] using
          preparedRelated.reachedCoordinates (frames.rename .there) observePathRef observePathRead)
        (template_reached frames binders binding.messageRoute) msg
      apply observed.bind
        (sourceNext := fun source => Original.fold routing
          (next.denoteOn model Occurrence.actions tables (LawResults.empty model) context runs processes
            (.cons value binders)) source.2)
      · intro process frame same
        subst frame
        exact preparedRetained
      · intro source target returned
        obtain ⟨same, appended⟩ := returned
        rw [same, appended]
        have kept := ArtifactBinding.captures_trans preparedRetained (ArtifactBinding.captures_append _
          [.transcript routing.context.suite (state.history ++ [.challenge queryOrigin] ++ [.message messageOrigin (.field field value)])])
        exact .checkpoint _ kept
          (ih model tables bindings runs protocols _runBinding processes calleesHold selectionMeaning expectedFrames { state with history := state.history ++ [.challenge queryOrigin] ++ [.message messageOrigin (.field field value)] } stack captured (.cons value binders)
            (reachedStack.trans (ScopedFrames.eval_rename .there binders _ (fun _ => rfl) frames).symm) _
            (Original.observation_frame preparedRelated routing.context.suite (.message messageOrigin (.field field value))) kept)
  | indicesEmpty tail ih =>
    have kept := ArtifactBinding.captures_trans retained
      (ArtifactBinding.captures_append environment [.indices []])
    apply Original.Simulation.checkpoint environment retained
    change Original.Simulation _ _ _ ((PIR.Process.done (environment ++ [.indices []])).bind _)
    exact .checkpoint _ kept
      (ih model tables bindings runs protocols _runBinding processes calleesHold selectionMeaning expectedFrames state stack captured binders reachedStack _ related.indicesEmpty kept)
  | indicesAppend terms term coordinateRef indexRef coordinates index tail ih =>
    obtain ⟨step, extended⟩ := related.indicesAppend coordinates index
    have kept := ArtifactBinding.captures_trans retained (ArtifactBinding.captures_append environment
      [.indices ((terms ++ [term]).map fun value => value.eval (LawResults.empty model) binders)])
    apply Original.Simulation.checkpoint environment retained
    rw [step]
    exact .checkpoint _ kept (ih model tables bindings runs protocols _runBinding processes calleesHold selectionMeaning expectedFrames state stack captured binders reachedStack _ extended kept)
  | @publicQuery context definitions callees selection out role scopes outputs history scope frames layout site field handle selected next rest mode publicService contract request template route
      stateRef pathRef stateRead pathRead tail ih =>
    subst handle
    let qualified := qualifyProtocolSite context.applicationPrefix site
    let origin := Domain.atCoordinates (routing.context.query qualified (.draw field))
      ((frames.eval model binders).map (·.index))
    have sourceRoute : routing.draw state.frames qualified field routing.selectedHandle = some origin := by
      rw [reachedStack]
      exact Original.Routing.draw_of_static publicService route _ (frames.sites_eval model binders)
    have asked : origin.request = some (.draw field) := by
      unfold origin Domain.atCoordinates
      split <;> rfl
    have folded : Original.fold routing (Occurrence.actions
        (.query qualified field (.cons routing.selectedHandle .nil))) state =
        Original.queryField state origin field := by
      change (Original.query routing state qualified field routing.selectedHandle).bind PIR.Process.done = _
      rw [Original.query, mode, sourceRoute]
      exact PIR.Process.bind_done _
    change Original.Simulation _ _ (Original.fold routing
      ((Occurrence.actions (.query qualified field (.cons routing.selectedHandle .nil))).bind
        (fun reply => next.denoteOn model Occurrence.actions tables (LawResults.empty model)
          context runs processes (.cons reply binders))) state) _
    rw [Original.fold_bind, folded]
    apply Original.Simulation.checkpoint environment retained
    apply (Original.Simulation.queryField state origin field asked routing.context routing.context.suite
      template stateRef pathRef environment _ (related.readHistory stateRead)
      (related.reachedCoordinates frames pathRef pathRead)
      (query_reached frames binders contract request route)).bind
    · intro process frame same
      subst frame
      exact retained
    · intro source target returned
      rcases source with ⟨value, reached⟩
      obtain ⟨same, appended⟩ := returned
      dsimp only at same appended
      subst reached target
      have kept := ArtifactBinding.captures_trans retained (ArtifactBinding.captures_append environment
        [.data (.field field value), .transcript routing.context.suite (state.history ++ [.challenge origin])])
      exact .checkpoint _ kept (ih model tables bindings runs protocols _runBinding processes calleesHold selectionMeaning expectedFrames { state with history := state.history ++ [.challenge origin] } stack captured (.cons value binders)
        (reachedStack.trans (ScopedFrames.eval_rename .there binders _ (fun _ => rfl) frames).symm) _
        (Original.query_frame related routing.context.suite field origin value) kept)
  | @localQuery context definitions callees selection out role scopes outputs history scope frames layout site field handle next rest port template mode binding contract
      coordinates readback tail ih =>
    let qualified := qualifyProtocolSite context.applicationPrefix site
    let origin := Domain.atCoordinates binding.origin ((frames.eval model binders).map (·.index))
    have asked : origin.request = some (.draw field) := by
      unfold origin Domain.atCoordinates
      split <;> rfl
    have folded : Original.fold routing (Occurrence.actions
        (.query qualified field (.cons handle .nil))) state =
        Original.query routing state qualified field handle := by
      simp only [Original.fold, Occurrence.actions, PIR.Process.interpretState, Original.operations]
      exact PIR.Process.bind_done _
    change Original.Simulation _ _ (Original.fold routing
      ((Occurrence.actions (.query qualified field (.cons handle .nil))).bind
        (fun reply => next.denoteOn model Occurrence.actions tables (LawResults.empty model)
          context runs processes (.cons reply binders))) state) _
    rw [Original.fold_bind, folded]
    apply Original.Simulation.checkpoint environment retained
    apply (Original.Simulation.localQuery routing state qualified field handle port origin
      (by rw [reachedStack]; exact mode.sound _ (frames.sites_eval model binders))
      (by rw [reachedStack]; exact binding.source _ (frames.sites_eval model binders)) asked
      template coordinates environment _ (readback.read related) contract
      (by simpa only [origin, ScopedFrames.coordinates_eval] using binding.target _ (frames.sites_eval model binders))).bind
    · intro process frame same
      subst frame
      exact retained
    · intro source target returned
      rcases source with ⟨value, reached⟩
      obtain ⟨same, appended⟩ := returned
      dsimp only at same appended
      subst reached target
      have kept := ArtifactBinding.captures_trans retained (ArtifactBinding.captures_append environment
        [.data (.field field value)])
      exact .checkpoint _ kept (ih model tables bindings runs protocols _runBinding processes calleesHold selectionMeaning expectedFrames state stack captured (.cons value binders)
        (reachedStack.trans (ScopedFrames.eval_rename .there binders _ (fun _ => rfl) frames).symm) _
        (related.bindData (ty := .field field) value rfl) kept)
  | @«repeat» context definitions callees selection out role scopes outputs history scope frames layout spec site callback count initial captures next body rest
      roster distinct active visible mappedVisible countReference countRead stateReferences initialReferences
      yieldData yielded initialHistory bodyHistory initialRead historyRead initialProfile bodyProfile yieldLocations
      bodyForm normalized bodyCertificate tail bodyIH tailIH =>
    apply Classical.choice
    have encodedData := visibleState_data visible
    obtain ⟨initialValues, initialPresent, initialReading⟩ := read_components initialRead binders related
    let data := Original.encodeHelperResult initialValues
    have encoded : Domain.encodeValues initialValues = some data := Original.encodeHelperResult_eq encodedData initialValues
    have located : Original.HistoryLocation routing.context initialHistory environment state.history := by
      apply historyLocation_of_profile initialProfile
      cases historyRead with
      | plain => trivial
      | transcript reference checked => exact related.readHistory checked
    have fullRead := Original.profileReferences_read initialProfile (initialReading.trans encoded) located
    have initialCarried : Original.FramedCarriedValues routing.context (context.roles role)
        (context.mapScopes spec.stateScopes) state.frames
        (initialValues.present, state) (Domain.inputFrame routing.context data state.history) :=
      ⟨rfl, data, (visibleState_encode mappedVisible model initialValues).trans encoded, rfl⟩
    have loopCertificate := Original.Simulation.framedRepeat routing spec context (context.roles role) active
      (Comps.eval (LawResults.empty model) captures binders)
      ((runsAtOn model Occurrence.actions Occurrence.iterations tables protocols context role).callback spec callback)
      site (body model) environment yielded (spec.state.map ValueSort.data) (visibleState_schema mappedVisible)
      state.frames (fun value reached carried index carriedRelated => by
        apply Classical.choice
        obtain ⟨closed, physicals, encodedValues, carriedFrame⟩ := carriedRelated
        obtain ⟨actual, present, encodedActual⟩ := visibleState_values mappedVisible model value encodedValues
        subst value carried
        have entered := related.repeatEnter routing.context binders actual index reached.history encodedActual
        let nextBinders : Binders model (RepeatScope spec.state scope) := .cons index (.cons actual.present binders)
        have bodyMeaning := normalizeRegion_soundOn (model := model) (actions := Occurrence.actions)
          (iterations := Occurrence.iterations) (tables := tables) (protocols := protocols) (context := context)
          {strict := true, callees := callees} (LawResults.empty model) processes role roster distinct
          (Comps.eval (LawResults.empty model) (repeatInputs captures) nextBinders)
          (LawsHold.empty _ _) (calleesHold _) callback
          ⟨repeatInputs captures, repeatInputs captures⟩ bodyForm normalized
          (bodyForm.lawsMatch_of_callsMatch bodyCertificate.callsMatch) nextBinders rfl
        have sourceInputs := repeatInputs_eval binders actual.present index captures
        have bodyStack : (reached.frames ++ [⟨qualifyProtocolSite context.applicationPrefix site,index⟩]) =
            (repeatFrames frames (qualifyProtocolSite context.applicationPrefix site)).eval model nextBinders := by
          rw [repeatFrames_eval]
          rw [closed, reachedStack]
        have checked := bodyIH model tables bindings runs protocols _runBinding processes calleesHold selectionMeaning (reached.frames ++ [⟨qualifyProtocolSite context.applicationPrefix site,index⟩])
          {reached with frames := reached.frames ++ [⟨qualifyProtocolSite context.applicationPrefix site,index⟩]}
          rfl environment nextBinders bodyStack _ entered (ArtifactBinding.captures_append environment _)
        rw [_runBinding] at checked
        have bodySource :
            (runsAtOn model Occurrence.actions Occurrence.iterations tables protocols context role).callback spec callback
              (.cons (some index) ((maskValues (context.roles role) (context.mapScopes spec.stateScopes)
                actual.present).append (Comps.eval (LawResults.empty model) captures binders))) =
            bodyForm.denoteOn model Occurrence.actions tables (LawResults.empty model) context
              (runsAtOn model Occurrence.actions Occurrence.iterations tables protocols context role) processes nextBinders := by
          rw [visibleState_mask mappedVisible]
          exact (congrArg (fun inputs => callback.denote (meaningAtOn model Occurrence.actions
            Occurrence.iterations tables protocols context role) inputs.get) sourceInputs.symm).trans bodyMeaning
        refine ⟨?_⟩
        rw [bodySource]
        apply checked.mapRelations
        · intro original final returned
          obtain ⟨read, stack, historyRead, _⟩ := returned
          rw [visibleState_mask visible] at read
          obtain ⟨nextData, nextEncoded, nextRead⟩ := Original.outputReferences_read original.1 yieldLocations read
          obtain ⟨nextValues, nextPresent, nextEncoding⟩ := visibleState_values visible model original.1 nextEncoded
          have mappedEncoding := (visibleState_encode mappedVisible model nextValues).trans nextEncoding
          have nextLocated := historyLocation_of_profile (environment := final) (history := original.2.history) bodyProfile historyRead
          have fullReading := Original.profileReferences_read bodyProfile nextRead nextLocated
          let nextFrame := Domain.inputFrame routing.context nextData original.2.history
          have nextRelated : Original.FramedCarriedValues routing.context (context.roles role)
              (context.mapScopes spec.stateScopes) state.frames
              (original.1, ⟨state.frames, original.2.history⟩) nextFrame :=
            ⟨rfl, nextData, by rw [nextPresent]; exact mappedEncoding, rfl⟩
          refine ⟨stack, nextFrame, fullReading, ?_, ?_⟩
          · exact nextRelated.2.sorts (visibleState_schema mappedVisible)
          · exact ⟨closed, nextRelated.2⟩
        · intro _ _ kept
          exact kept)
      (count.eval (LawResults.empty model) binders) countReference initialReferences (related.index countRead)
      initialValues.present state (Domain.inputFrame routing.context data state.history) fullRead initialCarried
    refine ⟨?_⟩
    rw [_runBinding]
    change Original.Simulation _ _ (Original.fold routing
      ((denoteRepeatOn spec context (context.roles role) (some (count.eval (LawResults.empty model) binders))
        (Comps.eval (LawResults.empty model) initial binders)
        (Comps.eval (LawResults.empty model) captures binders)
        ((runsAtOn model Occurrence.actions Occurrence.iterations tables protocols context role).callback spec callback)
        Occurrence.iterations site).bind fun values => next.denoteOn model Occurrence.actions tables
          (LawResults.empty model) context (runsAtOn model Occurrence.actions Occurrence.iterations tables protocols context role)
          processes (.cons values binders)) state) _
    rw [initialPresent, Original.fold_bind]
    apply Original.Simulation.checkpoint environment retained
    apply (loopCertificate.mapRelations (fun _ _ related => related)
      (fun _ _ kept => ArtifactBinding.captures_trans retained kept)).bind
    · intro _ _ kept
      exact kept
    · intro original final returned
      apply Classical.choice
      obtain ⟨carried, ⟨closed, physicals, encodedValues, carriedFrame⟩, finalFrame⟩ := returned
      obtain ⟨actual, present, encodedActual⟩ := visibleState_values mappedVisible model original.1 encodedValues
      rcases original with ⟨value, reached⟩
      dsimp only at present closed carriedFrame finalFrame
      subst value carried final
      have kept := ArtifactBinding.captures_trans retained (ArtifactBinding.captures_append environment
        (Domain.inputFrame routing.context physicals reached.history))
      refine ⟨.checkpoint _ kept ?_⟩
      rw [← _runBinding]
      exact tailIH model tables bindings runs protocols _runBinding processes calleesHold selectionMeaning expectedFrames reached (closed.trans stack) captured (.cons actual.present binders)
        (closed.trans reachedStack |>.trans (ScopedFrames.eval_rename .there binders _ (fun _ => rfl) frames).symm)
        _ (related.repeatExit routing.context binders actual reached.history encodedActual) kept
  | @projectedRepeat context definitions callees selection out role scopes outputs history scope frames layout spec site callback count initial captures next body rest
      roster distinct active visibility stateSorts schema countReference countRead initialLocations yieldLocations
      stateReferences initialReferences yieldData yielded initialHistory bodyHistory initialRead initialProjection yieldProjection
      historyRead initialProfile bodyProfile bodyForm normalized bodyCertificate nextMatched tail bodyIH tailIH =>
    apply Classical.choice
    let initialValues := Comps.eval (LawResults.empty model) initial binders
    obtain ⟨data, encoded, initialReading⟩ := Original.outputReferences_read initialValues initialProjection (initialRead.sound related)
    have localInitial := Original.roleOutputValues_mask role initialValues encoded
    have mappedInitial : Original.roleOutputValues (context.roles role) (context.mapScopes spec.stateScopes)
        (maskValues (context.roles role) (context.mapScopes spec.stateScopes) initialValues) = some data := by
      rw [← mask_visibility visibility, localInitial, ← roleValues_visibility visibility]
      exact encoded
    have located : Original.HistoryLocation routing.context initialHistory environment state.history := by
      apply historyLocation_of_profile initialProfile
      cases historyRead with
      | plain => trivial
      | transcript reference checked => exact related.readHistory checked
    have fullRead := Original.profileReferences_read initialProfile initialReading located
    have initialCarried : Original.ProjectedCarried routing.context (context.roles role)
        (context.mapScopes spec.stateScopes) state.frames (initialValues, state)
        (Domain.inputFrame routing.context data state.history) := ⟨rfl, data, mappedInitial, rfl⟩
    have loopCertificate := Original.Simulation.projectedFramedRepeat routing spec context (context.roles role) active
      (Comps.eval (LawResults.empty model) captures binders)
      ((runsAtOn model Occurrence.actions Occurrence.iterations tables protocols context role).callback spec callback)
      site (body model) environment yielded stateSorts schema state.frames
      (fun value reached carried index carriedRelated => by
        apply Classical.choice
        obtain ⟨closed, physicals, encodedValues, carriedFrame⟩ := carriedRelated
        have localEncoding : Original.roleOutputValues role spec.stateScopes
            (maskValues role spec.stateScopes value) = some physicals := by
          rw [mask_visibility visibility, roleValues_visibility visibility]
          exact encodedValues
        subst carried
        have entered := related.projectedEnter routing.context role spec.stateScopes binders value index reached.history localEncoding
        let nextBinders : Binders model (RepeatScope spec.state scope) := .cons index (.cons value binders)
        have bodyMeaning := normalizeRegion_soundOn (model := model) (actions := Occurrence.actions)
          (iterations := Occurrence.iterations) (tables := tables) (protocols := protocols) (context := context)
          {strict := true, callees := callees} (LawResults.empty model) processes role roster distinct
          (Comps.eval (LawResults.empty model) (projectedInputs role captures) nextBinders)
          (LawsHold.empty _ _) (calleesHold _) callback
          ⟨projectedInputs role captures, projectedInputs role captures⟩ bodyForm normalized
          (bodyForm.lawsMatch_of_callsMatch bodyCertificate.callsMatch) nextBinders rfl
        have sourceInputs := projectedInputs_eval role binders value index captures
        have bodyStack : (reached.frames ++ [⟨qualifyProtocolSite context.applicationPrefix site,index⟩]) =
            (repeatFrames frames (qualifyProtocolSite context.applicationPrefix site)).eval model nextBinders := by
          rw [repeatFrames_eval, closed, reachedStack]
        have checked := bodyIH model tables bindings runs protocols _runBinding processes calleesHold selectionMeaning (reached.frames ++ [⟨qualifyProtocolSite context.applicationPrefix site,index⟩])
          {reached with frames := reached.frames ++ [⟨qualifyProtocolSite context.applicationPrefix site,index⟩]}
          rfl environment nextBinders bodyStack _ entered (ArtifactBinding.captures_append environment _)
        rw [_runBinding] at checked
        have bodySource :
            (runsAtOn model Occurrence.actions Occurrence.iterations tables protocols context role).callback spec callback
              (.cons (some index) ((maskValues (context.roles role) (context.mapScopes spec.stateScopes)
                value).append (Comps.eval (LawResults.empty model) captures binders))) =
            bodyForm.denoteOn model Occurrence.actions tables (LawResults.empty model) context
              (runsAtOn model Occurrence.actions Occurrence.iterations tables protocols context role) processes nextBinders := by
          rw [← mask_visibility visibility]
          exact (congrArg (fun inputs => callback.denote (meaningAtOn model Occurrence.actions
            Occurrence.iterations tables protocols context role) inputs.get) sourceInputs.symm).trans bodyMeaning
        refine ⟨?_⟩
        rw [bodySource]
        apply checked.mapRelations
        · intro original final returned
          obtain ⟨read, stack, historyRead, _⟩ := returned
          obtain ⟨nextData, nextEncoded, nextRead⟩ := Original.outputReferences_read
            (maskValues role spec.stateScopes original.1) yieldProjection read
          have mappedEncoding : Original.roleOutputValues (context.roles role) (context.mapScopes spec.stateScopes)
              (maskValues (context.roles role) (context.mapScopes spec.stateScopes) original.1) = some nextData := by
            rw [← mask_visibility visibility, ← roleValues_visibility visibility]
            exact nextEncoded
          have nextLocated := historyLocation_of_profile (environment := final) (history := original.2.history) bodyProfile historyRead
          have fullReading := Original.profileReferences_read bodyProfile nextRead nextLocated
          let nextFrame := Domain.inputFrame routing.context nextData original.2.history
          have nextRelated : Original.ProjectedCarried routing.context (context.roles role)
              (context.mapScopes spec.stateScopes) state.frames
              (original.1, ⟨state.frames, original.2.history⟩) nextFrame := ⟨rfl,nextData,mappedEncoding,rfl⟩
          refine ⟨stack, nextFrame, fullReading, ?_, ?_⟩
          · exact nextRelated.2.sorts schema
          · exact ⟨closed, nextRelated.2⟩
        · intro _ _ kept; exact kept)
      (count.eval (LawResults.empty model) binders) countReference initialReferences (related.index countRead)
      initialValues state (Domain.inputFrame routing.context data state.history) fullRead initialCarried
    refine ⟨?_⟩
    rw [_runBinding]
    change Original.Simulation _ _ (Original.fold routing
      ((denoteRepeatOn spec context (context.roles role) (some (count.eval (LawResults.empty model) binders))
        initialValues (Comps.eval (LawResults.empty model) captures binders)
        ((runsAtOn model Occurrence.actions Occurrence.iterations tables protocols context role).callback spec callback)
        Occurrence.iterations site).bind fun values => next.denoteOn model Occurrence.actions tables
          (LawResults.empty model) context (runsAtOn model Occurrence.actions Occurrence.iterations tables protocols context role)
          processes (.cons values binders)) state) _
    rw [Original.repeat_bind_mask, Original.fold_bind]
    apply Original.Simulation.checkpoint environment retained
    apply (loopCertificate.mapRelations (fun _ _ related => related)
      (fun _ _ kept => ArtifactBinding.captures_trans retained kept)).bind
    · intro _ _ kept; exact kept
    · intro original final returned
      apply Classical.choice
      obtain ⟨carried, ⟨closed, physicals, encodedValues, carriedFrame⟩, finalFrame⟩ := returned
      rcases original with ⟨value, reached⟩
      dsimp only at closed carriedFrame finalFrame
      subst carried final
      have localEncoding : Original.roleOutputValues role spec.stateScopes
          (maskValues role spec.stateScopes value) = some physicals := by
        rw [mask_visibility visibility, roleValues_visibility visibility]
        exact encodedValues
      have kept := ArtifactBinding.captures_trans retained (ArtifactBinding.captures_append environment
        (Domain.inputFrame routing.context physicals reached.history))
      refine ⟨.checkpoint _ kept ?_⟩
      dsimp only
      rw [← mask_visibility visibility, ← ConnectionSubstitution.maskNext_denote role spec.stateScopes
        Occurrence.actions tables context _ processes next binders value, ← _runBinding]
      exact tailIH model tables bindings runs protocols _runBinding processes calleesHold selectionMeaning expectedFrames reached (closed.trans stack) captured (.cons value binders)
        (closed.trans reachedStack |>.trans (ScopedFrames.eval_rename .there binders _ (fun _ => rfl) frames).symm)
        _ (related.projectedExit routing.context role spec.stateScopes binders value reached.history localEncoding) kept
  | @application context definitions callees out role scopes outputs history scope frames layout
      payload same library callee signature signatureMatch roles site arguments calleeOutputs calleeHistory
      spine extent physicalExtent admission bodyCertificate next rest tail bodyIH tailIH =>
    rcases selectionMeaning with ⟨rfl, rfl, rfl⟩
    subst definitions
    let selected := library.entry callee
    have instantiated := ConnectionSubstitution.form_denote
      (Arguments.eval (LawResults.empty model) arguments binders) binders
      (fun binder => entryAt arguments binder) (ConnectionSubstitution.arguments_related arguments binders)
      Occurrence.actions (Occurrence.helpers model payload) (context.enter site roles)
      (runsAtOn model Occurrence.actions Occurrence.iterations (Occurrence.helpers model payload)
        (Occurrence.table model payload) (context.enter site roles) (calleeAt callees callee).role)
      (selected.earlier.processes model) selected.form
    have aligned := bodyIH model (Occurrence.helpers model payload) (fun _ => rfl)
      (runsAtOn model Occurrence.actions Occurrence.iterations (Occurrence.helpers model payload)
        (Occurrence.table model payload) (context.enter site roles) (calleeAt callees callee).role)
      (Occurrence.table model payload) rfl (selected.earlier.processes model) (selected.earlier.holds model)
      ⟨rfl,rfl,rfl⟩ expectedFrames state stack environment binders reachedStack environment related
      (by simp [ArtifactBinding.Captures])
    have extentProof := physicalExtent.yields model environment related.length.symm
    have aligned := aligned.withTargetInvariant extentProof
    change Original.Simulation _ _ (Original.fold routing
      ((library.processes model callee (context.enter site roles)
        (Arguments.eval (LawResults.empty model) arguments binders)).bind fun values =>
        next.denoteOn model Occurrence.actions (Occurrence.helpers model payload) (LawResults.empty model)
          context runs (library.processes model) (.cons values binders)) state) _
    rw [library.processes_entry, ConnectionLibrary.Entry.process_form, ← instantiated,
      Original.fold_bind, spine.plug_eq_bind]
    apply aligned.bind
    · intro _ frame kept
      exact ArtifactBinding.captures_trans retained kept
    · intro source frame returned
      obtain ⟨returned, size⟩ := returned
      have kept := ArtifactBinding.captures_trans retained returned.2.2.2
      have nextRelated := related.applicationExit binders returned.2.2.2 extent size source.1
        (calleeAt callees callee).role (calleeAt callees callee).signature.outputScopes calleeOutputs
        returned.1 calleeHistory routing.context.suite returned.2.2.1
      exact tailIH model (Occurrence.helpers model payload) (fun _ => rfl) runs
        (Occurrence.table model payload) _runBinding (library.processes model) (library.holds model)
        ⟨rfl,rfl,rfl⟩ expectedFrames source.2 returned.2.1 captured (.cons source.1 binders)
        (returned.2.1.trans (stack.symm.trans reachedStack) |>.trans
          (ScopedFrames.eval_rename .there binders _ (fun _ => rfl) frames).symm)
        frame nextRelated kept
  | @guard context definitions callees selection out role scopes outputs history scope frames layout ty equality left right next rest reference readback tail ih =>
    have readCondition := readback.read related
    apply Original.Simulation.checkpoint environment retained
    rw [Domain.View.guard_eq reference environment _ readCondition]
    let condition := left.eval (LawResults.empty model) binders = right.eval (LawResults.empty model) binders
    letI : Decidable condition := equality.decide model _ _
    by_cases holds : condition
    · change left.eval (LawResults.empty model) binders = right.eval (LawResults.empty model) binders at holds
      simpa only [Form.denoteOn, Form.denoteWithOn, holds, ↓reduceIte, decide_true,
        PIR.Process.bind] using
        (Original.Simulation.checkpoint environment retained
          (ih model tables bindings runs protocols _runBinding processes calleesHold selectionMeaning expectedFrames state stack captured binders reachedStack environment (readback.refined related holds) retained))
    · change ¬ (left.eval (LawResults.empty model) binders = right.eval (LawResults.empty model) binders) at holds
      simp only [Form.denoteOn, Form.denoteWithOn, holds, ↓reduceIte, decide_false,
        Original.fold_halt]
      exact .halt .reject
  | trueGuard reference readback tail ih =>
    apply Original.Simulation.checkpoint environment retained
    rw [Domain.View.guard_eq reference environment true (read_boolean readback related)]
    exact .checkpoint environment retained (ih model tables bindings runs protocols _runBinding processes calleesHold selectionMeaning expectedFrames state stack captured binders reachedStack environment related retained)
  | falseGuard reference readback rest =>
    apply Original.Simulation.checkpoint environment retained
    rw [Domain.View.guard_eq reference environment false (read_boolean readback related)]
    exact .halt .reject

/-- Use a finite checked source library without any author-supplied callee
process equations. This also supplies the library law at every repeat frame. -/
@[no_expose] noncomputable def Derivation.unselectedLibrarySimulation
    {payload : UnitPayload} {routing : Original.Routing} {context : ProtocolContext}
    {callees : List CalleeKey} {out : List Ty} {role : Nat} {scopes : List (List Nat)}
    {outputs : List Original.Location} {history : Option Nat}
    {scope : Scope} {frames : ScopedFrames scope} {layout : Layout scope}
    {form : Form [] callees scope out} {target : Block}
    (derivation : Derivation routing context payload.definitions callees out role scopes outputs history
      frames layout form target)
    (library : ConnectionLibrary.Library payload callees) (model : DomainModel)
    (state : Original.State model.toCarriers) (captured : Domain.Environment model.toCarriers)
    (binders : Binders model scope) (stack : state.frames = frames.eval model binders)
    (environment : Domain.Environment model.toCarriers)
    (related : Holds model binders state.history layout environment)
    (retained : ArtifactBinding.Captures captured environment) :
    Original.Simulation (Returns routing role scopes outputs history state.frames captured)
      (fun _ frame => ArtifactBinding.Captures captured frame)
      (Original.fold routing (form.denoteOn model Occurrence.actions (Occurrence.helpers model payload)
        (LawResults.empty model) context
        (runsAtOn model Occurrence.actions Occurrence.iterations (Occurrence.helpers model payload)
          (Occurrence.table model payload) context role)
        (library.processes model) binders) state) (target model environment) :=
  sound derivation model (Occurrence.helpers model payload) (fun _ => rfl)
    (runsAtOn model Occurrence.actions Occurrence.iterations (Occurrence.helpers model payload)
      (Occurrence.table model payload) context role) (Occurrence.table model payload) rfl
    (library.processes model) (library.holds model) trivial state.frames state rfl captured binders stack
    environment related retained

/-- The canonical selected-library specialization of the structural theorem. -/
@[no_expose] noncomputable def Alignment.librarySimulation
    {payload : UnitPayload} {routing : Original.Routing} {context : ProtocolContext}
    {callees : List CalleeKey} (library : ConnectionLibrary.Library payload callees)
    {out : List Ty} {role : Nat} {scopes : List (List Nat)}
    {outputs : List Original.Location} {history : Option Nat}
    {scope : Scope} {frames : ScopedFrames scope} {layout : Layout scope}
    {form : Form [] callees scope out} {target : Block}
    (derivation : Derivation routing context payload.definitions callees out role scopes outputs history
      frames layout form target (selection := .selected payload rfl library))
    (model : DomainModel) (state : Original.State model.toCarriers)
    (captured : Domain.Environment model.toCarriers) (binders : Binders model scope)
    (stack : state.frames = frames.eval model binders) (environment : Domain.Environment model.toCarriers)
    (related : Holds model binders state.history layout environment)
    (retained : ArtifactBinding.Captures captured environment) :
    Original.Simulation (Returns routing role scopes outputs history state.frames captured)
      (fun _ frame => ArtifactBinding.Captures captured frame)
      (Original.fold routing (form.denoteOn model Occurrence.actions (Occurrence.helpers model payload)
        (LawResults.empty model) context
        (runsAtOn model Occurrence.actions Occurrence.iterations (Occurrence.helpers model payload)
          (Occurrence.table model payload) context role) (library.processes model) binders) state)
      (target model environment) :=
  sound derivation model (Occurrence.helpers model payload) (fun _ => rfl)
    (runsAtOn model Occurrence.actions Occurrence.iterations (Occurrence.helpers model payload)
      (Occurrence.table model payload) context role) (Occurrence.table model payload) rfl
    (library.processes model) (library.holds model) ⟨rfl,rfl,rfl⟩ state.frames state rfl captured binders stack
    environment related retained

/-- The source fixes participant visibility before proposal. The history selector
is fixed by the caller and must agree with the construction profile. -/
structure Certificate (routing : Original.Routing) (context : ProtocolContext)
    (definitions : List CheckedDefinition) (role roster : Nat) (source : CheckedProtocol)
    (pattern : InputPattern source.inputs) (outputs : List Original.Location) (history : Option Nat)
    (frames : ScopedFrames pattern.scope) (layout : Layout pattern.scope) (target : Block)
    (callees : List CalleeKey := [])
    (selection : ConnectionLibrary.Selection definitions callees := .unselected) where
  self : context.roles role = routing.self
  historyProfile : historyPolicy routing.context.profile history = true
  form : Form [] callees pattern.scope source.outputs
  normalized : normalize {strict := true, callees := callees} source.body role roster pattern = .ok form
  alignment : Derivation routing context definitions callees (selection := selection) source.outputs role source.outputScopes outputs history
    frames layout form target

/-- Kernel-checked connection to the actual occurrence-aware source denotation.
Admission, ABI assembly and property installation remain root obligations. -/
@[no_expose] noncomputable def Certificate.simulation
    {routing : Original.Routing} {context : ProtocolContext} {definitions : List CheckedDefinition}
    {role roster : Nat} {source : CheckedProtocol} {pattern : InputPattern source.inputs}
    {outputs : List Original.Location} {history : Option Nat} {frames : ScopedFrames pattern.scope}
    {layout : Layout pattern.scope} {target : Block}
    (certificate : Certificate routing context definitions role roster source pattern outputs history frames layout target)
    (distinct : RosterDistinct context role roster)
    (model : DomainModel) (tables : Tables model (Occurrence.signature model.toCarriers))
    (bindings : ConnectionHelpers.TablesMatch model definitions tables)
    (protocols : ProtocolTable model.Value (Occurrence.signature model.toCarriers))
    (state : Original.State model.toCarriers)
    (binders : Binders model pattern.scope) (stack : state.frames = frames.eval model binders) (abi : Original.InputABI)
    (captured : Domain.Environment model.toCarriers)
    (sorts : Domain.sortsMatch abi.sorts captured = true)
    (bound : Original.LocationsBound captured.length abi.locations)
    (inputRead : Original.ValuesHolds captured abi.locations (pattern.environment model binders))
    (environment : Domain.Environment model.toCarriers)
    (related : Holds model binders state.history layout environment)
    (retained : ArtifactBinding.Captures captured environment) :
    Original.Simulation (Returns routing role source.outputScopes outputs history state.frames captured)
      (Original.InputLive abi (pattern.environment model binders) captured)
      (Original.fold routing (source.body.denote
        (participantMeaningWithOn model (.silent _) Occurrence.actions tables (context.roles role)
          protocols context Occurrence.iterations) (pattern.environment model binders).get) state)
      (target model environment) := by
  rw [normalize_occurrence_sound {strict := true} source.body role roster pattern certificate.form
    certificate.normalized certificate.alignment.callsMatch distinct (LawResults.empty model)
    (fun (entry : Fin 0) => entry.elim0) binders (LawsHold.empty _ _) (fun (entry : Fin 0) => entry.elim0)]
  apply (sound certificate.alignment model tables bindings
    (runsAtOn model Occurrence.actions Occurrence.iterations tables protocols context role) protocols rfl
    (fun (entry : Fin 0) => entry.elim0) (fun inputs => noCallees_hold _ inputs) trivial state.frames state rfl captured
    binders stack environment related retained).mapRelations
  · intro source target returned
    exact returned
  · intro source frame kept
    exact Original.inputLive_of_captures abi (pattern.environment model binders) captured frame source
      sorts bound inputRead kept

@[no_expose] noncomputable def Certificate.selectedSimulation
    {routing : Original.Routing} {context : ProtocolContext} {payload : UnitPayload}
    {callees : List CalleeKey} {library : ConnectionLibrary.Library payload callees}
    {role roster : Nat} {source : CheckedProtocol} {pattern : InputPattern source.inputs}
    {outputs : List Original.Location} {history : Option Nat} {frames : ScopedFrames pattern.scope}
    {layout : Layout pattern.scope} {target : Block}
    (certificate : Certificate routing context payload.definitions role roster source pattern outputs history frames layout target
      callees (.selected payload rfl library))
    (distinct : RosterDistinct context role roster)
    (model : DomainModel)
    (state : Original.State model.toCarriers)
    (binders : Binders model pattern.scope) (stack : state.frames = frames.eval model binders) (abi : Original.InputABI)
    (captured : Domain.Environment model.toCarriers)
    (sorts : Domain.sortsMatch abi.sorts captured = true)
    (bound : Original.LocationsBound captured.length abi.locations)
    (inputRead : Original.ValuesHolds captured abi.locations (pattern.environment model binders))
    (environment : Domain.Environment model.toCarriers)
    (related : Holds model binders state.history layout environment)
    (retained : ArtifactBinding.Captures captured environment) :
    Original.Simulation (Returns routing role source.outputScopes outputs history state.frames captured)
      (Original.InputLive abi (pattern.environment model binders) captured)
      (Original.fold routing (source.body.denote
        (participantMeaningWithOn model (.silent _) Occurrence.actions (Occurrence.helpers model payload) (context.roles role)
          (Occurrence.table model payload) context Occurrence.iterations) (pattern.environment model binders).get) state)
      (target model environment) := by
  rw [normalize_occurrence_sound {strict := true, callees := callees} source.body role roster pattern certificate.form
    certificate.normalized certificate.alignment.callsMatch distinct (LawResults.empty model)
    (library.processes model) binders (LawsHold.empty _ _) (library.holds model _)]
  apply (sound certificate.alignment model (Occurrence.helpers model payload) (fun _ => rfl)
    (runsAtOn model Occurrence.actions Occurrence.iterations (Occurrence.helpers model payload) (Occurrence.table model payload) context role) (Occurrence.table model payload) rfl
    (library.processes model) (library.holds model) ⟨rfl,rfl,rfl⟩ state.frames state rfl captured
    binders stack environment related retained).mapRelations
  · intro source target returned
    exact returned
  · intro source frame kept
    exact Original.inputLive_of_captures abi (pattern.environment model binders) captured frame source
      sorts bound inputRead kept

end Zkc.Construction.ConnectionCertificate
