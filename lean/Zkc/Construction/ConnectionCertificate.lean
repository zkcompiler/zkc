module

public import Zkc.Construction.ConnectionComputation
public import Zkc.Construction.ConnectionPresence
public import Zkc.Construction.ConnectionHelpers
public import Zkc.Construction.ConnectionActions
public import Zkc.Construction.OriginalFrameRelations

@[expose] public section

/-! A finite, intrinsically checked alignment derivation for straight-line plain
connections. Indices fix the actual source form and actual Domain.View block.
Constructors contain only finite static checks and smaller derivations. There
is no root semantic equation, Simulation, helper law or successful-value premise
in a constructor. Helpers carry finite exact declaration bindings. Loops and
queries deliberately have no rule in this unit.

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
      (checked : layout[reference]? = some (.data (.present (equalityTerm equality left right)))) :
      GuardReadback layout equality left right reference
  | boolean (condition : Term [] scope .boolean) (reference : Nat)
      (checked : layout[reference]? = some (.data (.present condition))) :
      GuardReadback layout .boolean condition (.bool true) reference

theorem read_boolean {model : DomainModel} {scope : Scope} {layout : Layout scope}
    {binders : Binders model scope} {history : Domain.History model.toCarriers}
    {environment : Domain.Environment model.toCarriers} {term : Term [] scope .boolean} {reference : Nat}
    (checked : layout[reference]? = some (.data (.present term)))
    (related : Holds model binders history layout environment) :
    environment[reference]? = some (.data (.boolean (term.eval (LawResults.empty model) binders))) := by
  obtain ⟨actual, physical, present, encoded, read⟩ := related.data checked
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

inductive Derivation (routing : Original.Routing) (frames : Original.Frames)
    (context : ProtocolContext) (definitions : List CheckedDefinition) (callees : List CalleeKey) (out : List Ty)
    (outputs : List Original.Location) :
    {scope : Scope} → Layout scope → Form [] callees scope out → Block → Type 1 where
  | done {scope : Scope} {layout : Layout scope} {values : Values (Comp [] scope) out}
      (readback : Readback layout values outputs) :
      Derivation routing frames context definitions callees out outputs layout (.done values) (fun _ => Domain.View.empty)
  | halt {scope : Scope} {layout : Layout scope} (reason : PIR.Stop) :
      Derivation routing frames context definitions callees out outputs layout (.halt reason) (fun _ _ => .halt reason)
  | split {scope : Scope} {layout : Layout scope} {ty : Ty}
      (subject : Subject scope ty) {absent : Form [] callees scope out}
      {present : Form [] callees (.value ty :: scope) out} {target : Block}
      (absentBranch : Derivation routing frames context definitions callees out outputs
        (layout.map (Cell.absentAt subject)) absent target)
      (presentBranch : Derivation routing frames context definitions callees out outputs
        (layout.map (Cell.presentAt subject)) present target) :
      Derivation routing frames context definitions callees out outputs layout
        (.split subject.comp absent present) target
  | splitPresent {scope : Scope} {layout : Layout scope} {ty : Ty}
      (subject : Subject scope ty) {absent : Form [] callees scope out}
      {present : Form [] callees (.value ty :: scope) out} {target : Block}
      (reference : Nat) (checked : layout[reference]? = some (.data subject.comp))
      (absentMatch : absent.CallsMatch)
      (tail : Derivation routing frames context definitions callees out outputs
        (layout.map (Cell.presentAt subject)) present target) :
      Derivation routing frames context definitions callees out outputs layout
        (.split subject.comp absent present) target
  | compute {scope : Scope} {layout : Layout scope}
      (operation : Calculation) (terms : Terms [] scope operation.op.arguments)
      {next : Form [] callees (.results operation.op.results :: scope) out} {rest : Block}
      (references : List Nat)
      (inputsData : operation.op.arguments.all Domain.dataType = true)
      (outputsData : operation.op.results.all Domain.dataType = true)
      (readback : Readback layout (components terms) (references.map Original.Location.data))
      (tail : Derivation routing frames context definitions callees out outputs
        (resultsLayout layout operation.op.results) next rest) :
      Derivation routing frames context definitions callees out outputs layout
        (.compute operation.op (ConnectionCalculations.calculation_allowed operation) terms next)
        (fun model => Domain.View.sequence
          (Domain.View.calculation model operation references (operation.op.results.map ValueSort.data)) (rest model))
  | mathHelper {scope : Scope} {layout : Layout scope}
      (program : Program) (helper : Helper) (math : helper.kind = .math)
      (binding : ConnectionHelpers.Binding definitions helper program)
      (arguments : Values (Comp [] scope) helper.inputs)
      {next : Form [] callees (.tuple helper.outputs :: scope) out} {rest : Block}
      (references : List Nat)
      (inputsData : helper.inputs.all Domain.dataType = true)
      (outputsData : helper.outputs.all Domain.dataType = true)
      (readback : Readback layout arguments (references.map Original.Location.data))
      (tail : Derivation routing frames context definitions callees out outputs
        (tupleLayout layout helper.outputs) next rest) :
      Derivation routing frames context definitions callees out outputs layout (.math helper arguments next)
        (fun model => Domain.View.sequence
          (Domain.View.helper model program helper.name references (helper.outputs.map ValueSort.data)) (rest model))
  | calculation {scope : Scope} {layout : Layout scope} {form : Form [] callees scope out}
      (operation : Calculation) (total : operation.op.total = true)
      (terms : Terms [] scope operation.op.arguments) (references : List Nat)
      (inputsData : operation.op.arguments.all Domain.dataType = true)
      (outputsData : operation.op.results.all Domain.dataType = true)
      (readback : Readback layout (components terms) (references.map Original.Location.data))
      {rest : Block}
      (tail : Derivation routing frames context definitions callees out outputs
        (layout ++ cells (NormalForm.calculation operation.op total terms)) form rest) :
      Derivation routing frames context definitions callees out outputs layout form
        (fun model => Domain.View.sequence
          (Domain.View.calculation model operation references (operation.op.results.map ValueSort.data)) (rest model))
  | receive {scope : Scope} {layout : Layout scope} (ty : Ty) (site : String) (peer : Nat)
      {next : Form [] callees (.value ty :: scope) out} {rest : Block}
      (origin : Origin)
      (route : routing.message frames (qualifyProtocolSite context.applicationPrefix site)
        (context.roles peer) routing.self = some origin)
      (data : ty.isHandle = false)
      (tail : Derivation routing frames context definitions callees out outputs (receiveLayout layout ty) next rest) :
      Derivation routing frames context definitions callees out outputs layout (.receive ty site peer next)
        (fun model => Domain.View.sequence
          (Domain.View.receive (qualifyProtocolSite context.applicationPrefix site)
            (qualifyProtocolSite context.applicationPrefix site) (routing.context.role (context.roles peer))
            ty [.data ty]) (rest model))
  | send {scope : Scope} {layout : Layout scope} (ty : Ty) (site : String) (peer : Nat)
      (value : Term [] scope ty) {next : Form [] callees scope out} {rest : Block}
      (reference : Nat) (readback : layout[reference]? = some (.data (.present value)))
      (origin : Origin)
      (route : routing.message frames (qualifyProtocolSite context.applicationPrefix site)
        routing.self (context.roles peer) = some origin)
      (tail : Derivation routing frames context definitions callees out outputs layout next rest) :
      Derivation routing frames context definitions callees out outputs layout (.send ty site peer value next)
        (fun model => Domain.View.sequence
          (Domain.View.send (qualifyProtocolSite context.applicationPrefix site)
            (qualifyProtocolSite context.applicationPrefix site) (routing.context.role (context.roles peer))
            reference []) (rest model))
  | guard {scope : Scope} {layout : Layout scope} {ty : Ty}
      (equality : Equality ty) (left right : Term [] scope ty)
      {next : Form [] callees scope out} {rest : Block}
      (reference : Nat)
      (readback : GuardReadback layout equality left right reference)
      (tail : Derivation routing frames context definitions callees out outputs layout next rest) :
      Derivation routing frames context definitions callees out outputs layout (.guard equality left right next)
        (fun model => Domain.View.sequence (Domain.View.guard reference []) (rest model))
  | trueGuard {scope : Scope} {layout : Layout scope} {form : Form [] callees scope out}
      (reference : Nat) (readback : layout[reference]? = some (.data (.present (.bool true))))
      {rest : Block} (tail : Derivation routing frames context definitions callees out outputs layout form rest) :
      Derivation routing frames context definitions callees out outputs layout form
        (fun model => Domain.View.sequence (Domain.View.guard reference []) (rest model))
  | falseGuard {scope : Scope} {layout : Layout scope}
      (reference : Nat) (readback : layout[reference]? = some (.data (.present (.bool false))))
      (rest : Block) :
      Derivation routing frames context definitions callees out outputs layout (.halt .reject)
        (fun model => Domain.View.sequence (Domain.View.guard reference []) (rest model))

/-- Certificate size follows syntax, independently of values and replies. -/
def Derivation.size {routing : Original.Routing} {frames : Original.Frames} {context : ProtocolContext} {definitions : List CheckedDefinition}
    {callees : List CalleeKey} {out : List Ty} {outputs : List Original.Location}
    {scope : Scope} {layout : Layout scope} {form : Form [] callees scope out} {target : Block} :
    Derivation routing frames context definitions callees out outputs layout form target → Nat
  | .done _ | .halt _ | .falseGuard .. => 1
  | .split _ absent present => 1 + absent.size + present.size
  | .splitPresent _ _ _ _ tail => 1 + tail.size
  | .compute _ _ _ _ _ _ tail => 1 + tail.size
  | .mathHelper _ _ _ _ _ _ _ _ _ tail => 1 + tail.size
  | .calculation _ _ _ _ _ _ _ tail => 1 + tail.size
  | .receive _ _ _ _ _ _ tail => 1 + tail.size
  | .send _ _ _ _ _ _ _ _ tail => 1 + tail.size
  | .guard _ _ _ _ _ tail => 1 + tail.size
  | .trueGuard _ _ tail => 1 + tail.size

/-- Structural helper bindings introduce no normalizer laws or callee calls. -/
theorem Derivation.callsMatch {routing : Original.Routing} {frames : Original.Frames} {context : ProtocolContext} {definitions : List CheckedDefinition}
    {callees : List CalleeKey} {out : List Ty} {outputs : List Original.Location}
    {scope : Scope} {layout : Layout scope} {form : Form [] callees scope out} {target : Block}
    (derivation : Derivation routing frames context definitions callees out outputs layout form target) : form.CallsMatch := by
  induction derivation <;>
    simp_all only [Form.CallsMatch, Form.lawCalls, Form.calleeCalls, List.map_append, Prod.mk.injEq]
  all_goals exact ⟨rfl, rfl⟩

/-- Fixed full-tuple readback, unchanged source state, immutable physical input
prefix. CompleteReturns can strengthen this using the parent-owned schema. -/
def Returns {model : DomainModel} {out : List Ty} (outputs : List Original.Location)
    (state : Original.State model.toCarriers) (captured : Domain.Environment model.toCarriers)
    (source : Values (Component model.Value) out × Original.State model.toCarriers)
    (target : Domain.Environment model.toCarriers) : Prop :=
  Original.ValuesHolds target outputs source.1 ∧ source.2 = state ∧ ArtifactBinding.Captures captured target

/-- Internal structural induction for the public certificate boundary. All models, source binders and
physical environments satisfying the fixed frame relation are quantified.
The source is the actual occurrence-aware denotation folded by Original.fold;
the target is the actual indexed Domain.View block, including its checkpoints.
Input sorts, complete input readback and bounds are fixed ABI obligations.
RouteCoverage and CompleteReturns remain available as independent root gates. -/
private noncomputable def sound
    {routing : Original.Routing} {frames : Original.Frames} {context : ProtocolContext} {definitions : List CheckedDefinition}
    {callees : List CalleeKey} {out : List Ty} {outputs : List Original.Location}
    {scope : Scope} {layout : Layout scope} {form : Form [] callees scope out} {target : Block}
    (derivation : Derivation routing frames context definitions callees out outputs layout form target)
    (plain : routing.context.profile = .plain)
    (model : DomainModel) (tables : Tables model (Occurrence.signature model.toCarriers))
    (bindings : ConnectionHelpers.TablesMatch model definitions tables)
    (runs : Runs model (Occurrence.signature model.toCarriers))
    (processes : CalleeProcesses model callees (Occurrence.signature model.toCarriers))
    (state : Original.State model.toCarriers) (stack : state.frames = frames)
    {inputTypes : List Ty} (abi : Original.InputABI) (inputs : Values (Component model.Value) inputTypes)
    (captured : Domain.Environment model.toCarriers)
    (sorts : Domain.sortsMatch abi.sorts captured = true)
    (bound : Original.LocationsBound captured.length abi.locations)
    (inputRead : Original.ValuesHolds captured abi.locations inputs)
    (binders : Binders model scope) (environment : Domain.Environment model.toCarriers)
    (related : Holds model binders state.history layout environment)
    (retained : ArtifactBinding.Captures captured environment) :
    Original.Simulation (Returns outputs state captured) (Original.InputLive abi inputs captured)
      (Original.fold routing (form.denoteOn model Occurrence.actions tables (LawResults.empty model)
        context runs processes binders) state) (target model environment) := by
  have live (frame : Domain.Environment model.toCarriers)
      (kept : ArtifactBinding.Captures captured frame)
      (source : PIR.Process (Domain.effects model.toCarriers)
        (Values (Component model.Value) out × Original.State model.toCarriers)) :=
    Original.inputLive_of_captures abi inputs captured frame source sorts bound inputRead kept
  induction derivation generalizing environment with
  | done readback => exact .done ⟨readback.sound related, rfl, retained⟩
  | halt reason => exact .halt reason
  | split subject absentBranch presentBranch absentIH presentIH =>
    cases evaluated : subject.comp.eval (LawResults.empty model) binders with
    | none =>
      simpa only [Form.denoteOn, Form.denoteWithOn, evaluated] using
        absentIH binders environment (related.absentAt subject evaluated) retained
    | some value =>
      simpa only [Form.denoteOn, Form.denoteWithOn, evaluated] using
        presentIH (.cons value binders) environment (related.presentAt subject value evaluated) retained
  | splitPresent subject reference checked absentMatch tail ih =>
    cases evaluated : subject.comp.eval (LawResults.empty model) binders with
    | none => exact False.elim (related.not_absent checked evaluated)
    | some value =>
      simpa only [Form.denoteOn, Form.denoteWithOn, evaluated] using
        ih (.cons value binders) environment (related.presentAt subject value evaluated) retained
  | @compute scope layout operation terms next rest references inputsData outputsData readback tail ih =>
    rw [ConnectionCalculations.form_compute_closed model Occurrence.actions (LawResults.empty model)
      context runs processes tables operation terms next binders, Original.fold_bind]
    apply Original.Simulation.checkpoint environment (live _ retained _)
    apply (Original.Simulation.closedCalculationOn model routing operation
      (Terms.eval (LawResults.empty model) terms binders) inputsData outputsData state environment references
      (read_terms readback binders related)).bind
    · intro process frame same
      subst frame
      exact live _ retained _
    · intro source target returned
      apply Classical.choice
      obtain ⟨values, same, appended⟩ := returned
      rw [same, appended]
      have kept := ArtifactBinding.captures_trans retained (ArtifactBinding.captures_append
        environment (Original.encodeHelperResult values))
      exact ⟨.checkpoint _ (live _ kept _)
        (ih (.cons values binders) _ (results_frame model outputsData values binders related) kept)⟩
  | @mathHelper scope layout program helper math binding arguments next rest references inputsData outputsData
      readback tail ih =>
    apply Classical.choice
    obtain ⟨values, present, read⟩ := read_components readback binders related
    have sourceEq := ConnectionCalculations.form_math_present_closed model Occurrence.actions
      (LawResults.empty model) context runs processes program.payload.definitions helper arguments values
      next binders present
    rw [← binding.tables bindings] at sourceEq
    rw [sourceEq, Original.fold_bind]
    refine ⟨Original.Simulation.checkpoint environment (live _ retained _) ?_⟩
    apply (Original.Simulation.linkedDataHelperOn model program routing helper binding.present outputsData
      values environment references read state inputsData).bind
    · intro process frame same
      subst frame
      exact live _ retained _
    · intro source target returned
      apply Classical.choice
      obtain ⟨values, same, appended⟩ := returned
      rw [same, appended]
      have kept := ArtifactBinding.captures_trans retained (ArtifactBinding.captures_append
        environment (Original.encodeHelperResult values))
      exact ⟨.checkpoint _ (live _ kept _)
        (ih (.cons values.present binders) _ (tuple_frame model outputsData values binders related) kept)⟩
  | @calculation scope layout form operation total terms references inputsData outputsData readback rest tail ih =>
    have step := ConnectionCalculations.view_calculation_total model operation total
      (Terms.eval (LawResults.empty model) terms binders) inputsData outputsData environment references
      (read_terms readback binders related)
    have extended := calculation_frame model operation total terms outputsData binders related
    have kept := ArtifactBinding.captures_trans retained (ArtifactBinding.captures_append environment
      (Original.encodeHelperResult (operation.op.evalTotal model total
        (Terms.eval (LawResults.empty model) terms binders))))
    apply Original.Simulation.checkpoint environment (live _ retained _)
    rw [step]
    exact .checkpoint _ (live _ kept _) (ih binders _ extended kept)
  | @receive scope layout ty site peer next rest origin route data tail ih =>
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
    apply Original.Simulation.checkpoint environment (live _ retained _)
    apply (Original.Simulation.plainReceive routing state ty qualified (context.roles peer) origin
      (by simpa only [qualified, stack] using route) data environment).bind
    · intro process frame same
      subst frame
      exact live _ retained _
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
        exact ⟨.checkpoint target (live _ kept _) (ih (.cons value binders) target extended kept)⟩
  | @send scope layout ty site peer value next rest reference readback origin route tail ih =>
    apply Classical.choice
    obtain ⟨actual, physical, present, encoded, read⟩ := related.data readback
    have same : actual = value.eval (LawResults.empty model) binders := Option.some.inj present.symm
    subst actual
    obtain ⟨payload, payloadEq, physicalEq⟩ : ∃ payload,
        Domain.Payload.ofValue ty (value.eval (LawResults.empty model) binders) = some payload ∧
        physical = .data payload := by
      unfold Domain.Value.encode at encoded
      cases found : Domain.Payload.ofValue ty (value.eval (LawResults.empty model) binders) with
      | none => simp [found] at encoded
      | some payload => exact ⟨payload, rfl, (Option.some.inj (by simpa [found] using encoded)).symm⟩
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
    apply Original.Simulation.checkpoint environment (live _ retained _)
    apply (Original.Simulation.plainSend routing state ty qualified (context.roles peer)
      (value.eval (LawResults.empty model) binders) origin
      (by simpa only [qualified, stack] using route) environment reference payload payloadEq
      (by simpa only [physicalEq] using read)).bind
    · intro process frame same
      subst frame
      exact live _ retained _
    · intro source target returned
      rw [returned.1, returned.2]
      exact .checkpoint environment (live _ retained _) (ih binders environment related retained)
  | @guard scope layout ty equality left right next rest reference readback tail ih =>
    have readCondition := readback.read related
    apply Original.Simulation.checkpoint environment (live _ retained _)
    rw [Domain.View.guard_eq reference environment _ readCondition]
    let condition := left.eval (LawResults.empty model) binders = right.eval (LawResults.empty model) binders
    letI : Decidable condition := equality.decide model _ _
    by_cases holds : condition
    · change left.eval (LawResults.empty model) binders = right.eval (LawResults.empty model) binders at holds
      simpa only [Form.denoteOn, Form.denoteWithOn, holds, ↓reduceIte, decide_true,
        PIR.Process.bind] using
        (Original.Simulation.checkpoint environment (live _ retained _)
          (ih binders environment related retained))
    · change ¬ (left.eval (LawResults.empty model) binders = right.eval (LawResults.empty model) binders) at holds
      simp only [Form.denoteOn, Form.denoteWithOn, holds, ↓reduceIte, decide_false,
        Original.fold_halt]
      exact .halt .reject
  | trueGuard reference readback tail ih =>
    apply Original.Simulation.checkpoint environment (live _ retained _)
    rw [Domain.View.guard_eq reference environment true (read_boolean readback related)]
    exact .checkpoint environment (live _ retained _) (ih binders environment related retained)
  | falseGuard reference readback rest =>
    apply Original.Simulation.checkpoint environment (live _ retained _)
    rw [Domain.View.guard_eq reference environment false (read_boolean readback related)]
    exact .halt .reject

/-- Proof-relevant accepted data for an actual checked source body. The source,
pattern, output row, initial frame and target block are fixed before proposal.
Normalization is a finite kernel-checked equality, not an authored replacement
body. The core accepts exact source declarations, with no normalizer law or
callee environment in this fragment. -/
structure Certificate (routing : Original.Routing) (frames : Original.Frames) (context : ProtocolContext)
    (definitions : List CheckedDefinition) (role roster : Nat) (source : CheckedProtocol) (pattern : InputPattern source.inputs)
    (outputs : List Original.Location) (layout : Layout pattern.scope) (target : Block) where
  form : Form [] [] pattern.scope source.outputs
  normalized : normalize {} source.body role roster pattern = .ok form
  alignment : Derivation routing frames context definitions [] source.outputs outputs layout form target

/-- The single public accepted-certificate-to-Simulation interface. It connects
the actual typed source body, interpreted with real occurrence actions and
iterations, to the indexed Domain.View block. No root equation or Simulation is
supplied by an instance. Root masking, source admission ownership, final ABI
assembly and independent reached-source routing coverage stay with the caller.
-/
@[no_expose] noncomputable def Certificate.simulation
    {routing : Original.Routing} {frames : Original.Frames} {context : ProtocolContext} {definitions : List CheckedDefinition}
    {role roster : Nat} {source : CheckedProtocol} {pattern : InputPattern source.inputs}
    {outputs : List Original.Location} {layout : Layout pattern.scope} {target : Block}
    (certificate : Certificate routing frames context definitions role roster source pattern outputs layout target)
    (plain : routing.context.profile = .plain) (distinct : RosterDistinct context role roster)
    (model : DomainModel) (tables : Tables model (Occurrence.signature model.toCarriers))
    (bindings : ConnectionHelpers.TablesMatch model definitions tables)
    (protocols : ProtocolTable model.Value (Occurrence.signature model.toCarriers))
    (state : Original.State model.toCarriers) (stack : state.frames = frames)
    (binders : Binders model pattern.scope) (abi : Original.InputABI)
    (captured : Domain.Environment model.toCarriers)
    (sorts : Domain.sortsMatch abi.sorts captured = true)
    (bound : Original.LocationsBound captured.length abi.locations)
    (inputRead : Original.ValuesHolds captured abi.locations (pattern.environment model binders))
    (environment : Domain.Environment model.toCarriers)
    (related : Holds model binders state.history layout environment)
    (retained : ArtifactBinding.Captures captured environment) :
    Original.Simulation (Returns outputs state captured) (Original.InputLive abi (pattern.environment model binders) captured)
      (Original.fold routing (source.body.denote
        (participantMeaningWithOn model (.silent _) Occurrence.actions tables (context.roles role)
          protocols context Occurrence.iterations) (pattern.environment model binders).get) state)
      (target model environment) := by
  rw [normalize_occurrence_sound {} source.body role roster pattern certificate.form
    certificate.normalized certificate.alignment.callsMatch distinct (LawResults.empty model)
    (fun (entry : Fin 0) => entry.elim0) binders (LawsHold.empty _ _) (fun (entry : Fin 0) => entry.elim0)]
  exact sound certificate.alignment plain model tables bindings
    (runsAtOn model Occurrence.actions Occurrence.iterations tables protocols context role)
    (fun (entry : Fin 0) => entry.elim0) state stack abi (pattern.environment model binders) captured sorts bound inputRead
    binders environment related retained

end Zkc.Construction.ConnectionCertificate
