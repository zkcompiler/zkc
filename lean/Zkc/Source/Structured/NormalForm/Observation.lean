module

public import Zkc.Source.Structured.NormalForm.Soundness
public import Zkc.Source.Structured.Occurrence

/-! Normalization into the existing source occurrence meaning.

Helper sites stay silent, as in `Occurrence.table`. Protocol actions and reached
repeat boundaries retain their interpretation, including stops and all outputs.
Callbacks remain shared typed regions; their dynamic coordinates are supplied by
`denoteRepeatOn`, never reconstructed from an erased process. -/

public section
set_option autoImplicit false
namespace Zkc.Source.Structured.NormalForm

@[expose] def LawResults.empty (model : DomainModel) : LawResults model [] where
  result entry := entry.elim0

theorem LawsHold.empty {model : DomainModel} {I : PIR.Signature} {Γ : List Ty}
    (tables : Tables model I) (inputs : Values (Component model.Value) Γ) :
    LawsHold tables (LawResults.empty model) inputs := fun entry => entry.elim0

/-- The complete occurrence process of the same typed body, for arbitrary
provider replies. `CallsMatch` fixes exact helper/callee identities; `LawsHold`
and `CalleesHold` supply their semantic equations at the pattern's input pins.
A structural signature can keep helper invocations and use no helper laws. -/
theorem normalize_occurrence_sound {model : DomainModel}
    {tables : Tables model (Occurrence.signature model.toCarriers)}
    {protocols : ProtocolTable model.Value (Occurrence.signature model.toCarriers)}
    {context : ProtocolContext}
    (sig : Signature) {Γ out : List Ty} (body : Region protocolDialect Γ out)
    (role roster : Nat) (pattern : InputPattern Γ) (form : Form sig.laws sig.callees pattern.scope out)
    (normalized : normalize sig body role roster pattern = .ok form) (matched : form.CallsMatch)
    (distinct : RosterDistinct context role roster) (results : LawResults model sig.laws)
    (processes : CalleeProcesses model sig.callees (Occurrence.signature model.toCarriers))
    (binders : Binders model pattern.scope)
    (lawsHold : LawsHold tables results (pattern.environment model binders))
    (calleesHold : CalleesHold protocols processes (pattern.environment model binders)) :
    body.denote (participantMeaningWithOn model (.silent _) Occurrence.actions tables
        (context.roles role) protocols context Occurrence.iterations) (pattern.environment model binders).get =
      form.denoteOn model Occurrence.actions tables results context
        (runsAtOn model Occurrence.actions Occurrence.iterations tables protocols context role) processes binders :=
  normalize_soundOn (actions := Occurrence.actions) (iterations := Occurrence.iterations)
    sig body role roster pattern form normalized matched distinct results processes binders lawsHold calleesHold

/-- Apply normalization to a checked protocol's actual body with its existing
input and output masks. The only input equation fixes the ABI tuple represented
by the pattern; there is no assumed equation between root processes. -/
theorem normalize_checkedProtocol_soundOn {model : DomainModel} {I : PIR.Signature}
    (actions : PIR.OperationInterpretation (Interface model) I) (iterations : IterationObservations I)
    (tables : Tables model I) (protocols : ProtocolTable model.Value I) (context : ProtocolContext)
    (definition : CheckedProtocol) (sig : Signature) (role : Nat)
    (pattern : InputPattern definition.inputs)
    (form : Form sig.laws sig.callees pattern.scope definition.outputs)
    (normalized : normalize sig definition.body role definition.roles.length pattern = .ok form)
    (matched : form.CallsMatch) (distinct : RosterDistinct context role definition.roles.length)
    (results : LawResults model sig.laws) (processes : CalleeProcesses model sig.callees I)
    (inputs : Values (Component model.Value) definition.inputs) (binders : Binders model pattern.scope)
    (environment : maskValues (context.roles role) (context.mapScopes definition.inputScopes) inputs =
      pattern.environment model binders)
    (lawsHold : LawsHold tables results (pattern.environment model binders))
    (calleesHold : CalleesHold protocols processes (pattern.environment model binders)) :
    definition.denoteWithOn model (.silent _) actions tables protocols iterations context (context.roles role) inputs =
      (form.denoteOn model actions tables results context
        (runsAtOn model actions iterations tables protocols context role) processes binders).bind fun values =>
          .done (maskValues (context.roles role) (context.mapScopes definition.outputScopes) values) := by
  unfold CheckedProtocol.denoteWithOn
  erw [environment]
  exact bind_congr_left (normalize_soundOn (actions := actions) (iterations := iterations)
    sig definition.body role definition.roles.length pattern form normalized matched distinct results processes
      binders lawsHold calleesHold) _

/-- Normalized meanings commute with an effect interpretation whenever the
source helper/protocol tables and observations do. This reuses the existing
source naturality theorem, rather than another evaluator or erasure argument. -/
theorem normalize_interpret {model : DomainModel} {I J : PIR.Signature}
    (operations : PIR.OperationInterpretation I J)
    {leftActions : PIR.OperationInterpretation (Interface model) I}
    {rightActions : PIR.OperationInterpretation (Interface model) J}
    (actions : ∀ action, (leftActions action).interpret operations = rightActions action)
    {leftTables : Tables model I} {rightTables : Tables model J}
    (tables : Evaluation.ComponentTablesOn.Interprets operations leftTables rightTables)
    {leftProtocols : ProtocolTable model.Value I} {rightProtocols : ProtocolTable model.Value J}
    (protocols : ProtocolTable.Interprets operations leftProtocols rightProtocols)
    {leftIterations : IterationObservations I} {rightIterations : IterationObservations J}
    (iterations : IterationObservations.Interprets operations leftIterations rightIterations)
    (sig : Signature) {Γ out : List Ty} (body : Region protocolDialect Γ out)
    (role roster : Nat) (pattern : InputPattern Γ) (form : Form sig.laws sig.callees pattern.scope out)
    (normalized : normalize sig body role roster pattern = .ok form) (matched : form.CallsMatch)
    (context : ProtocolContext) (distinct : RosterDistinct context role roster)
    (results : LawResults model sig.laws)
    (leftProcesses : CalleeProcesses model sig.callees I) (rightProcesses : CalleeProcesses model sig.callees J)
    (binders : Binders model pattern.scope)
    (leftLaws : LawsHold leftTables results (pattern.environment model binders))
    (rightLaws : LawsHold rightTables results (pattern.environment model binders))
    (leftCallees : CalleesHold leftProtocols leftProcesses (pattern.environment model binders))
    (rightCallees : CalleesHold rightProtocols rightProcesses (pattern.environment model binders)) :
    (form.denoteOn model leftActions leftTables results context
        (runsAtOn model leftActions leftIterations leftTables leftProtocols context role) leftProcesses binders).interpret
          operations =
      form.denoteOn model rightActions rightTables results context
        (runsAtOn model rightActions rightIterations rightTables rightProtocols context role) rightProcesses binders := by
  rw [← normalize_soundOn (actions := leftActions) (iterations := leftIterations)
    sig body role roster pattern form normalized matched distinct results leftProcesses binders leftLaws leftCallees,
    ← normalize_soundOn (actions := rightActions) (iterations := rightIterations)
    sig body role roster pattern form normalized matched distinct results rightProcesses binders rightLaws rightCallees]
  exact participant_denoteOn_interpret operations (SiteObservations.silent_interpret operations)
    actions tables (context.roles role) body (pattern.environment model binders).get protocols context iterations

end Zkc.Source.Structured.NormalForm
