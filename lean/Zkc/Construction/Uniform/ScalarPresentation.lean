module

public import Zkc.Construction.ScalarConnection

@[expose] public section

/-! Complete finite scalar presentations for consumers that retain all returned
values, including interpreted-byte transport. The encoder is source-owned and
fixed before evidence; no protocol supplies an artifact/output matching proof. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Zkc.Construction.Uniform.ScalarPresentation
open Zkc.Source Zkc.Source.Structured
open ScalarProjection
attribute [local implicit_reducible] CheckedProtocol.signature
variable {F G A B C : Type}

/-- Any observation respecting the complete return relation follows from the
simulation. Erasure applies only to administrative checkpoints. -/
theorem observe {carriers : Carriers} {returns : A → B → Prop}
    {live : PIR.Process (Domain.effects carriers) A → Domain.Environment carriers → Prop}
    {source : PIR.Process (Domain.effects carriers) A} {target : PIR.Process (Domain.effects carriers) B}
    (law : Original.Simulation returns live source target)
    (left : A → C) (right : B → C)
    (agree : ∀ a b, returns a b → left a = right b) :
    ((target.bind fun value => .done (right value)).interpret Original.forgetCheckpoints) =
      ((source.bind fun value => .done (left value)).interpret Original.forgetCheckpoints) := by
  induction law with
  | done related => exact congrArg (fun value => PIR.Process.done (I := Domain.effects carriers) value) (agree _ _ related).symm
  | halt => rfl
  | call operation next ih =>
      simp only [PIR.Process.bind, PIR.Process.interpret]
      congr 1
      funext reply
      exact ih reply
  | checkpoint frame related next ih =>
      simpa only [PIR.Process.bind, PIR.Process.interpret, Original.forgetCheckpoints] using ih

theorem forget_twice {carriers : Carriers} (source : PIR.Process (Domain.effects carriers) A) :
    (source.interpret Original.forgetCheckpoints).interpret Original.forgetCheckpoints =
      source.interpret Original.forgetCheckpoints := by
  rw [PIR.Process.interpret_comp]
  congr 1
  funext operation
  cases operation <;> rfl

theorem history_false {carriers : Carriers} (events : Domain.History carriers) :
    history false events = events := by
  induction events with
  | nil => rfl
  | cons head tail ih => cases head <;> simp_all [history, event, key]

theorem operations_false {carriers : Carriers} :
    operations (carriers := carriers) false = Original.forgetCheckpoints := by
  funext operation
  cases operation <;> try rfl
  case observe observed => cases observed <;> rfl
  case query events origin =>
    change PIR.Process.call (I := Domain.effects carriers)
        (.query (history false events) origin) PIR.Process.done =
      PIR.Process.call (I := Domain.effects carriers) (.query events origin) PIR.Process.done
    rw [history_false]

theorem sourceView_forget (context : Context) (source : PIR.Process (Actions F G) A)
    (events : Domain.History (uniformCarriers F G)) :
    (SourceProcess.sourceView context source events).interpret Original.forgetCheckpoints =
      SourceProcess.sourceView context source events := by
  induction source generalizing events with
  | done => rfl
  | halt => rfl
  | call operation next ih =>
      cases operation with
      | receive ty site sender =>
        cases ty <;>
          simp only [SourceProcess.sourceView, SourceProcess.receive, PIR.Process.bind,
            PIR.Process.interpret, Original.forgetCheckpoints]
        all_goals congr 1; funext reply; congr 1; funext ignored; exact ih reply _
      | send site receiver value =>
        rename_i ty
        cases ty <;>
          simp only [SourceProcess.sourceView, SourceProcess.send, Payload.ofValue,
            DomainAdapter.embedPayload, PIR.Process.bind, PIR.Process.interpret, Original.forgetCheckpoints]
        all_goals congr 1; funext ignored; exact ih () _
      | query site field arguments =>
        simp only [SourceProcess.sourceView, SourceProcess.query, PIR.Process.bind,
          PIR.Process.interpret, Original.forgetCheckpoints]
        congr 1; funext reply; exact ih reply _

/-- Total presentation encoder. On every reached return of a checked connection
its option is proved present by CompleteReturns, including every residual. -/
def values (signature : ProtocolSignature) (context : Context) (role : Nat)
    (source : Values (Component (uniformCarriers F G).Value) signature.outputs ×
      Domain.History (uniformCarriers F G)) : Domain.Environment (uniformCarriers F G) :=
  ((Original.roleOutputValues role signature.outputScopes source.1).map
    fun data => Domain.inputFrame context data source.2).getD []

section Connected
variable [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- Exact finite full-value presentation, derived from Connected and coverage.
It includes the returned transcript and arbitrary residual data, rather than
only the acceptance bit. Initial scalar histories remain handler-owned. -/
theorem connected {program : Program} {routing : Original.Routing} {role : Nat}
    {abi : Original.InputABI} {artifact : Participant}
    (connection : SourceConnection.Connected program routing role abi artifact)
    (mode : routing.mode = .validator) (replacement : Replacement)
    (profile : routing.context.profile = .fiatShamir replacement) (noLocal : routing.locals = [])
    (physical : Domain.Environment (uniformCarriers F G))
    (inputs : Values (Component (assignment F G)) program.payload.entry.inputs)
    (decoded : abi.read physical program.payload.entry.inputs = some inputs)
    (emptyHistory : ConnectionInputs.inputHistory routing.context artifact.inputs physical = [])
    (supported : ScalarSupport.Supported false
      (Occurrence.participant (ringModel F G) program role inputs)) :
    ((Domain.participant (ringModel F G) program routing.context artifact physical).bind
      fun result => .done result.values).interpret Original.forgetCheckpoints =
    (SourceProcess.sourceView routing.context
      ((program.participant F G role inputs).interpret CommonAdapter.project) []).bind
      fun result => .done (values program.payload.entry.signature routing.context role result) := by
  have transport := observe (Classical.choice (connection.simulation (ringModel F G) physical))
    (fun result => values program.payload.entry.signature routing.context role (result.1, result.2.history))
    (fun result => result.values) (by
      intro source target related
      obtain ⟨data, encoded, returned⟩ := related.values
      simp only [values, encoded, Option.map_some, Option.getD_some, returned])
  rw [transport, connection.source_eq_fold]
  have occurrence : SourceConnection.occurrence program role abi (ringModel F G) physical =
      Occurrence.participant (ringModel F G) program role inputs := by
    simp only [SourceConnection.occurrence, decoded]
  rw [occurrence]
  have covered := Classical.choice (connection.coverage (ringModel F G) physical)
  rw [occurrence] at covered
  have initialState : SourceConnection.initial routing artifact physical = ⟨[], []⟩ := by
    simp only [SourceConnection.initial, emptyHistory]
  rw [initialState]
  have observed := Classical.choice (ScalarObservation.simulation mode replacement profile noLocal
    covered supported (by intro _; rfl) [])
  have presented := observe observed
    (values program.payload.entry.signature routing.context role)
    (fun result => values program.payload.entry.signature routing.context role (result.1, result.2.history))
    (by
      intro scalar nominal related
      congr 1
      exact Prod.ext related.1 (related.2.2.trans (history_false _)))
  rw [operations_false, PIR.Process.interpret_bind] at presented
  simp only [PIR.Process.interpret, forget_twice, history_false] at presented
  rw [PIR.Process.interpret_bind]
  simp only [PIR.Process.interpret]
  rw [PIR.Process.interpret_bind, sourceView_forget] at presented
  simp only [PIR.Process.interpret] at presented
  rw [ScalarConnection.scalar_participant] at presented
  exact presented

end Connected
end Zkc.Construction.Uniform.ScalarPresentation
