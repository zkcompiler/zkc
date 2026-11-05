module

public import Zkc.Semantics.MonadicPostcondition
public import Zkc.Source.Structured.OracleProcessTotal

@[expose] public section

/-! Provider invariants for the existing source presentation. The proof-carrying
restriction erases to the original computation in any lawful monad. It makes no
losslessness assumption and includes stopped executions with their actual state and log.
The presentation below is inspected only as a proof object; `Process.runM` remains executor.
-/

set_option autoImplicit false
namespace Zkc.Source.Structured.OracleProviderFrame

open Std.Do.Internal

variable {m : Type → Type} [Monad m] [LawfulMonad m] {A B S T E F : Type}
  {I J : PIR.Signature}

/-- A local proof rule on the existing free presentation. External replies may stop,
change auxiliary state, and emit any events. Only the provider invariant is constrained. -/
def Safe (invariant : S → Prop) : PIR.Process (OracleProcess.Effect I S E) A →
    (A → Prop) → Prop
  | .done value, post => post value
  | .halt _, _ => True
  | .call request next, post => invariant request.2 ∧
      ∀ result, invariant result.state → Safe invariant (next result) post

theorem Safe.bind {invariant : S → Prop} (process : PIR.Process (OracleProcess.Effect I S E) A)
    (next : A → PIR.Process (OracleProcess.Effect I S E) B) (pre : A → Prop) (post : B → Prop)
    (head : Safe invariant process pre)
    (tail : ∀ value, pre value → Safe invariant (next value) post) :
    Safe invariant (process.bind next) post := by
  induction process with
  | done value => exact tail value head
  | halt reason => trivial
  | call request continuation ih =>
    exact ⟨head.1, fun result valid ↦ ih result (head.2 result valid)⟩

theorem Safe.map {invariant : S → Prop} (process : PIR.Process (OracleProcess.Effect I S E) A)
    (change : A → B) (pre : A → Prop) (post : B → Prop)
    (head : Safe invariant process pre) (law : ∀ value, pre value → post (change value)) :
    Safe invariant (OracleProcess.mapResult change process) post :=
  head.bind _ _ pre post fun value valid ↦ law value valid

theorem Safe.sequence {invariant : S → Prop} (stateInvariant : T → Prop)
    (first : PIR.Execution T F A)
    (next : A → T → PIR.Process (OracleProcess.Effect I S E) (PIR.Execution T F B))
    (head : stateInvariant first.state)
    (tail : ∀ value state, stateInvariant state →
      Safe invariant (next value state) (fun result ↦ stateInvariant result.state)) :
    Safe invariant (OracleProcess.sequence first next) (fun result ↦ stateInvariant result.state) := by
  cases first with
  | mk outcome state events =>
    cases outcome with
    | stopped reason => exact head
    | returned value =>
      exact (tail value state head).map _ _ _ _ (fun _ valid ↦ valid)

theorem Safe.present {invariant : S → Prop} (stateInvariant : T → Prop)
    (operations : (operation : J.Op) → T →
      PIR.Process (OracleProcess.Effect I S E) (PIR.Execution T F (J.Reply operation)))
    (localLaw : ∀ operation state, stateInvariant state →
      Safe invariant (operations operation state) (fun result ↦ stateInvariant result.state))
    (process : PIR.Process J A) (state : T) (valid : stateInvariant state) :
    Safe invariant (OracleProcess.present operations process state)
      (fun result ↦ stateInvariant result.state) := by
  induction process generalizing state with
  | done value => exact valid
  | halt reason => exact valid
  | call operation next ih =>
    exact (localLaw operation state valid).bind _ _ _ _ fun result kept ↦
      Safe.sequence stateInvariant result _ kept (fun value current live ↦ ih value current live)

/-- The proof restriction erases to the existing monadic interpreter, including outer
failure. An outer halt uses the interpreter's own fallback, whose invariant is explicit. -/
theorem Safe.executeM (invariant : S → Prop)
    (external : PIR.MonadHandler m I S E)
    (localLaw : ∀ operation state, invariant state →
      Ensures (fun result ↦ invariant result.state) (external operation state))
    (process : PIR.Process (OracleProcess.Effect I S E) (PIR.Execution T F A))
    (post : PIR.Execution T F A → Prop) (initial : T)
    (fallback : ∀ reason, post ⟨.stopped reason, initial, []⟩)
    (safe : Safe invariant process post) :
    Ensures post (OracleProcess.executeM external process initial) := by
  induction process with
  | done value =>
    rw [OracleProcess.executeM_done]
    exact MonadicPostcondition.pure post value safe
  | halt reason =>
    simp only [OracleProcess.executeM, PIR.Process.runM, pure_bind]
    exact MonadicPostcondition.pure post _ (fallback reason)
  | call request next ih =>
    have equation : OracleProcess.executeM external (.call request next) initial =
        (external request.1 request.2 >>= fun result ↦
          OracleProcess.executeM external (next result) initial) := by
      simp only [OracleProcess.executeM, OracleProcess.runM_effect_call, bind_assoc]
    rw [equation]
    exact (localLaw _ _ safe.1).bind fun result valid ↦ ih result (safe.2 result valid)

/-- Local complete-record preservation composes along the original Process, for every
return and every stop, with no premise about a whole run. -/
theorem runM_invariant (invariant : S → Prop) (handler : PIR.MonadHandler m I S E)
    (localLaw : ∀ operation state, invariant state →
      Ensures (fun result ↦ invariant result.state) (handler operation state))
    (process : PIR.Process I A) (state : S) (valid : invariant state) :
    Ensures (fun result ↦ invariant result.state) (process.runM handler state) := by
  induction process generalizing state with
  | done value => exact MonadicPostcondition.pure _ _ valid
  | halt reason => exact MonadicPostcondition.pure _ _ valid
  | call operation next ih =>
    apply (localLaw operation state valid).bind
    intro result kept
    cases result with
    | mk outcome current events =>
      cases outcome with
      | stopped reason => exact MonadicPostcondition.pure _ _ kept
      | returned value => exact MonadicPostcondition.map (ih value current kept) _ (fun _ live ↦ live)

end Zkc.Source.Structured.OracleProviderFrame

namespace Zkc.Source.Structured.OracleProviderFrame

open Std.Do.Internal

variable {model : DomainModel} {snapshot : Snapshot} {domains : List DomainSpec}
  {math : OracleMathEnvironment} {S E : Type}

set_option smartUnfolding false in
/-- Every local descriptor keeps the provider; only the query arm can call it. This
covers all descriptors, nominal sorts, validation failures, and absent arguments. -/
theorem operation_provider (oracles : List (CheckedOracle snapshot domains math))
    (location : OracleLocation) (self : Nat) (roles : Nat → Nat) (op : OracleOp)
    (arguments : Values (Component (ProtocolValue model.toCarriers)) op.arguments)
    (state : OracleRuntimeState model snapshot domains math S)
    (localOnly : OracleProcess.externalQuery op = false) :
    (OracleExecution.operation model oracles (OracleProcess.refusingBase (E := E))
      location self roles op arguments state).state.provider = state.provider := by
  cases op
  case query kind owner =>
    cases owner with
    | some owner => cases localOnly
    | none =>
      dsimp only [OracleExecution.operation, OracleOp.results]
      split <;> rfl
  case send kind holder receivers bounds =>
    cases kind
    dsimp only [OracleExecution.operation, OracleOp.results]
    repeat' (split <;> try dsimp only [OracleExecution.returned,
      OracleExecution.refusal, OracleOp.results])
  case forgetShape source target =>
    cases source
    cases target
    dsimp only [OracleExecution.operation, OracleOp.results]
    repeat' (split <;> try dsimp only [OracleExecution.returned,
      OracleExecution.refusal, OracleOp.results])
  all_goals
    dsimp only [OracleExecution.operation, OracleOp.results]
    repeat' (split <;> try dsimp only [OracleExecution.returned,
      OracleExecution.refusal, OracleOp.results])

/-- Data demand observes logical holder payloads without touching the provider. -/
theorem demand_provider (request : OracleDataDemand) (location : OracleLocation)
    (state : OracleRuntimeState model snapshot domains math S) :
    (OracleStore.demandBase (E := E) request location state).state.provider = state.provider := by
  rcases request with ⟨sort, requester, view⟩
  cases sort <;> dsimp only [OracleStore.demandBase]
  all_goals repeat' (first | rfl | split)

/-- Control frames, source cursors, application stacks, and holder data demand cannot
modify the external provider state. -/
theorem control_provider (oracles : List (CheckedOracle snapshot domains math))
    (action : OracleProtocolAction model.toCarriers)
    (state : OracleProtocol.State model snapshot domains math S)
    (localOnly : OracleProcess.externalAction action = false) :
    (OracleProtocol.handler model oracles (OracleProcess.refusingOrdinary (E := E))
      OracleProcess.refusingBase action state).state.oracle.provider = state.oracle.provider := by
  cases action <;> try cases localOnly
  case demand request => exact demand_provider request _ state.oracle
  all_goals
    dsimp only [OracleProtocol.handler]
    repeat' (first | rfl | split)

/-- Virtual recursion runs on the immutable older logical table. Its counter changes and
every inner stopped record are included in the same provider invariant. -/
theorem answer_safe (invariant : S → Prop) (self : Nat)
    (entries : OracleEntries model snapshot domains math) (request : OracleRead) (state : S × Nat)
    (valid : invariant state.1) :
    Safe invariant (OracleProcess.answer (E := E) model self entries request state)
      (fun result ↦ invariant result.state.1) := by
  induction entries generalizing request state with
  | nil => exact valid
  | cons entry older ih =>
    rcases entry with ⟨row, table⟩
    simp only [OracleProcess.answer]
    split
    · split
      · split
        · exact valid
        · cases table.payload with
          | base data =>
            apply Safe.map _ _ (fun result ↦ invariant result.state)
            · exact ⟨valid, fun result live ↦ live⟩
            · exact fun _ live ↦ live
          | virtual checked answerType captures =>
            dsimp only
            split
            · apply Safe.map _ _ (fun result ↦ invariant result.state.1)
              · apply Safe.present (fun current : S × Nat ↦ invariant current.1)
                  _ _ _ (state.1, state.2 + 1) valid
                · intro child current live
                  exact ih _ current live
              · exact fun _ live ↦ live
            · exact valid
      · exact ih request state valid
    · exact ih request state valid

theorem read_safe (invariant : S → Prop) (request : OracleRead)
    (state : OracleRuntimeState model snapshot domains math S) (valid : invariant state.provider) :
    Safe invariant (OracleProcess.read (E := E) model request state)
      (fun result ↦ invariant result.state.provider) :=
  (answer_safe invariant state.self state.entries request _ valid).map _ _ _ _
    (fun _ live ↦ live)

theorem query_safe (invariant : S → Prop) (location : OracleLocation)
    (self : Nat) (roles : Nat → Nat) (kind : OracleKind) (owner : Nat)
    (handle : Component (ProtocolValue model.toCarriers) (.oracle kind))
    (position : Component (ProtocolValue model.toCarriers) kind.query)
    (state : OracleRuntimeState model snapshot domains math S) (valid : invariant state.provider) :
    Safe invariant (OracleProcess.query (E := E) model location self roles kind owner
      handle position state) (fun result ↦ invariant result.state.provider) := by
  unfold OracleProcess.query
  split
  · exact valid
  · split
    · exact valid
    · split
      · exact (read_safe invariant _ state valid).map _ _ _ _ (fun _ live ↦ live)
      · exact valid

set_option smartUnfolding false in
theorem operation_safe (invariant : S → Prop)
    (oracles : List (CheckedOracle snapshot domains math))
    (location : OracleLocation) (self : Nat) (roles : Nat → Nat) (op : OracleOp)
    (arguments : Values (Component (ProtocolValue model.toCarriers)) op.arguments)
    (state : OracleRuntimeState model snapshot domains math S) (valid : invariant state.provider) :
    Safe invariant (OracleProcess.operation (E := E) model oracles location self roles op
      arguments state) (fun result ↦ invariant result.state.provider) := by
  cases op <;> try
    (change invariant _
     rw [operation_provider oracles location self roles _ arguments state rfl]
     exact valid)
  case query kind owner =>
    cases owner with
    | none =>
      change invariant _
      rw [operation_provider oracles location self roles _ arguments state rfl]
      exact valid
    | some owner => exact query_safe invariant location self roles kind owner _ _ state valid

theorem action_safe (invariant : S → Prop)
    (oracles : List (CheckedOracle snapshot domains math))
    (action : OracleProtocolAction model.toCarriers)
    (state : OracleProtocol.State model snapshot domains math S)
    (valid : invariant state.oracle.provider) :
    Safe invariant (OracleProcess.action (E := E) model oracles action state)
      (fun result ↦ invariant result.state.oracle.provider) := by
  cases action <;> try
    (change invariant _
     rw [control_provider oracles _ state rfl]
     exact valid)
  case ordinary operation =>
    apply Safe.map _ _ (fun result ↦ invariant result.state)
    · exact ⟨valid, fun result live ↦ live⟩
    · exact fun _ live ↦ live
  case oracle request =>
    simp only [OracleProcess.action]
    split
    · exact valid
    · exact (operation_safe invariant oracles _ _ _ _ _ state.oracle valid).map _ _ _ _
        (fun _ live ↦ live)

variable {m : Type → Type} [Monad m] [LawfulMonad m]

/-- The actual original source handler preserves any provider invariant preserved by its
two external handlers. No replacement source evaluator or whole-run premise is supplied. -/
theorem actionM_invariant (invariant : S → Prop)
    (oracles : List (CheckedOracle snapshot domains math))
    (ordinary : PIR.MonadHandler m (participantInterfaceOn model.toCarriers) S E)
    (base : PIR.MonadHandler m (oracleReadInterface model.toCarriers) S E)
    (ordinaryLaw : ∀ operation state, invariant state →
      Ensures (fun result ↦ invariant result.state) (ordinary operation state))
    (baseLaw : ∀ request state, invariant state →
      Ensures (fun result ↦ invariant result.state) (base request state))
    (action : OracleProtocolAction model.toCarriers)
    (state : OracleProtocol.State model snapshot domains math S)
    (valid : invariant state.oracle.provider) :
    Ensures (fun result ↦ invariant result.state.oracle.provider)
      (OracleProcess.actionM model oracles ordinary base action state) := by
  apply Safe.executeM invariant _ _ _ _ state (fun _ ↦ valid)
    (action_safe invariant oracles action state valid)
  intro operation current live
  cases operation with
  | inl operation => exact ordinaryLaw operation current live
  | inr request => exact baseLaw request current live

end Zkc.Source.Structured.OracleProviderFrame
