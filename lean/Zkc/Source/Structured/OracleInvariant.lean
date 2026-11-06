module

public import Zkc.Source.Structured.OracleProtocol

@[expose] public section

/-! Reachable immutable stores. Virtual captures are validated against the strict older
prefix at insertion; the prefix is then immutable. No arbitrary wellformed-store premise
is substituted for source construction. Root/environment data is a separate ingress input. -/

set_option autoImplicit false
namespace Zkc.Source.Structured
namespace OracleStore
variable {model : DomainModel} {snapshot : Snapshot} {domains : List DomainSpec}
  {math : OracleMathEnvironment}

def PayloadBefore (self : Nat) (older : OracleEntries model snapshot domains math)
    {row : Ty} (table : OracleStoredTable model snapshot domains math row) : Prop :=
  match table.payload with
  | .base _ => True
  | .virtual _ _ captures =>
    OracleExecution.capturedSourcesValid (⟨self, older, (), 0⟩ :
      OracleRuntimeState model snapshot domains math Unit) table.holder table.receivers captures = true

inductive Reachable (self : Nat) : OracleEntries model snapshot domains math → Prop where
  | empty : Reachable self []
  | inserted {older : OracleEntries model snapshot domains math} {row : Ty}
      (table : OracleStoredTable model snapshot domains math row)
      (earlier : Reachable self older) (fresh : hasAnchor older table.anchor = false)
      (captures : PayloadBefore self older table) :
      Reachable self (⟨row, table⟩ :: older)

theorem Reachable.older {self : Nat} {older : OracleEntries model snapshot domains math}
    {row : Ty} {table : OracleStoredTable model snapshot domains math row}
    (reachable : Reachable self (⟨row, table⟩ :: older)) :
    Reachable self older ∧ hasAnchor older table.anchor = false ∧ PayloadBefore self older table := by
  cases reachable with | inserted _ earlier fresh captures => exact ⟨earlier, fresh, captures⟩

/-- Every retained table has an actual reachable older suffix, strictly smaller than the
current store. Virtual capture validity is about that suffix, not a hand-installed graph. -/
theorem Reachable.member_older {self : Nat} {entries : OracleEntries model snapshot domains math}
    (reachable : Reachable self entries) (entry : Σ row, OracleStoredTable model snapshot domains math row)
    (member : entry ∈ entries) :
    ∃ newer older, entries = newer ++ entry :: older ∧ Reachable self older ∧
      hasAnchor older entry.2.anchor = false ∧ PayloadBefore self older entry.2 ∧
      older.length < entries.length := by
  induction reachable with
  | empty => simp at member
  | @inserted older row table earlier fresh captures ih =>
    rcases List.mem_cons.mp member with same | member
    · subst entry
      exact ⟨[], older, rfl, earlier, fresh, captures, by simp⟩
    · obtain ⟨newer, earlierEntries, same, earlierPrefix, freshPrefix, capturesPrefix, shorter⟩ := ih member
      refine ⟨⟨row, table⟩ :: newer, earlierEntries, ?_, earlierPrefix, freshPrefix, capturesPrefix, ?_⟩
      · simp only [List.cons_append, same]
      · simp only [List.length_cons]; omega

/-- Insertions expose the actual strict prefix checked by the source handler. -/
def Extension (self : Nat) (before after : OracleEntries model snapshot domains math) : Prop :=
  after = before ∨ ∃ row, ∃ table : OracleStoredTable model snapshot domains math row,
    after = ⟨row, table⟩ :: before ∧ hasAnchor before table.anchor = false ∧ PayloadBefore self before table

theorem Extension.reachable {self : Nat} {before after : OracleEntries model snapshot domains math}
    (step : Extension self before after) (initial : Reachable self before) : Reachable self after := by
  rcases step with rfl | ⟨row, table, rfl, fresh, captures⟩
  · exact initial
  · exact .inserted table initial fresh captures

theorem insert_some {entries result : OracleEntries model snapshot domains math}
    {row : Ty} {table : OracleStoredTable model snapshot domains math row}
    (inserted : insert entries table = some result) :
    result = ⟨row, table⟩ :: entries ∧ hasAnchor entries table.anchor = false := by
  unfold insert at inserted
  split at inserted
  · contradiction
  · exact ⟨(Option.some.inj inserted).symm, by simpa using (by assumption : ¬ _ = true)⟩

@[simp] theorem read_entries {S E : Type} (model : DomainModel)
    (base : PIR.Handler (oracleReadInterface model.toCarriers) S E) (request : OracleRead)
    (state : OracleRuntimeState model snapshot domains math S) :
    (read model base request state).state.entries = state.entries := rfl

end OracleStore

namespace OracleExecution
variable {model : DomainModel} {snapshot : Snapshot} {domains : List DomainSpec}
  {math : OracleMathEnvironment} {S E : Type}

macro "finish_oracle_extension" : tactic => `(tactic| (
  dsimp only [operation, OracleOp.results]
  repeat' first
    | (solve | left; rfl)
    | (split <;> try dsimp only [returned, refusal, OracleStore.read])
  all_goals unfold OracleStore.Extension
  all_goals first
    | exact Or.inl rfl
    | (have insertion := OracleStore.insert_some (by assumption)
       obtain ⟨sameEntries, fresh⟩ := insertion
       rw [sameEntries]
       right
       refine ⟨_, _, rfl, fresh, ?_⟩
       first
       | trivial
       | (subst_vars; simp_all [OracleStore.PayloadBefore, capturedSourcesValid]
          exact And.right (by assumption)))
))

set_option maxHeartbeats 500000 in
theorem operation_extension (model : DomainModel)
    (oracles : List (CheckedOracle snapshot domains math))
    (base : PIR.Handler (oracleReadInterface model.toCarriers) S E)
    (location : OracleLocation) (self : Nat) (roles : Nat → Nat) (op : OracleOp)
    (arguments : Values (Component (ProtocolValue model.toCarriers)) op.arguments)
    (state : OracleRuntimeState model snapshot domains math S) :
    OracleStore.Extension state.self state.entries
      (operation model oracles base location self roles op arguments state).state.entries := by
  cases op with
  | virtual signature holder receivers =>
    finish_oracle_extension
  | query kind owner =>
    cases kind; cases owner
    all_goals cases arguments with
    | cons value rest =>
      cases rest with
      | cons second tail =>
        cases tail
        finish_oracle_extension
  | send kind holder receivers bounds =>
    cases kind
    all_goals cases arguments with
    | cons value rest =>
      cases rest with
      | cons second tail =>
        cases tail
        finish_oracle_extension
  | input sort holder receivers bounds =>
    all_goals cases arguments with
    | cons value rest =>
      cases rest with
      | cons second tail =>
        cases tail
        finish_oracle_extension
  | components sort holder receivers =>
    all_goals cases arguments with
    | cons value rest =>
      cases rest
      finish_oracle_extension
  | contents kind holder =>
    all_goals cases arguments with
    | cons value rest =>
      cases rest
      finish_oracle_extension
  | shape kind dimension =>
    all_goals cases arguments with
    | cons value rest =>
      cases rest
      finish_oracle_extension
  | forgetShape source target =>
    cases source; cases target
    all_goals cases arguments with
    | cons value rest =>
      cases rest
      finish_oracle_extension
  | sequenceEmpty kind maximum selected =>
    cases arguments
    finish_oracle_extension
  | sequenceAppend kind maximum selected =>
    all_goals cases arguments with
    | cons value rest =>
      cases rest with
      | cons second tail =>
        cases tail
        finish_oracle_extension
  | sequenceAt kind maximum selected =>
    all_goals cases arguments with
    | cons value rest =>
      cases rest with
      | cons second tail =>
        cases tail
        finish_oracle_extension
  | sequenceLength kind maximum =>
    all_goals cases arguments with
    | cons value rest =>
      cases rest
      finish_oracle_extension

macro "finish_oracle_self" : tactic => `(tactic| (
  dsimp only [operation, OracleOp.results]
  repeat' first
    | rfl
    | (split <;> try dsimp only [returned, refusal, OracleStore.read])
))

set_option maxHeartbeats 300000 in
theorem operation_self (model : DomainModel)
    (oracles : List (CheckedOracle snapshot domains math))
    (base : PIR.Handler (oracleReadInterface model.toCarriers) S E)
    (location : OracleLocation) (self : Nat) (roles : Nat → Nat) (op : OracleOp)
    (arguments : Values (Component (ProtocolValue model.toCarriers)) op.arguments)
    (state : OracleRuntimeState model snapshot domains math S) :
    (operation model oracles base location self roles op arguments state).state.self = state.self := by
  cases op with
  | virtual signature holder receivers =>
    finish_oracle_self
  | query kind owner =>
    cases kind; cases owner
    all_goals cases arguments with
    | cons value rest =>
      cases rest with
      | cons second tail =>
        cases tail
        finish_oracle_self
  | send kind holder receivers bounds =>
    cases kind
    all_goals cases arguments with
    | cons value rest =>
      cases rest with
      | cons second tail =>
        cases tail
        finish_oracle_self
  | input sort holder receivers bounds =>
    all_goals cases arguments with
    | cons value rest =>
      cases rest with
      | cons second tail =>
        cases tail
        finish_oracle_self
  | components sort holder receivers =>
    all_goals cases arguments with
    | cons value rest =>
      cases rest
      finish_oracle_self
  | contents kind holder =>
    all_goals cases arguments with
    | cons value rest =>
      cases rest
      finish_oracle_self
  | shape kind dimension =>
    all_goals cases arguments with
    | cons value rest =>
      cases rest
      finish_oracle_self
  | forgetShape source target =>
    cases source; cases target
    all_goals cases arguments with
    | cons value rest =>
      cases rest
      finish_oracle_self
  | sequenceEmpty kind maximum selected =>
    cases arguments
    finish_oracle_self
  | sequenceAppend kind maximum selected =>
    all_goals cases arguments with
    | cons value rest =>
      cases rest with
      | cons second tail =>
        cases tail
        finish_oracle_self
  | sequenceAt kind maximum selected =>
    all_goals cases arguments with
    | cons value rest =>
      cases rest with
      | cons second tail =>
        cases tail
        finish_oracle_self
  | sequenceLength kind maximum =>
    all_goals cases arguments with
    | cons value rest =>
      cases rest
      finish_oracle_self

end OracleExecution

namespace OracleStore
variable {model : DomainModel} {snapshot : Snapshot} {domains : List DomainSpec}
  {math : OracleMathEnvironment} {S E : Type}

theorem demandBase_state (request : OracleDataDemand) (location : OracleLocation)
    (state : OracleRuntimeState model snapshot domains math S) :
    (demandBase (E := E) request location state).state = state := by
  unfold demandBase
  split
  · rfl
  · cases request with
    | mk sort requester view =>
      cases sort <;> dsimp only
      all_goals repeat' first | rfl | split

end OracleStore

namespace OracleProtocol
variable {model : DomainModel} {snapshot : Snapshot} {domains : List DomainSpec}
  {math : OracleMathEnvironment} {S E : Type}

def Reachable (state : State model snapshot domains math S) : Prop :=
  OracleStore.Reachable state.oracle.self state.oracle.entries

set_option maxHeartbeats 200000 in
theorem handler_reachable (oracles : List (CheckedOracle snapshot domains math))
    (ordinary : PIR.Handler (participantInterfaceOn model.toCarriers) S E)
    (base : PIR.Handler (oracleReadInterface model.toCarriers) S E)
    (action : (Interface model).Op) (state : State model snapshot domains math S)
    (initial : Reachable state) :
    Reachable ((handler model oracles ordinary base) action state).state := by
  cases action with
  | oracle request =>
    dsimp only [handler]
    split
    · exact initial
    · change OracleStore.Reachable _ _
      rw [OracleExecution.operation_self]
      exact (OracleExecution.operation_extension model oracles base _ _ _ _ _ _).reachable initial
  | demand request =>
    dsimp only [handler]
    change OracleStore.Reachable (OracleStore.demandBase (E := E) _ _ _).state.self
      (OracleStore.demandBase (E := E) _ _ _).state.entries
    rw [OracleStore.demandBase_state]
    exact initial
  | _ =>
    dsimp only [handler]
    all_goals repeat' first | exact initial | split

/-- The invariant follows the reached Process, including failure post-states. It is not
an assumption on a hand-installed store at every child query. -/
theorem run_reachable (oracles : List (CheckedOracle snapshot domains math))
    (ordinary : PIR.Handler (participantInterfaceOn model.toCarriers) S E)
    (base : PIR.Handler (oracleReadInterface model.toCarriers) S E)
    {A : Type} (process : PIR.Process (Interface model) A)
    (state : State model snapshot domains math S) (initial : Reachable state) :
    Reachable (process.run (handler model oracles ordinary base) state).state := by
  induction process generalizing state with
  | done value => exact initial
  | halt reason => exact initial
  | call action next ih =>
    have head := handler_reachable oracles ordinary base action state initial
    cases result : handler model oracles ordinary base action state with
    | mk outcome post events =>
      rw [result] at head
      cases outcome with
      | stopped reason => simpa only [PIR.Process.run, result, PIR.Execution.follow] using head
      | returned reply =>
        simpa only [PIR.Process.run, result, PIR.Execution.follow] using ih reply post head

end OracleProtocol
end Zkc.Source.Structured
