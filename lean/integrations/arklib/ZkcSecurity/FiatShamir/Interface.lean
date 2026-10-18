module

public import Zkc.Semantics.Execution
public import VCVio.OracleComp.QueryTracking.CostModel
public import VCVio.OracleComp.QueryTracking.RandomOracle.FreshQuery

@[expose] public section

/-! The Fiat–Shamir transform of validators over typed query sites.

A validator is a process over any operation signature. A transcript interface
states, for each operation, how the transform treats it:

- a receive reads the next proof message, absorbs an event carrying it and
  continues with the reply that the absorbed event determines;
- a send absorbs an event and continues with a fixed reply;
- a query absorbs its challenge occurrence, asks the transcript oracle at the
  history ending with that occurrence and continues with its own decoding of the
  raw answer, or stops with `exhausted` when the decoder refuses;
- any other operation refuses.

The transcript oracle answers a history `key` in its own raw type `R key`, so
the raw answer may depend on the query occurrence that ends the key (its
method and the operands fixed before sampling). Query sites choose their own
result sorts (field or extension elements, bounded indices, bit strings, gated
or compound challenges) and their own decoders, which may refuse, as a
rejection sampler does. Soundness does not depend on which stop a refusal
reports; `exhausted` is the runtime's outcome for a sampler that gives up.
`transform` is the transform with a challenge function in any monad; `answer`
asks the transcript oracle on all event histories, `OracleSpec.ofFn R`.

`replay` walks a validator along absorbed events, recovering received replies
from their events and answering queries from a table. It is a function of the
events and reads the table only at histories no longer than the replayed one
(`replay_congr`), the two facts the security argument needs.

`QueryBound` counts the queries on every path of a validator and `CostBound`
charges each query the error of its absorbed occurrence; `transform_costBound`
carries the charge to VCVio's pathwise cost model, in which an oracle key is
charged the error of its last event (`keyError`).

A per-key charge `charge : List E → E → ENNReal` charges a query the value at
its whole key: the absorbed history before it and its occurrence. It can count
loop iterations from the history and read operands carried in the occurrence.
`ChargedCostBound` bounds the charges on every path of a validator from a given
history, and `transform_chargedCostBound` carries it to the cost model, in which
a key is charged `keyCharge charge`. A charge that ignores the history is the
error of the occurrence (`keyCharge_const`, `CostBound.charged`).
-/

set_option autoImplicit false

namespace ZkcSecurity.FiatShamir
open OracleComp OracleSpec

/-- A returned value satisfying the acceptance predicate. Stops never accept. -/
def Accepted {A : Type} (accepts : A → Prop) : PIR.Outcome A → Prop
  | .returned value => accepts value
  | .stopped _ => False

namespace Typed

/-- How the transform treats one validator operation whose reply has type
`Reply`. Transcript events have type `E`, proof messages `P`, and the oracle
answers a history `key` in `R key`. -/
inductive Absorption (E P : Type) (R : List E → Type) (Reply : Type) where
  /-- Read the next proof message, absorb `event message` and continue with the
  reply `recover` reads from that event. A message whose event recovers no reply
  refuses without being consumed. -/
  | receive (event : P → E) (recover : E → Option Reply)
  /-- Absorb `event` and continue with `value`. Produces no proof data. -/
  | send (event : E) (value : Reply)
  /-- Absorb the challenge occurrence `event`, ask the oracle at the history
  `preceding ++ [event]` and continue with `decode preceding` of its raw answer;
  a refused decoding stops with `exhausted`. -/
  | query (event : E) (decode : (preceding : List E) → R (preceding ++ [event]) → Option Reply)
  /-- Refuse without consuming proof data. -/
  | refuse

/-- A transcript interface: the absorption of every operation of `I`. -/
abbrev Interface (I : PIR.Signature) (E P : Type) (R : List E → Type) :=
  (operation : I.Op) → Absorption E P R (I.Reply operation)

variable {I : PIR.Signature} {E P A : Type} {R : List E → Type}

section Transform
variable {m : Type → Type} [Monad m]

/-- The Fiat–Shamir transform of `process` over the interface `absorb`, from the
absorbed `history`, reading proof messages from `proof` and answering queries
with `oracle`. Returns the outcome and the unread proof suffix. -/
def transform (absorb : Interface I E P R) (oracle : (key : List E) → m (R key)) :
    PIR.Proc I A → List E → List P → m (PIR.Outcome A × List P)
  | .done value, _, proof => pure (.returned value, proof)
  | .halt stop, _, proof => pure (.stopped stop, proof)
  | .call operation next, history, proof =>
      match absorb operation with
      | .receive event recover =>
          match proof with
          | [] => pure (.stopped .refused, [])
          | message :: rest =>
              match recover (event message) with
              | some value =>
                  transform absorb oracle (next value) (history ++ [event message]) rest
              | none => pure (.stopped .refused, message :: rest)
      | .send event value => transform absorb oracle (next value) (history ++ [event]) proof
      | .query event decode => do
          let raw ← oracle (history ++ [event])
          match decode history raw with
          | some value => transform absorb oracle (next value) (history ++ [event]) proof
          | none => pure (.stopped .exhausted, proof)
      | .refuse => pure (.stopped .refused, proof)

variable (absorb : Interface I E P R) (oracle : (key : List E) → m (R key))

theorem transform_receive {operation : I.Op} {next : I.Reply operation → PIR.Proc I A}
    {event : P → E} {recover : E → Option (I.Reply operation)}
    (absorbed : absorb operation = .receive event recover) (history : List E) (message : P)
    (rest : List P) :
    transform absorb oracle (.call operation next) history (message :: rest) =
      match recover (event message) with
      | some value => transform absorb oracle (next value) (history ++ [event message]) rest
      | none => pure (.stopped .refused, message :: rest) := by
  simp only [transform, absorbed]

theorem transform_receive_nil {operation : I.Op} {next : I.Reply operation → PIR.Proc I A}
    {event : P → E} {recover : E → Option (I.Reply operation)}
    (absorbed : absorb operation = .receive event recover) (history : List E) :
    transform absorb oracle (.call operation next) history [] = pure (.stopped .refused, []) := by
  simp only [transform, absorbed]

theorem transform_send {operation : I.Op} {next : I.Reply operation → PIR.Proc I A}
    {event : E} {value : I.Reply operation} (absorbed : absorb operation = .send event value)
    (history : List E) (proof : List P) :
    transform absorb oracle (.call operation next) history proof =
      transform absorb oracle (next value) (history ++ [event]) proof := by
  simp only [transform, absorbed]

theorem transform_query {operation : I.Op} {next : I.Reply operation → PIR.Proc I A}
    {event : E}
    {decode : (preceding : List E) → R (preceding ++ [event]) → Option (I.Reply operation)}
    (absorbed : absorb operation = .query event decode) (history : List E) (proof : List P) :
    transform absorb oracle (.call operation next) history proof =
      oracle (history ++ [event]) >>= fun raw =>
        match decode history raw with
        | some value => transform absorb oracle (next value) (history ++ [event]) proof
        | none => pure (.stopped .exhausted, proof) := by
  simp only [transform, absorbed]

theorem transform_refuse {operation : I.Op} {next : I.Reply operation → PIR.Proc I A}
    (absorbed : absorb operation = .refuse) (history : List E) (proof : List P) :
    transform absorb oracle (.call operation next) history proof =
      pure (.stopped .refused, proof) := by
  simp only [transform, absorbed]

end Transform

/-- One transcript challenge: the transcript oracle on all event histories,
asked at `key`. -/
def answer (key : List E) : OracleComp (OracleSpec.ofFn R) (R key) :=
  liftM ((OracleSpec.ofFn R).query key)

section Replay
variable [DecidableEq E]

/-- Walk `process` along the absorbed `events`, starting after `history`.
Received replies are recovered from their events and queries are answered by
decoding `table` at the history ending with their occurrence. The result is the
residual process after the last event, or `none` when the events are not a
history the transform could absorb from this process. -/
def replay (absorb : Interface I E P R) (table : (key : List E) → R key) :
    PIR.Proc I A → List E → List E → Option (PIR.Proc I A)
  | process, _, [] => some process
  | .done _, _, _ :: _ => none
  | .halt _, _, _ :: _ => none
  | .call operation next, history, observed :: rest =>
      match absorb operation with
      | .receive _ recover =>
          match recover observed with
          | some value => replay absorb table (next value) (history ++ [observed]) rest
          | none => none
      | .send event value =>
          if observed = event then replay absorb table (next value) (history ++ [observed]) rest
          else none
      | .query event decode =>
          if observed = event then
            match decode history (table (history ++ [event])) with
            | some value => replay absorb table (next value) (history ++ [event]) rest
            | none => none
          else none
      | .refuse => none

variable (absorb : Interface I E P R) (table : (key : List E) → R key)

@[simp] theorem replay_nil (process : PIR.Proc I A) (history : List E) :
    replay absorb table process history [] = some process := by
  cases process <;> rfl

/-- One received message, absorbed with its event. -/
theorem replay_receive {operation : I.Op} {next : I.Reply operation → PIR.Proc I A}
    {event : P → E} {recover : E → Option (I.Reply operation)}
    (absorbed : absorb operation = .receive event recover) (history : List E) (message : P)
    {value : I.Reply operation} (recovered : recover (event message) = some value) :
    replay absorb table (.call operation next) history [event message] = some (next value) := by
  simp [replay, absorbed, recovered]

/-- One sent value, absorbed with its event. -/
theorem replay_send {operation : I.Op} {next : I.Reply operation → PIR.Proc I A}
    {event : E} {value : I.Reply operation} (absorbed : absorb operation = .send event value)
    (history : List E) :
    replay absorb table (.call operation next) history [event] = some (next value) := by
  simp [replay, absorbed]

/-- One challenge occurrence, answered by decoding the table at the history
ending with it. -/
theorem replay_query {operation : I.Op} {next : I.Reply operation → PIR.Proc I A}
    {event : E}
    {decode : (preceding : List E) → R (preceding ++ [event]) → Option (I.Reply operation)}
    (absorbed : absorb operation = .query event decode) (history : List E)
    {value : I.Reply operation}
    (decoded : decode history (table (history ++ [event])) = some value) :
    replay absorb table (.call operation next) history [event] = some (next value) := by
  simp [replay, absorbed, decoded]

/-- Replaying a concatenation replays the first part, then the second from the
residual and the extended history. -/
theorem replay_append (first second : List E) :
    ∀ (process : PIR.Proc I A) (history : List E),
      replay absorb table process history (first ++ second) =
        (replay absorb table process history first).bind fun residual =>
          replay absorb table residual (history ++ first) second := by
  induction first with
  | nil => intro process history; simp
  | cons observed rest ih =>
      intro process history
      cases process with
      | done value => rfl
      | halt stop => rfl
      | call operation next =>
          rcases absorbed : absorb operation with ⟨event, recover⟩ | ⟨event, value⟩ |
            ⟨event, decode⟩ | _
          · simp only [List.cons_append, replay, absorbed]
            cases recover observed with
            | none => rfl
            | some value => simp [ih]
          · simp only [List.cons_append, replay, absorbed]
            split
            · simp [ih]
            · rfl
          · simp only [List.cons_append, replay, absorbed]
            split
            · rename_i same
              subst same
              cases decode history (table (history ++ [observed])) with
              | none => rfl
              | some value => simp [ih]
            · rfl
          · simp only [List.cons_append, replay, absorbed]
            rfl

/-- Replay reads the table only at histories no longer than the replayed one. -/
theorem replay_congr {other : (key : List E) → R key} (events : List E) :
    ∀ (process : PIR.Proc I A) (history : List E),
      (∀ key : List E, key.length ≤ history.length + events.length → table key = other key) →
      replay absorb table process history events = replay absorb other process history events := by
  induction events with
  | nil => intro process history _; simp
  | cons observed rest ih =>
      intro process history agree
      have shifted : ∀ key : List E,
          key.length ≤ (history ++ [observed]).length + rest.length → table key = other key := by
        intro key bound
        apply agree
        simp only [List.length_append, List.length_cons, List.length_nil] at bound ⊢
        omega
      cases process with
      | done value => rfl
      | halt stop => rfl
      | call operation next =>
          rcases absorbed : absorb operation with ⟨event, recover⟩ | ⟨event, value⟩ |
            ⟨event, decode⟩ | _
          · simp only [replay, absorbed]
            cases recover observed with
            | none => rfl
            | some value => exact ih _ _ shifted
          · simp only [replay, absorbed]
            split
            · exact ih _ _ shifted
            · rfl
          · simp only [replay, absorbed]
            split
            · rename_i same
              subst same
              have agreeing : table (history ++ [observed]) = other (history ++ [observed]) := by
                apply agree
                simp
              rw [agreeing]
              cases decode history (other (history ++ [observed])) with
              | none => rfl
              | some value => exact ih _ _ shifted
            · rfl
          · simp only [replay, absorbed]

end Replay

section Bounds

/-- At most `budget` queries on every path, for every reply. -/
def QueryBound (absorb : Interface I E P R) : PIR.Proc I A → ℕ → Prop
  | .done _, _ => True
  | .halt _, _ => True
  | .call operation next, budget =>
      match absorb operation with
      | .receive _ _ => ∀ value, QueryBound absorb (next value) budget
      | .send _ value => QueryBound absorb (next value) budget
      | .query _ _ => 0 < budget ∧ ∀ value, QueryBound absorb (next value) (budget - 1)
      | .refuse => True

/-- The queries on every path charge at most `cost` in total, each query the
error of its absorbed occurrence. -/
def CostBound (absorb : Interface I E P R) (error : E → ENNReal) :
    PIR.Proc I A → ENNReal → Prop
  | .done _, _ => True
  | .halt _, _ => True
  | .call operation next, cost =>
      match absorb operation with
      | .receive _ _ => ∀ value, CostBound absorb error (next value) cost
      | .send _ value => CostBound absorb error (next value) cost
      | .query event _ => ∃ remaining, error event + remaining ≤ cost ∧
          ∀ value, CostBound absorb error (next value) remaining
      | .refuse => True

variable (absorb : Interface I E P R) (error : E → ENNReal)

theorem CostBound.mono :
    ∀ (process : PIR.Proc I A) {cost larger : ENNReal},
      CostBound absorb error process cost → cost ≤ larger → CostBound absorb error process larger
  | .done _, _, _, _, _ => trivial
  | .halt _, _, _, _, _ => trivial
  | .call operation next, _, _, bounded, le => by
      rcases absorbed : absorb operation with ⟨event, recover⟩ | ⟨event, value⟩ |
        ⟨event, decode⟩ | _
      · simp only [CostBound, absorbed] at bounded ⊢
        exact fun value => CostBound.mono (next value) (bounded value) le
      · simp only [CostBound, absorbed] at bounded ⊢
        exact CostBound.mono (next value) bounded le
      · simp only [CostBound, absorbed] at bounded ⊢
        obtain ⟨remaining, charged, rest⟩ := bounded
        exact ⟨remaining, charged.trans le, rest⟩
      · simp only [CostBound, absorbed]

/-- A query count with every occurrence error at most `bound` charges at most
`budget * bound`. -/
theorem QueryBound.costBound {bound : ENNReal} (bounded : ∀ event, error event ≤ bound) :
    ∀ (process : PIR.Proc I A) (budget : ℕ),
      QueryBound absorb process budget → CostBound absorb error process (budget * bound)
  | .done _, _, _ => trivial
  | .halt _, _, _ => trivial
  | .call operation next, budget, counted => by
      rcases absorbed : absorb operation with ⟨event, recover⟩ | ⟨event, value⟩ |
        ⟨event, decode⟩ | _
      · simp only [QueryBound, absorbed] at counted
        simp only [CostBound, absorbed]
        exact fun value => QueryBound.costBound bounded (next value) budget (counted value)
      · simp only [QueryBound, absorbed] at counted
        simp only [CostBound, absorbed]
        exact QueryBound.costBound bounded (next value) budget counted
      · simp only [QueryBound, absorbed] at counted
        simp only [CostBound, absorbed]
        obtain ⟨positive, rest⟩ := counted
        refine ⟨((budget - 1 : ℕ) : ENNReal) * bound, ?_, fun value =>
          QueryBound.costBound bounded (next value) (budget - 1) (rest value)⟩
        calc error event + ((budget - 1 : ℕ) : ENNReal) * bound
            ≤ bound + ((budget - 1 : ℕ) : ENNReal) * bound := add_le_add_left (bounded event) _
          _ = (budget : ENNReal) * bound := by
            rw [← one_add_mul, ← Nat.cast_one, ← Nat.cast_add, Nat.add_sub_cancel' positive]
      · simp only [CostBound, absorbed]

/-- The error charged to an oracle key: the error of its last event, zero for
the empty history. -/
def keyError (key : List E) : ENNReal :=
  match key.getLast? with
  | some event => error event
  | none => 0

@[simp] theorem keyError_append_singleton (history : List E) (event : E) :
    keyError error (history ++ [event]) = error event := by
  simp [keyError]

/-- The charge of an oracle key under a per-key charge: the charge of its last
event after the history before it, zero for the empty history. -/
def keyCharge (charge : List E → E → ENNReal) (key : List E) : ENNReal :=
  match key.getLast? with
  | some event => charge key.dropLast event
  | none => 0

@[simp] theorem keyCharge_append_singleton (charge : List E → E → ENNReal) (history : List E)
    (event : E) : keyCharge charge (history ++ [event]) = charge history event := by
  simp [keyCharge]

/-- A charge that ignores the history before the occurrence charges every key the
error of its last event. -/
theorem keyCharge_const : keyCharge (fun _ event => error event) = keyError error := by
  funext key
  unfold keyCharge keyError
  cases key.getLast? <;> rfl

/-- The queries on every path from the absorbed `history` charge at most `cost`
in total, each query the charge of its key: the history before it and its
occurrence. -/
def ChargedCostBound (charge : List E → E → ENNReal) :
    PIR.Proc I A → List E → ENNReal → Prop
  | .done _, _, _ => True
  | .halt _, _, _ => True
  | .call operation next, history, cost =>
      match absorb operation with
      | .receive event _ => ∀ message value,
          ChargedCostBound charge (next value) (history ++ [event message]) cost
      | .send event value => ChargedCostBound charge (next value) (history ++ [event]) cost
      | .query event _ => ∃ remaining, charge history event + remaining ≤ cost ∧
          ∀ value, ChargedCostBound charge (next value) (history ++ [event]) remaining
      | .refuse => True

/-- A cost bound with an error per occurrence is a charged cost bound, from any
history, for the charge that ignores the history. -/
theorem CostBound.charged :
    ∀ (process : PIR.Proc I A) (cost : ENNReal), CostBound absorb error process cost →
      ∀ history, ChargedCostBound absorb (fun _ event => error event) process history cost
  | .done _, _, _, _ => trivial
  | .halt _, _, _, _ => trivial
  | .call operation next, cost, bounded, history => by
      rcases absorbed : absorb operation with ⟨event, recover⟩ | ⟨event, value⟩ |
        ⟨event, decode⟩ | _
      · simp only [CostBound, absorbed] at bounded
        simp only [ChargedCostBound, absorbed]
        exact fun message value => CostBound.charged (next value) cost (bounded value) _
      · simp only [CostBound, absorbed] at bounded
        simp only [ChargedCostBound, absorbed]
        exact CostBound.charged (next value) cost bounded _
      · simp only [CostBound, absorbed] at bounded
        simp only [ChargedCostBound, absorbed]
        obtain ⟨remaining, charged, rest⟩ := bounded
        exact ⟨remaining, charged, fun value => CostBound.charged (next value) remaining (rest value) _⟩
      · simp only [ChargedCostBound, absorbed]

/-- A query count with every charge at most `bound` charges at most
`budget * bound` from every history. -/
theorem QueryBound.chargedCostBound {charge : List E → E → ENNReal} {bound : ENNReal}
    (bounded : ∀ history event, charge history event ≤ bound) :
    ∀ (process : PIR.Proc I A) (budget : ℕ), QueryBound absorb process budget →
      ∀ history, ChargedCostBound absorb charge process history (budget * bound)
  | .done _, _, _, _ => trivial
  | .halt _, _, _, _ => trivial
  | .call operation next, budget, counted, history => by
      rcases absorbed : absorb operation with ⟨event, recover⟩ | ⟨event, value⟩ |
        ⟨event, decode⟩ | _
      · simp only [QueryBound, absorbed] at counted
        simp only [ChargedCostBound, absorbed]
        exact fun message value =>
          QueryBound.chargedCostBound bounded (next value) budget (counted value) _
      · simp only [QueryBound, absorbed] at counted
        simp only [ChargedCostBound, absorbed]
        exact QueryBound.chargedCostBound bounded (next value) budget counted _
      · simp only [QueryBound, absorbed] at counted
        simp only [ChargedCostBound, absorbed]
        obtain ⟨positive, rest⟩ := counted
        refine ⟨((budget - 1 : ℕ) : ENNReal) * bound, ?_, fun value =>
          QueryBound.chargedCostBound bounded (next value) (budget - 1) (rest value) _⟩
        calc charge history event + ((budget - 1 : ℕ) : ENNReal) * bound
            ≤ bound + ((budget - 1 : ℕ) : ENNReal) * bound :=
              add_le_add_left (bounded history event) _
          _ = (budget : ENNReal) * bound := by
            rw [← one_add_mul, ← Nat.cast_one, ← Nat.cast_add, Nat.add_sub_cancel' positive]
      · simp only [ChargedCostBound, absorbed]

/-- A total query count with every key error at most `bound` charges at most
`queries * bound` on every path. -/
theorem worstCaseCostBound_of_isTotalQueryBound {α D : Type} {Raw : D → Type}
    [∀ key : D, Nonempty (Raw key)]
    (weight : D → ENNReal) {bound : ENNReal} (bounded : ∀ key, weight key ≤ bound) :
    ∀ (computation : OracleComp (OracleSpec.ofFn Raw) α) (queries : ℕ),
      IsTotalQueryBound computation queries →
        WorstCaseCostBound computation ⟨weight⟩ (queries * bound) := by
  intro computation
  induction computation using OracleComp.inductionOn with
  | pure value =>
      intro queries _
      exact (worstCaseCostBound_pure _ _ _).mpr zero_le
  | query_bind key next ih =>
      intro queries counted
      obtain ⟨positive, rest⟩ := isTotalQueryBound_query_bind_iff.mp counted
      rw [worstCaseCostBound_query_bind_iff]
      intro reply charged member
      have tail := (worstCaseCostBound_iff_support_bound _ _ _).mp
        (ih reply (queries - 1) (rest reply)) charged member
      calc weight key + Multiplicative.toAdd charged.2
          ≤ bound + ((queries - 1 : ℕ) : ENNReal) * bound := add_le_add (bounded key) tail
        _ = (queries : ENNReal) * bound := by
          rw [← one_add_mul, ← Nat.cast_one, ← Nat.cast_add, Nat.add_sub_cancel' positive]

theorem worstCaseCostBound_map {α β : Type} (f : α → β)
    (computation : OracleComp (OracleSpec.ofFn R) α) (weight : List E → ENNReal)
    (cost : ENNReal) (bounded : WorstCaseCostBound computation ⟨weight⟩ cost) :
    WorstCaseCostBound (f <$> computation) ⟨weight⟩ cost := by
  have composed := WorstCaseCostBound.bind (k := fun value => (pure (f value) :
      OracleComp (OracleSpec.ofFn R) β)) bounded fun _ =>
    (worstCaseCostBound_pure _ _ (0 : ENNReal)).mpr le_rfl
  rw [add_zero] at composed
  simpa only [map_eq_bind_pure_comp, Function.comp_def] using composed

/-- The transform makes at most the validator's cost on every path, each query
charged the error of its key. -/
theorem transform_costBound :
    ∀ (process : PIR.Proc I A) (cost : ENNReal) (history : List E) (proof : List P),
      CostBound absorb error process cost →
        WorstCaseCostBound (transform absorb answer process history proof)
          ⟨keyError error⟩ cost := by
  intro process
  induction process with
  | done value =>
      intro cost history proof _
      exact (worstCaseCostBound_pure _ _ _).mpr zero_le
  | halt stop =>
      intro cost history proof _
      exact (worstCaseCostBound_pure _ _ _).mpr zero_le
  | call operation next ih =>
      intro cost history proof bounded
      rcases absorbed : absorb operation with ⟨event, recover⟩ | ⟨event, value⟩ |
        ⟨event, decode⟩ | _
      · simp only [CostBound, absorbed] at bounded
        cases proof with
        | nil =>
            rw [transform_receive_nil absorb _ absorbed]
            exact (worstCaseCostBound_pure _ _ _).mpr zero_le
        | cons message rest =>
            rw [transform_receive absorb _ absorbed]
            cases recover (event message) with
            | none => exact (worstCaseCostBound_pure _ _ _).mpr zero_le
            | some value => exact ih value cost _ rest (bounded value)
      · simp only [CostBound, absorbed] at bounded
        rw [transform_send absorb _ absorbed]
        exact ih value cost _ proof bounded
      · simp only [CostBound, absorbed] at bounded
        obtain ⟨remaining, charged, rest⟩ := bounded
        rw [transform_query absorb _ absorbed, answer, worstCaseCostBound_query_bind_iff]
        intro raw total member
        have tail : Multiplicative.toAdd total.2 ≤ remaining := by
          revert member
          cases decode history raw with
          | none =>
              intro member
              exact (worstCaseCostBound_iff_support_bound _ _ _).mp
                ((worstCaseCostBound_pure _ _ _).mpr zero_le) total member
          | some value =>
              intro member
              exact (worstCaseCostBound_iff_support_bound _ _ _).mp
                (ih value remaining (history ++ [event]) proof (rest value)) total member
        calc keyError error (history ++ [event]) + Multiplicative.toAdd total.2
            ≤ error event + remaining := by
              rw [keyError_append_singleton]
              exact add_le_add le_rfl tail
          _ ≤ cost := charged
      · rw [transform_refuse absorb _ absorbed]
        exact (worstCaseCostBound_pure _ _ _).mpr zero_le

/-- The transform charges at most the validator's charged cost on every path,
each query charged `keyCharge charge` at its key. -/
theorem transform_chargedCostBound (charge : List E → E → ENNReal) :
    ∀ (process : PIR.Proc I A) (cost : ENNReal) (history : List E) (proof : List P),
      ChargedCostBound absorb charge process history cost →
        WorstCaseCostBound (transform absorb answer process history proof)
          ⟨keyCharge charge⟩ cost := by
  intro process
  induction process with
  | done value =>
      intro cost history proof _
      exact (worstCaseCostBound_pure _ _ _).mpr zero_le
  | halt stop =>
      intro cost history proof _
      exact (worstCaseCostBound_pure _ _ _).mpr zero_le
  | call operation next ih =>
      intro cost history proof bounded
      rcases absorbed : absorb operation with ⟨event, recover⟩ | ⟨event, value⟩ |
        ⟨event, decode⟩ | _
      · simp only [ChargedCostBound, absorbed] at bounded
        cases proof with
        | nil =>
            rw [transform_receive_nil absorb _ absorbed]
            exact (worstCaseCostBound_pure _ _ _).mpr zero_le
        | cons message rest =>
            rw [transform_receive absorb _ absorbed]
            cases recover (event message) with
            | none => exact (worstCaseCostBound_pure _ _ _).mpr zero_le
            | some value => exact ih value cost _ rest (bounded message value)
      · simp only [ChargedCostBound, absorbed] at bounded
        rw [transform_send absorb _ absorbed]
        exact ih value cost _ proof bounded
      · simp only [ChargedCostBound, absorbed] at bounded
        obtain ⟨remaining, charged, rest⟩ := bounded
        rw [transform_query absorb _ absorbed, answer, worstCaseCostBound_query_bind_iff]
        intro raw total member
        have tail : Multiplicative.toAdd total.2 ≤ remaining := by
          revert member
          cases decode history raw with
          | none =>
              intro member
              exact (worstCaseCostBound_iff_support_bound _ _ _).mp
                ((worstCaseCostBound_pure _ _ _).mpr zero_le) total member
          | some value =>
              intro member
              exact (worstCaseCostBound_iff_support_bound _ _ _).mp
                (ih value remaining (history ++ [event]) proof (rest value)) total member
        calc keyCharge charge (history ++ [event]) + Multiplicative.toAdd total.2
            ≤ charge history event + remaining := by
              rw [keyCharge_append_singleton]
              exact add_le_add le_rfl tail
          _ ≤ cost := charged
      · rw [transform_refuse absorb _ absorbed]
        exact (worstCaseCostBound_pure _ _ _).mpr zero_le

/-- The transform makes at most the validator's query count on every path. -/
theorem transform_queryBound :
    ∀ (process : PIR.Proc I A) (budget : ℕ) (history : List E) (proof : List P),
      QueryBound absorb process budget →
        IsTotalQueryBound (transform absorb answer process history proof) budget := by
  intro process
  induction process with
  | done value => intro budget history proof _; trivial
  | halt stop => intro budget history proof _; trivial
  | call operation next ih =>
      intro budget history proof bounded
      rcases absorbed : absorb operation with ⟨event, recover⟩ | ⟨event, value⟩ |
        ⟨event, decode⟩ | _
      · simp only [QueryBound, absorbed] at bounded
        cases proof with
        | nil =>
            rw [transform_receive_nil absorb _ absorbed]
            trivial
        | cons message rest =>
            rw [transform_receive absorb _ absorbed]
            cases recover (event message) with
            | none => trivial
            | some value => exact ih value budget _ rest (bounded value)
      · simp only [QueryBound, absorbed] at bounded
        rw [transform_send absorb _ absorbed]
        exact ih value budget _ proof bounded
      · simp only [QueryBound, absorbed] at bounded
        rw [transform_query absorb _ absorbed, answer]
        refine isTotalQueryBound_query_bind_iff.mpr ⟨bounded.1, fun raw => ?_⟩
        cases decode history raw with
        | none => trivial
        | some value => exact ih value _ _ _ (bounded.2 value)
      · rw [transform_refuse absorb _ absorbed]
        trivial

end Bounds

section Execution

theorem tableQueryLog_map {α β : Type} (f : α → β)
    (computation : OracleComp (OracleSpec.ofFn R) α) (table : (key : List E) → R key) :
    tableQueryLog (f <$> computation) table = tableQueryLog computation table := by
  rw [map_eq_bind_pure_comp, tableQueryLog_bind]
  simp

/-- Deterministic evaluation of the oracle transform against a total table is
the transform with the table as challenge function. -/
theorem evalWithAnswerFn_transform (absorb : Interface I E P R)
    (table : (key : List E) → R key) :
    ∀ (process : PIR.Proc I A) (history : List E) (proof : List P),
      evalWithAnswerFn (QueryImpl.ofFn table) (transform absorb answer process history proof) =
        transform (m := Id) absorb table process history proof := by
  intro process
  induction process with
  | done value => intro history proof; rfl
  | halt stop => intro history proof; rfl
  | call operation next ih =>
      intro history proof
      rcases absorbed : absorb operation with ⟨event, recover⟩ | ⟨event, value⟩ |
        ⟨event, decode⟩ | _
      · cases proof with
        | nil =>
            rw [transform_receive_nil absorb _ absorbed, transform_receive_nil absorb _ absorbed]
            rfl
        | cons message rest =>
            rw [transform_receive absorb _ absorbed, transform_receive absorb _ absorbed]
            cases recover (event message) with
            | none => rfl
            | some value => exact ih value _ _
      · rw [transform_send absorb _ absorbed, transform_send absorb _ absorbed]
        exact ih value _ _
      · rw [transform_query absorb _ absorbed, transform_query absorb _ absorbed, answer,
          evalWithAnswerFn_bind, evalWithAnswerFn_liftM_query, QueryImpl.ofFn_apply]
        change _ = (match decode history (table (history ++ [event])) with
          | some value => transform (m := Id) absorb table (next value) (history ++ [event]) proof
          | none => pure (.stopped .exhausted, proof))
        cases decode history (table (history ++ [event])) with
        | none => rfl
        | some value => exact ih value _ _
      · rw [transform_refuse absorb _ absorbed, transform_refuse absorb _ absorbed]
        rfl

end Execution

/-- The initial histories determine the statements: when two statements' initial
histories, each followed by some events, are equal, the statements are equal.
Injective initial histories of which none is a proper prefix of another satisfy
this. -/
def Determined {Stmt : Type} (initial : Stmt → List E) : Prop :=
  ∀ statement other (rest otherRest : List E),
    initial statement ++ rest = initial other ++ otherRest → statement = other

end Typed

end ZkcSecurity.FiatShamir
