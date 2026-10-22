module

public import Zkc.Transcript.Replay
public import VCVio.OracleComp.Constructions.SampleableType.NativeMeasure
public import VCVio.OracleComp.QueryTracking.CostModel
public import VCVio.OracleComp.QueryTracking.RandomOracle.FreshQuery

@[expose] public section

/-! The Fiat–Shamir transform of validators over typed query sites, against a
history oracle.

The transcript interface, the transform, replay and acceptance are the core
definitions of `Zkc.Transcript`: a query absorbs its occurrence, asks the
transcript oracle at the history ending with it and decodes the raw answer
`Raw event` of its occurrence alone. This module runs the transform against
VCVio's lazily sampled oracle on event histories and states its query costs.

**The history oracle.** The oracle `OracleSpec.ofFn R` answers every event
history `key` in `R key`; the prover may ask any key, including the empty one.
At a key ending with a query occurrence the answer reads, by an equivalence, as
a raw answer of that occurrence (`ReadsByOccurrence`). Two readings cover the
consumers: a range independent of the key (`fun _ => B`, read as itself), and
the range by the last event, `ByLast Raw`, which is `Raw` of the key's last
event and `Unit` at the empty key, where no query lands (`ByLast.read`). `ask`
is the transcript oracle the transform uses: the history oracle at the
concatenation, read in the occurrence's raw type.

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

export Zkc.Transcript (Accepted AcceptedComplete)

namespace Typed

export Zkc.Transcript (Absorption Interface transform replay Determined)

variable {I : PIR.Signature} {E P A : Type} {Raw : E → Type}

section Reading

/-- A history oracle answering a key in `R key`, whose answer at a key ending
with a query occurrence reads, by an equivalence, as a raw answer of that
occurrence. -/
class ReadsByOccurrence (R : List E → Type) (Raw : E → Type) where
  read : (preceding : List E) → (event : E) → R (preceding ++ [event]) ≃ Raw event

/-- A history oracle whose range does not depend on the key reads every answer
as itself. -/
instance ReadsByOccurrence.constant (B : Type) :
    ReadsByOccurrence (E := E) (fun _ => B) (fun _ => B) where
  read _ _ := Equiv.refl B

variable (Raw) in
/-- `Raw` of the last event, and `Unit` without one. -/
def OfLast : Option E → Type
  | some event => Raw event
  | none => Unit

variable (Raw) in
/-- The raw answer type of a history key: the raw type of its last event, and
`Unit` at the empty key, which no query reaches. -/
abbrev ByLast (key : List E) : Type := OfLast Raw key.getLast?

variable (Raw) in
theorem byLast_append (preceding : List E) (event : E) :
    ByLast Raw (preceding ++ [event]) = Raw event := by
  simp [ByLast, OfLast]

variable (Raw) in
/-- The answer at a key ending with an occurrence, read in the occurrence's raw
type. -/
def ByLast.read {preceding : List E} {event : E} : ByLast Raw (preceding ++ [event]) ≃ Raw event :=
  Equiv.cast (byLast_append Raw preceding event)

/-- The history oracle with raw answers by the last event reads every answer at
a key ending with an occurrence in the occurrence's raw type. -/
instance ByLast.reads : ReadsByOccurrence (ByLast Raw) Raw where
  read _ _ := ByLast.read Raw

instance OfLast.sampleable [∀ event, SampleableType (Raw event)] :
    ∀ last : Option E, SampleableType (OfLast Raw last)
  | some event => inferInstanceAs (SampleableType (Raw event))
  | none => inferInstanceAs (SampleableType Unit)

instance ByLast.sampleable [∀ event, SampleableType (Raw event)] (key : List E) :
    SampleableType (ByLast Raw key) :=
  OfLast.sampleable key.getLast?

variable (Raw) in
/-- Read in the occurrence's raw type, the uniform answer at a key is uniform. -/
theorem prEvent_read [∀ event, SampleableType (Raw event)] (preceding : List E) (event : E)
    (holds : Raw event → Prop) :
    Pr{let raw ← $ᵗ (ByLast Raw (preceding ++ [event]))}[holds (ByLast.read Raw raw)] =
      Pr{let raw ← $ᵗ (Raw event)}[holds raw] :=
  SampleableType.prEvent_uniformSample_equiv _ holds

/-- Read in the occurrence's raw type, the uniform answer of a history oracle at
a key ending with the occurrence is uniform. -/
theorem prEvent_reads {R : List E → Type} [ReadsByOccurrence R Raw] [∀ key, SampleableType (R key)]
    [∀ event, SampleableType (Raw event)] (preceding : List E) (event : E)
    (holds : Raw event → Prop) :
    Pr{let raw ← $ᵗ (R (preceding ++ [event]))}[holds (ReadsByOccurrence.read preceding event raw)] =
      Pr{let raw ← $ᵗ (Raw event)}[holds raw] :=
  SampleableType.prEvent_uniformSample_equiv _ holds

end Reading

variable {R : List E → Type}

/-- One transcript challenge: the transcript oracle on all event histories,
asked at `key`. -/
def answer (key : List E) : OracleComp (OracleSpec.ofFn R) (R key) :=
  liftM ((OracleSpec.ofFn R).query key)

/-- The transcript oracle of the transform: the history oracle at the absorbed
history followed by the occurrence, read in the occurrence's raw type. -/
def ask [ReadsByOccurrence R Raw] (preceding : List E) (event : E) :
    OracleComp (OracleSpec.ofFn R) (Raw event) :=
  ReadsByOccurrence.read preceding event <$> answer (preceding ++ [event])

/-- A table of history answers, read at a history before an occurrence and the
occurrence. -/
def readTable [ReadsByOccurrence R Raw] (table : (key : List E) → R key)
    (preceding : List E) (event : E) : Raw event :=
  ReadsByOccurrence.read preceding event (table (preceding ++ [event]))

section Bounds

/-- At most `budget` queries on every path, for every reply. -/
def QueryBound (absorb : Interface I E P Raw) : PIR.Process I A → ℕ → Prop
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
def CostBound (absorb : Interface I E P Raw) (error : E → ENNReal) :
    PIR.Process I A → ENNReal → Prop
  | .done _, _ => True
  | .halt _, _ => True
  | .call operation next, cost =>
      match absorb operation with
      | .receive _ _ => ∀ value, CostBound absorb error (next value) cost
      | .send _ value => CostBound absorb error (next value) cost
      | .query event _ => ∃ remaining, error event + remaining ≤ cost ∧
          ∀ value, CostBound absorb error (next value) remaining
      | .refuse => True

variable (absorb : Interface I E P Raw) (error : E → ENNReal)

theorem CostBound.mono :
    ∀ (process : PIR.Process I A) {cost larger : ENNReal},
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
    ∀ (process : PIR.Process I A) (budget : ℕ),
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

/-- A charge bounded everywhere bounds every key's charge. -/
theorem keyCharge_le {charge : List E → E → ENNReal} {bound : ENNReal}
    (bounded : ∀ history event, charge history event ≤ bound) (key : List E) :
    keyCharge charge key ≤ bound := by
  unfold keyCharge
  split
  · exact bounded _ _
  · exact zero_le

/-- A charge that ignores the history before the occurrence charges every key the
error of its last event. -/
theorem keyCharge_const : keyCharge (fun _ event => error event) = keyError error := by
  funext key
  unfold keyCharge keyError
  cases key.getLast? <;> rfl

/-- The queries on every path from the absorbed `history` charge at most `cost`
in total, each query the charge of its key: the history before it and its
occurrence. A receive continues only with the reply its absorbed event
recovers, so only those replies are constrained. -/
def ChargedCostBound (charge : List E → E → ENNReal) :
    PIR.Process I A → List E → ENNReal → Prop
  | .done _, _, _ => True
  | .halt _, _, _ => True
  | .call operation next, history, cost =>
      match absorb operation with
      | .receive event recover => ∀ message value, recover (event message) = some value →
          ChargedCostBound charge (next value) (history ++ [event message]) cost
      | .send event value => ChargedCostBound charge (next value) (history ++ [event]) cost
      | .query event _ => ∃ remaining, charge history event + remaining ≤ cost ∧
          ∀ value, ChargedCostBound charge (next value) (history ++ [event]) remaining
      | .refuse => True

/-- A cost bound with an error per occurrence is a charged cost bound, from any
history, for the charge that ignores the history. -/
theorem CostBound.charged :
    ∀ (process : PIR.Process I A) (cost : ENNReal), CostBound absorb error process cost →
      ∀ history, ChargedCostBound absorb (fun _ event => error event) process history cost
  | .done _, _, _, _ => trivial
  | .halt _, _, _, _ => trivial
  | .call operation next, cost, bounded, history => by
      rcases absorbed : absorb operation with ⟨event, recover⟩ | ⟨event, value⟩ |
        ⟨event, decode⟩ | _
      · simp only [CostBound, absorbed] at bounded
        simp only [ChargedCostBound, absorbed]
        exact fun message value _ => CostBound.charged (next value) cost (bounded value) _
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
    ∀ (process : PIR.Process I A) (budget : ℕ), QueryBound absorb process budget →
      ∀ history, ChargedCostBound absorb charge process history (budget * bound)
  | .done _, _, _, _ => trivial
  | .halt _, _, _, _ => trivial
  | .call operation next, budget, counted, history => by
      rcases absorbed : absorb operation with ⟨event, recover⟩ | ⟨event, value⟩ |
        ⟨event, decode⟩ | _
      · simp only [QueryBound, absorbed] at counted
        simp only [ChargedCostBound, absorbed]
        exact fun message value _ =>
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

variable [ReadsByOccurrence R Raw]

/-- A query of the transform asks the history oracle once, at the history ending
with the occurrence. -/
theorem ask_bind {β : Type} (preceding : List E) (event : E)
    (continuation : Raw event → OracleComp (OracleSpec.ofFn R) β) :
    ask preceding event >>= continuation =
      answer (preceding ++ [event]) >>= fun raw =>
        continuation (ReadsByOccurrence.read preceding event raw) := by
  simp only [ask, bind_map_left]

/-- The transform makes at most the validator's cost on every path, each query
charged the error of its key. -/
theorem transform_costBound :
    ∀ (process : PIR.Process I A) (cost : ENNReal) (history : List E) (proof : List P),
      CostBound absorb error process cost →
        WorstCaseCostBound (transform absorb (ask (R := R)) process history proof)
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
            rw [Zkc.Transcript.transform_receive_nil absorb _ absorbed]
            exact (worstCaseCostBound_pure _ _ _).mpr zero_le
        | cons message rest =>
            rw [Zkc.Transcript.transform_receive absorb _ absorbed]
            cases recover (event message) with
            | none => exact (worstCaseCostBound_pure _ _ _).mpr zero_le
            | some value => exact ih value cost _ rest (bounded value)
      · simp only [CostBound, absorbed] at bounded
        rw [Zkc.Transcript.transform_send absorb _ absorbed]
        exact ih value cost _ proof bounded
      · simp only [CostBound, absorbed] at bounded
        obtain ⟨remaining, charged, rest⟩ := bounded
        rw [Zkc.Transcript.transform_query absorb _ absorbed, ask_bind, answer,
          worstCaseCostBound_query_bind_iff]
        intro raw total member
        have tail : Multiplicative.toAdd total.2 ≤ remaining := by
          revert member
          cases decode (ReadsByOccurrence.read history event raw) with
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
      · rw [Zkc.Transcript.transform_refuse absorb _ absorbed]
        exact (worstCaseCostBound_pure _ _ _).mpr zero_le

/-- The transform charges at most the validator's charged cost on every path,
each query charged `keyCharge charge` at its key. -/
theorem transform_chargedCostBound (charge : List E → E → ENNReal) :
    ∀ (process : PIR.Process I A) (cost : ENNReal) (history : List E) (proof : List P),
      ChargedCostBound absorb charge process history cost →
        WorstCaseCostBound (transform absorb (ask (R := R)) process history proof)
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
            rw [Zkc.Transcript.transform_receive_nil absorb _ absorbed]
            exact (worstCaseCostBound_pure _ _ _).mpr zero_le
        | cons message rest =>
            rw [Zkc.Transcript.transform_receive absorb _ absorbed]
            cases recovered : recover (event message) with
            | none => exact (worstCaseCostBound_pure _ _ _).mpr zero_le
            | some value => exact ih value cost _ rest (bounded message value recovered)
      · simp only [ChargedCostBound, absorbed] at bounded
        rw [Zkc.Transcript.transform_send absorb _ absorbed]
        exact ih value cost _ proof bounded
      · simp only [ChargedCostBound, absorbed] at bounded
        obtain ⟨remaining, charged, rest⟩ := bounded
        rw [Zkc.Transcript.transform_query absorb _ absorbed, ask_bind, answer,
          worstCaseCostBound_query_bind_iff]
        intro raw total member
        have tail : Multiplicative.toAdd total.2 ≤ remaining := by
          revert member
          cases decode (ReadsByOccurrence.read history event raw) with
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
      · rw [Zkc.Transcript.transform_refuse absorb _ absorbed]
        exact (worstCaseCostBound_pure _ _ _).mpr zero_le

/-- The transform makes at most the validator's query count on every path. -/
theorem transform_queryBound :
    ∀ (process : PIR.Process I A) (budget : ℕ) (history : List E) (proof : List P),
      QueryBound absorb process budget →
        IsTotalQueryBound (transform absorb (ask (R := R)) process history proof) budget := by
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
            rw [Zkc.Transcript.transform_receive_nil absorb _ absorbed]
            trivial
        | cons message rest =>
            rw [Zkc.Transcript.transform_receive absorb _ absorbed]
            cases recover (event message) with
            | none => trivial
            | some value => exact ih value budget _ rest (bounded value)
      · simp only [QueryBound, absorbed] at bounded
        rw [Zkc.Transcript.transform_send absorb _ absorbed]
        exact ih value budget _ proof bounded
      · simp only [QueryBound, absorbed] at bounded
        rw [Zkc.Transcript.transform_query absorb _ absorbed, ask_bind, answer]
        refine isTotalQueryBound_query_bind_iff.mpr ⟨bounded.1, fun raw => ?_⟩
        cases decode (ReadsByOccurrence.read history event raw) with
        | none => trivial
        | some value => exact ih value _ _ _ (bounded.2 value)
      · rw [Zkc.Transcript.transform_refuse absorb _ absorbed]
        trivial

end Bounds

section Execution
variable [ReadsByOccurrence R Raw]

theorem tableQueryLog_map {α β : Type} (f : α → β)
    (computation : OracleComp (OracleSpec.ofFn R) α) (table : (key : List E) → R key) :
    tableQueryLog (f <$> computation) table = tableQueryLog computation table := by
  rw [map_eq_bind_pure_comp, tableQueryLog_bind]
  simp

/-- Deterministic evaluation of the oracle transform against a total table is
the transform with the table, read by occurrence, as challenge function. -/
theorem evalWithAnswerFn_transform (absorb : Interface I E P Raw)
    (table : (key : List E) → R key) :
    ∀ (process : PIR.Process I A) (history : List E) (proof : List P),
      evalWithAnswerFn (QueryImpl.ofFn table) (transform absorb (ask (R := R)) process history proof) =
        transform (m := Id) absorb (readTable (Raw := Raw) table) process history proof := by
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
            rw [Zkc.Transcript.transform_receive_nil absorb _ absorbed,
              Zkc.Transcript.transform_receive_nil absorb _ absorbed]
            rfl
        | cons message rest =>
            rw [Zkc.Transcript.transform_receive absorb _ absorbed,
              Zkc.Transcript.transform_receive absorb _ absorbed]
            cases recover (event message) with
            | none => rfl
            | some value => exact ih value _ _
      · rw [Zkc.Transcript.transform_send absorb _ absorbed,
          Zkc.Transcript.transform_send absorb _ absorbed]
        exact ih value _ _
      · rw [Zkc.Transcript.transform_query absorb _ absorbed,
          Zkc.Transcript.transform_query absorb _ absorbed, ask_bind, answer,
          evalWithAnswerFn_bind, evalWithAnswerFn_liftM_query, QueryImpl.ofFn_apply]
        change _ = (match decode (ReadsByOccurrence.read history event (table (history ++ [event]))) with
          | some value => transform (m := Id) absorb (readTable (Raw := Raw) table) (next value)
              (history ++ [event]) proof
          | none => pure (.stopped .exhausted, proof))
        cases decode (ReadsByOccurrence.read history event (table (history ++ [event]))) with
        | none => rfl
        | some value => exact ih value _ _
      · rw [Zkc.Transcript.transform_refuse absorb _ absorbed,
          Zkc.Transcript.transform_refuse absorb _ absorbed]
        rfl

end Execution

end Typed

end ZkcSecurity.FiatShamir
