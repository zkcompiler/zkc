module

public import ZkcSecurity.ProgramLogic.Transcript.Interface

@[expose] public section

/-! A hash-chain transcript over an abstract hash with full-digest states.

The chain realizes the transcript oracle on event histories with one hash `H`
whose outputs, the digests `S`, are the chain states, as in the
[native hash-chain suites](../../../../../docs/spec/ir/construction.md#native-hash-chain-suites).
Every primitive input begins with a role tag, so an input is one of:

- `bind e`: `H(t_bind ‖ enc e)`, the state after the one-event history `[e]`;
- `absorb s e`: `H(t_absorb ‖ s ‖ enc e)`, the state after absorbing `e` at
  state `s`;
- `request s e k`: `H(t_request ‖ s ‖ enc e ‖ k)`, counter block `k` of the
  answer to the request with occurrence `e` at state `s`;
- `other x`: any input of `H` that has none of these shapes, such as a call of
  the same primitive in another namespace.

`Input` is this classification; the byte encoding and its injectivity are in
`ZkcSecurity.HashChain.Encoding`. The state of a history is a function of the
chain inputs a cache answers (`chainState`): the first event is bound, and every
later event is absorbed at the state before it.

The validator runs over the typed transcript interface of
`ZkcSecurity.FiatShamir.Typed` with raw answers of `width` digests
(`Raw`). `chainTransform` runs it with the chain in any monad, given the hash
as a function: received and sent events are absorbed; a query occurrence is
answered by the counter blocks `0, …, width - 1` at the current state, after
which the occurrence is absorbed too, so consecutive requests have distinct
inputs. `chainRun` binds the first event of the initial history and absorbs the
rest before running the validator. `experiment` is the concrete experiment: the
adversary calls the primitive directly and outputs a statement and a proof,
then the statement's validator runs with the chain on the same primitive.
`simulateQ_chainRun` evaluates the oracle form under any implementation of the
primitive.
-/

set_option autoImplicit false

namespace ZkcSecurity.HashChain
open OracleComp OracleSpec ZkcSecurity.FiatShamir

/-- The primitive inputs of a hash chain by role: binding the first event,
absorbing an event at a state, one counter block of a request at a state, and
every other input of the hash. -/
inductive Input (E S X : Type) where
  | bind (event : E)
  | absorb (state : S) (event : E)
  | request (state : S) (event : E) (block : ℕ)
  | other (input : X)
  deriving DecidableEq

/-- The primitive: one hash from inputs to digests. -/
abbrev Primitive (E S X : Type) : OracleSpec (Input E S X) :=
  OracleSpec.ofFn fun _ : Input E S X => S

/-- The raw answer of every query occurrence: `width` digests. -/
abbrev Raw (E S : Type) (width : ℕ) : E → Type := fun _ => Fin width → S

/-- The ideal history oracle's answer at every history key: `width` digests. -/
abbrev Answer (E S : Type) (width : ℕ) : List E → Type := fun _ => Fin width → S

variable {E S X : Type}

/-- The state an input reads, if any. -/
def Input.state? : Input E S X → Option S
  | .absorb state _ => some state
  | .request state _ _ => some state
  | _ => none

section Chain

/-- The state reached from `state` by absorbing `events`, when the cache answers
every step. -/
def chainFrom (cache : Input E S X → Option S) : S → List E → Option S
  | state, [] => some state
  | state, event :: rest => (cache (.absorb state event)).bind fun next => chainFrom cache next rest

/-- The state of a nonempty history in a cache: the first event is bound and
every later event is absorbed. The empty history has no state. -/
def chainState (cache : Input E S X → Option S) : List E → Option S
  | [] => none
  | event :: rest => (cache (.bind event)).bind fun state => chainFrom cache state rest

variable (cache : Input E S X → Option S)

theorem chainFrom_append (first second : List E) :
    ∀ state : S, chainFrom cache state (first ++ second) =
      (chainFrom cache state first).bind fun next => chainFrom cache next second := by
  induction first with
  | nil => intro state; rfl
  | cons event rest ih =>
      intro state
      simp only [List.cons_append, chainFrom]
      cases cache (.absorb state event) with
      | none => rfl
      | some next => exact ih next

@[simp] theorem chainState_nil : chainState cache ([] : List E) = none := rfl

@[simp] theorem chainState_singleton (event : E) :
    chainState cache [event] = cache (.bind event) := by
  simp only [chainState, chainFrom]
  cases cache (.bind event) <;> rfl

/-- The state after a nonempty history and one more event absorbs that event at
the history's state. -/
theorem chainState_append_singleton {history : List E} (nonempty : history ≠ []) (event : E) :
    chainState cache (history ++ [event]) =
      (chainState cache history).bind fun state => cache (.absorb state event) := by
  obtain ⟨first, rest, rfl⟩ := List.exists_cons_of_ne_nil nonempty
  simp only [List.cons_append, chainState]
  cases cache (.bind first) with
  | none => rfl
  | some state =>
      simp only [Option.bind_some, chainFrom_append]
      cases chainFrom cache state rest with
      | none => rfl
      | some next =>
          simp only [Option.bind_some, chainFrom]
          cases cache (.absorb next event) <;> rfl

/-- A history with a state is nonempty. -/
theorem ne_nil_of_chainState {history : List E} {state : S}
    (reached : chainState cache history = some state) : history ≠ [] := by
  rintro rfl
  simp at reached

/-- Two caches that agree on binding and absorbing inputs give every history the
same state. -/
theorem chainState_congr {other : Input E S X → Option S}
    (agree : ∀ event, cache (.bind event) = other (.bind event))
    (agreeAbsorb : ∀ state event, cache (.absorb state event) = other (.absorb state event)) :
    ∀ history : List E, chainState cache history = chainState other history := by
  have fromAgree : ∀ (events : List E) (state : S),
      chainFrom cache state events = chainFrom other state events := by
    intro events
    induction events with
    | nil => intro state; rfl
    | cons event rest ih =>
        intro state
        simp only [chainFrom, agreeAbsorb, ih]
  intro history
  cases history with
  | nil => rfl
  | cons event rest => simp only [chainState, agree, fromAgree]

end Chain

section Transform
variable {I : PIR.Signature} {P A : Type} {width : ℕ} {m : Type → Type} [Monad m]

/-- The answers of `count` calls in index order. -/
def collect : (count : ℕ) → (Fin count → m S) → m (Fin count → S)
  | 0, _ => pure Fin.elim0
  | count + 1, call => do
      let head ← call 0
      let tail ← collect count fun index => call index.succ
      pure (Fin.cons head tail)

/-- The validator run with the chain: absorbed events advance the state with one
`absorb` call each; a query occurrence is answered by the counter blocks at the
current state, its occurrence is then absorbed, and the site decodes the blocks. -/
def chainTransform (absorb : Typed.Interface I E P (Raw E S width)) (hash : Input E S X → m S) :
    PIR.Process I A → S → List E → List P → m (PIR.Outcome A × List P)
  | .done value, _, _, proof => pure (.returned value, proof)
  | .halt stop, _, _, proof => pure (.stopped stop, proof)
  | .call operation next, state, history, proof =>
      match absorb operation with
      | .receive event recover =>
          match proof with
          | [] => pure (.stopped .refused, [])
          | message :: rest =>
              match recover (event message) with
              | some value => do
                  let advanced ← hash (.absorb state (event message))
                  chainTransform absorb hash (next value) advanced (history ++ [event message]) rest
              | none => pure (.stopped .refused, message :: rest)
      | .send event value => do
          let advanced ← hash (.absorb state event)
          chainTransform absorb hash (next value) advanced (history ++ [event]) proof
      | .query event decode => do
          let raw ← collect width fun block => hash (.request state event block.val)
          let advanced ← hash (.absorb state event)
          match decode raw with
          | some value => chainTransform absorb hash (next value) advanced (history ++ [event]) proof
          | none => pure (.stopped .exhausted, proof)
      | .refuse => pure (.stopped .refused, proof)

/-- Absorb `events` from `state`, one `absorb` call each. -/
def absorbAll (hash : Input E S X → m S) : S → List E → m S
  | state, [] => pure state
  | state, event :: rest => do
      let next ← hash (.absorb state event)
      absorbAll hash next rest

/-- Bind the first event of the initial history, absorb the rest and run the
validator from the resulting state. An empty initial history binds nothing and
refuses. -/
def chainRun (absorb : Typed.Interface I E P (Raw E S width)) (hash : Input E S X → m S)
    (validator : PIR.Process I A) (initial : List E) (proof : List P) :
    m (PIR.Outcome A × List P) :=
  match initial with
  | [] => pure (.stopped .refused, proof)
  | event :: rest => do
      let state ← hash (.bind event)
      let state ← absorbAll hash state rest
      chainTransform absorb hash validator state (event :: rest) proof

end Transform

section Experiment
variable {I : PIR.Signature} {P A Stmt : Type} {width : ℕ}

/-- One call of the primitive. -/
def call (input : Input E S X) : OracleComp (Primitive E S X) S :=
  liftM ((Primitive E S X).query input)

/-- The concrete experiment: the adversary calls the primitive and outputs a
statement and a proof; the statement's validator then runs with the chain on the
same primitive, from the statement's initial history. -/
def experiment (absorb : Typed.Interface I E P (Raw E S width)) (validator : Stmt → PIR.Process I A)
    (initial : Stmt → List E) (adversary : OracleComp (Primitive E S X) (Stmt × List P)) :
    OracleComp (Primitive E S X) (Stmt × (PIR.Outcome A × List P)) :=
  adversary >>= fun claimed => (fun result => (claimed.1, result)) <$>
    chainRun absorb call (validator claimed.1) (initial claimed.1) claimed.2

variable {n : Type → Type} [Monad n] [LawfulMonad n] (impl : QueryImpl (Primitive E S X) n)

theorem simulateQ_collect :
    ∀ (count : ℕ) (calls : Fin count → Input E S X),
      simulateQ impl (collect count fun index => call (calls index)) =
        collect count fun index => impl (calls index)
  | 0, _ => by simp [collect]
  | count + 1, calls => by
      have tail := simulateQ_collect count fun index => calls index.succ
      simp only [call] at tail
      simp only [collect, simulateQ_bind, simulateQ_pure, call, simulateQ_spec_query, tail]

theorem simulateQ_chainTransform (absorb : Typed.Interface I E P (Raw E S width)) :
    ∀ (process : PIR.Process I A) (state : S) (history : List E) (proof : List P),
      simulateQ impl (chainTransform absorb call process state history proof) =
        chainTransform absorb (fun input => impl input) process state history proof := by
  intro process
  induction process with
  | done value => intro state history proof; simp [chainTransform]
  | halt stop => intro state history proof; simp [chainTransform]
  | call operation next ih =>
      intro state history proof
      rcases absorbed : absorb operation with ⟨event, recover⟩ | ⟨event, value⟩ |
        ⟨event, decode⟩ | _
      · cases proof with
        | nil => simp [chainTransform, absorbed]
        | cons message rest =>
            simp only [chainTransform, absorbed]
            cases recover (event message) with
            | none => simp
            | some value =>
                simp only [simulateQ_bind, call, simulateQ_spec_query]
                exact bind_congr fun advanced => ih value _ _ _
      · simp only [chainTransform, absorbed, simulateQ_bind, call, simulateQ_spec_query]
        exact bind_congr fun advanced => ih value _ _ _
      · simp only [chainTransform, absorbed, simulateQ_bind]
        rw [simulateQ_collect impl width fun block => .request state event block.val]
        refine bind_congr fun raw => ?_
        simp only [call, simulateQ_spec_query]
        refine bind_congr fun advanced => ?_
        cases decode raw with
        | none => simp
        | some value => exact ih value _ _ _
      · simp [chainTransform, absorbed]

theorem simulateQ_absorbAll :
    ∀ (events : List E) (state : S),
      simulateQ impl (absorbAll call state events) = absorbAll (fun input => impl input) state events
  | [], state => by simp [absorbAll]
  | event :: rest, state => by
      simp only [absorbAll, simulateQ_bind, call, simulateQ_spec_query]
      exact bind_congr fun next => simulateQ_absorbAll rest next

theorem simulateQ_chainRun (absorb : Typed.Interface I E P (Raw E S width))
    (validator : PIR.Process I A) (initial : List E) (proof : List P) :
    simulateQ impl (chainRun absorb call validator initial proof) =
      chainRun absorb (fun input => impl input) validator initial proof := by
  cases initial with
  | nil => simp [chainRun]
  | cons event rest =>
      simp only [chainRun, simulateQ_bind, call, simulateQ_spec_query]
      refine bind_congr fun state => ?_
      rw [simulateQ_absorbAll impl rest state]
      exact bind_congr fun state => simulateQ_chainTransform impl absorb validator state _ proof

end Experiment

end ZkcSecurity.HashChain
