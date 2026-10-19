module

public import ZkcSecurity.HashChain.Bound
public import ZkcSecurity.FiatShamir.ProviderSimulation

@[expose] public section

/-! The hash-chain simulator with a private tape and attempt accounting.

`chainSimulator width length` is a `ZkcSecurity.FiatShamir.Provider.Simulator`
for the primitive of a hash chain over the history oracle whose answer at a key
is `width` digests. Its state holds the private tape, the position of the next
unread tape entry, the private answers, the history recorded for each generated
state (the first one kept) and the ideal answers it has recorded.

- **Attempts.** The counter block `k < width` of a request with occurrence `e`
  at a state with recorded history `h` belongs to the attempt `h ++ [e]`, the
  TranscriptQuery whose answer the block is read from (`chainShared`). All
  counter blocks below the width of one request at one state make up one
  concrete attempt (`chainTogether`). A request at a state without a recorded
  history is answered privately; if its state is recorded later, the request
  then joins an attempt. In the concrete experiment this is the prediction
  event, charged to the simulation's loss.
- **Private answers.** Every other call is answered privately: a repeated call
  gets its earlier answer, a fresh call the next tape entry (`ChainState.respond`).
  A fresh binding answer, or a fresh absorbing answer at a state with a recorded
  history, records the history it reaches unless its state already has one
  (`noteReached`), so an assignment to an attempt never changes once made.
-/

set_option autoImplicit false

namespace ZkcSecurity.HashChain
open OracleComp OracleSpec ZkcSecurity.FiatShamir

variable {E S X : Type}

/-- The tape entry at a position, or the default digest past the end. -/
def tapeAt [Inhabited S] {length : ℕ} (tape : Fin length → S) (position : ℕ) : S :=
  if below : position < length then tape ⟨position, below⟩ else default

/-- The state of the hash-chain simulator. -/
structure ChainState (E S X : Type) (width length : ℕ) where
  tape : Fin length → S
  position : ℕ
  answers : Input E S X → Option S
  reached : S → Option (List E)
  recorded : List E → Option (Fin width → S)

/-- The attempt of a call: the counter blocks below the width of a request at a
state with a recorded history belong to that history extended by the request's
occurrence. -/
def chainAttempt (width : ℕ) (reached : S → Option (List E)) : Input E S X → Option (List E)
  | .request state event block =>
      if block < width then (reached state).map (fun history => history ++ [event]) else none
  | _ => none

/-- The reply to a call of an attempt: its counter block of the ideal answer. -/
def chainShared [Inhabited S] (width : ℕ) : Input E S X → (Fin width → S) → S
  | .request _ _ block, answer => if below : block < width then answer ⟨block, below⟩ else default
  | _, _ => default

/-- The counter blocks below the width of one request at one state. -/
def chainTogether (width : ℕ) : Input E S X → Input E S X → Prop
  | .request state event block, .request state' event' block' =>
      state = state' ∧ event = event' ∧ block < width ∧ block' < width
  | _, _ => False

variable [DecidableEq E] [DecidableEq S] [DecidableEq X] [Inhabited S]

/-- The private reply: a repeated call gets its earlier answer, a fresh call the
next tape entry, recording the history a generated state reaches. -/
def ChainState.respond {width length : ℕ} (state : ChainState E S X width length)
    (input : Input E S X) : S × ChainState E S X width length :=
  match state.answers input with
  | some answer => (answer, state)
  | none =>
      (tapeAt state.tape state.position,
        { state with
          position := state.position + 1
          answers := Function.update state.answers input (some (tapeAt state.tape state.position))
          reached := noteReached state.reached input (tapeAt state.tape state.position) })

omit [DecidableEq E] [DecidableEq X] [Inhabited S] in
/-- A recorded history is never replaced. -/
theorem noteReached_of_some {reached : S → Option (List E)} {state : S} {history : List E}
    (recorded : reached state = some history) (input : Input E S X) (answer : S) :
    noteReached reached input answer state = some history := by
  cases recordedAnswer : reached answer with
  | some _ => simp only [noteReached, recordedAnswer]; exact recorded
  | none =>
      have different : state ≠ answer := by
        rintro rfl
        rw [recorded] at recordedAnswer
        cases recordedAnswer
      cases input with
      | bind event =>
          simp only [noteReached, recordedAnswer]
          rw [Function.update_of_ne different]
          exact recorded
      | absorb state' event =>
          cases recordedState : reached state' with
          | none => simp only [noteReached, recordedAnswer, recordedState]; exact recorded
          | some _ =>
              simp only [noteReached, recordedAnswer, recordedState]
              rw [Function.update_of_ne different]
              exact recorded
      | request => simp only [noteReached, recordedAnswer]; exact recorded
      | other => simp only [noteReached, recordedAnswer]; exact recorded

omit [DecidableEq E] [DecidableEq X] [Inhabited S] in
/-- Assignments to attempts survive recording a history. -/
theorem chainAttempt_noteReached {width : ℕ} {reached : S → Option (List E)} {query : Input E S X}
    {key : List E} (assigned : chainAttempt width reached query = some key)
    (input : Input E S X) (answer : S) :
    chainAttempt width (noteReached reached input answer) query = some key := by
  cases query with
  | request state event block =>
      simp only [chainAttempt] at assigned ⊢
      by_cases below : block < width
      · simp only [below, ↓reduceIte] at assigned ⊢
        cases recorded : reached state with
        | none => simp [recorded] at assigned
        | some history =>
            simp only [recorded, Option.map_some] at assigned
            rw [noteReached_of_some recorded input answer]
            simpa using assigned
      · simp [below] at assigned
  | bind => cases assigned
  | absorb => cases assigned
  | other => cases assigned

/-- The hash-chain simulator over the history oracle with `width`-digest answers,
with a private tape of `length` digests. -/
@[reducible] def chainSimulator (width length : ℕ) :
    Provider.Simulator (Primitive E S X) (Answer E S width) (Fin length → S) where
  State := ChainState E S X width length
  start tape := ⟨tape, 0, fun _ => none, fun _ => none, fun _ => none⟩
  attempt state input := chainAttempt width state.reached input
  recorded state key := state.recorded key
  record state key answer := { state with recorded := Function.update state.recorded key (some answer) }
  shared input _ answer := chainShared width input answer
  respond state input := state.respond input
  together := chainTogether width
  recorded_start _ _ := rfl
  recorded_record _ _ _ := Function.update_self _ _ _
  recorded_record_of_ne _ _ _ _ different := Function.update_of_ne different _ _
  recorded_respond state input _ := by
    simp only [ChainState.respond]
    split <;> rfl
  attempt_record _ _ _ _ _ assigned := assigned
  attempt_respond state call query key assigned := by
    simp only [ChainState.respond]
    split
    · exact assigned
    · exact chainAttempt_noteReached assigned call _
  attempt_together state query other together := by
    cases query with
    | request state' event block =>
        cases other with
        | request state'' event' block' =>
            obtain ⟨rfl, rfl, below, below'⟩ := together
            simp only [chainAttempt, below, below', ↓reduceIte]
        | bind => exact together.elim
        | absorb => exact together.elim
        | other => exact together.elim
    | bind => exact together.elim
    | absorb => exact together.elim
    | other => exact together.elim

end ZkcSecurity.HashChain
