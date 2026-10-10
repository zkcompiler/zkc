import Zkc.Compiler.Storage

/-! Kernel-checked controls for the abstract storage law. No native decision oracle. -/
set_option autoImplicit false
namespace Tests.Storage
open Zkc.Compiler.Storage

abbrev Code := List (Instruction Nat Nat)

-- One real input read, a multi-output producer, a consumer, and an escaping output.
def scheduled : Code :=
  [.kernel 0 [0] [1, 2], .release [0, 1], .kernel 1 [2] [3], .release [2]]

theorem scheduled_safe : Safe scheduled [3] := by simp [scheduled, Safe, needed]

-- The client is quantified over effectful meanings and all initial logical states.
theorem arbitrary_effects {V S E F : Type} (semantics : Semantics Nat V Nat S E F)
    (left right : Environment Nat V) (sameInput : left 0 = right 0)
    (state : LogicalState S) :
    runScoped semantics scheduled [3] left state =
      runScoped semantics (eraseReleases scheduled) [3] right state := by
  apply runScoped_eraseReleases _ _ _ scheduled_safe
  intro name member
  have only : name = 0 := by simpa [scheduled, needed] using member
  subst name
  exact sameInput

-- A later definition discharges an old need; its own inputs are read first.
example : needed ([.kernel 0 [0] [0]] : Code) [0] = [0] := rfl
example : needed ([.kernel 0 [] [0]] : Code) [0] = [] := rfl
example : Safe ([.release [0], .kernel 0 [] [0]] : Code) [0] := by simp [Safe, needed]
example : ¬ Safe ([.release [0], .kernel 0 [0] [0]] : Code) [0] := by simp [Safe, needed]
example : ¬ Safe ([.release [0]] : Code) [0] := by simp [Safe, needed]

structure Counters where
  liveCount : Nat := 0
  liveBytes : Nat := 0
  totalBytes : Nat := 0
  ticks : Nat := 0
  mutations : Nat := 0
  deriving DecidableEq, Repr

structure Limits where
  liveCount : Nat := 4
  liveBytes : Nat := 12
  totalBytes : Nat := 12
  ticks : Nat := 3
  deriving Repr

inductive Event where
  | attempt (op budget : Nat) (inputs : List Nat)
  | completed (op : Nat)
  deriving DecidableEq, Repr

def available (limits : Limits) (state : Counters) : Nat :=
  min (limits.liveBytes - state.liveBytes) (limits.totalBytes - state.totalBytes)

/-- A mutating backend observes the logical budget, and may fail after mutation.
The first call returns two alias-sized values, each charged as a separate binding. -/
def semantics (limits : Limits := {}) (failAt : Option Nat := none) :
    Semantics Nat Nat Nat Counters Event String where
  tick state :=
    if state.ticks ≥ limits.ticks then .fail (.external "instructions") state
    else .pure () { state with ticks := state.ticks + 1 }
  kernel op inputs state :=
    let budget := available limits state
    let next := { state with mutations := state.mutations + 1 }
    let attempt := Event.attempt op budget inputs
    let values := if op = 0 then [3, 3] else if op = 2 then [] else [inputs.sum + 1]
    if failAt = some op then ⟨.error (.external "backend-mutated"), next, [attempt]⟩
    else if values.sum > budget then ⟨.error (.external "output-bytes"), next, [attempt]⟩
    else ⟨.ok values, next, [attempt, .completed op]⟩
  retain _ values state :=
    if state.liveCount + values.length > limits.liveCount ∨
        state.liveBytes + values.sum > limits.liveBytes ∨
        state.totalBytes + values.sum > limits.totalBytes then
      .fail (.external "retained-values") state
    else .pure () { state with
      liveCount := state.liveCount + values.length
      liveBytes := state.liveBytes + values.sum
      totalBytes := state.totalBytes + values.sum }
  bytes := id
  leave charges state := { state with
    liveCount := state.liveCount - charges.count
    liveBytes := state.liveBytes - charges.bytes }

def env : Environment Nat Nat := fun name => if name = 0 then some 2 else none

def initial : LogicalState Counters := ⟨⟨1, 2, 2, 0, 0⟩, ⟨1, 2⟩⟩

def result (limits : Limits := {}) (failAt : Option Nat := none) :=
  runScoped (semantics limits failAt) scheduled [3] env initial

-- Equality for every logical limit and either backend failure point.
theorem policies_preserved (limits : Limits) (failAt : Option Nat) :
    result limits failAt =
      runScoped (semantics limits failAt) (eraseReleases scheduled) [3] env initial :=
  arbitrary_effects _ _ _ rfl _

-- Physical erasure really changes the map, even though execution stays equal.
example : erase env [0] 0 = none ∧ env 0 = some 2 := by decide
example : (run (semantics {}) scheduled [3] env initial).state.ghost = ⟨4, 12⟩ := rfl
example : (result {}).outcome = .ok [4] := rfl
example : (result {}).state = ⟨⟨0, 0, 12, 3, 2⟩, ⟨0, 0⟩⟩ := rfl
example : (result {}).events =
    [.attempt 0 10 [2], .completed 0, .attempt 1 4 [3], .completed 1] := rfl

-- Successful outputs, all counters and the exact observed budgets agree.
example : result {} = runScoped (semantics {}) (eraseReleases scheduled) [3] env initial :=
  arbitrary_effects _ _ _ rfl _

-- A dead binding's charge still causes byte exhaustion; successful allocations
-- reach the ceiling exactly. The failing kernel's mutated state survives cleanup.
example : (result { liveBytes := 11 }).outcome = .error (.external "output-bytes") := rfl
example : (result { liveBytes := 11 }).state = ⟨⟨0, 0, 8, 2, 2⟩, ⟨0, 0⟩⟩ := rfl
example : (result { liveBytes := 11 }).events =
    [.attempt 0 9 [2], .completed 0, .attempt 1 3 [3]] := rfl
example : (result { totalBytes := 11 }).outcome = .error (.external "output-bytes") := rfl
example : (result { liveBytes := 13, totalBytes := 13 }).outcome = .ok [4] := rfl

-- Retention may fail after a completed backend call. No failed batch is added
-- to the ghost ledger, so exit refunds only the initial binding in this case.
example : (result { liveCount := 2 }).outcome = .error (.external "retained-values") := rfl
example : (result { liveCount := 2 }).state = ⟨⟨0, 0, 2, 1, 1⟩, ⟨0, 0⟩⟩ := rfl
example : (result { liveCount := 2 }).events = [.attempt 0 10 [2], .completed 0] := rfl

-- Backend failure keeps the precise error, post-state and failed-attempt event.
example : (result {} (some 1)).outcome = .error (.external "backend-mutated") := rfl
example : (result {} (some 1)).state = ⟨⟨0, 0, 8, 2, 2⟩, ⟨0, 0⟩⟩ := rfl
example : (result {} (some 1)).events =
    [.attempt 0 10 [2], .completed 0, .attempt 1 4 [3]] := rfl
example : (result {} (some 0)).state = ⟨⟨0, 0, 2, 1, 1⟩, ⟨0, 0⟩⟩ := rfl

-- The return ticks; releases never tick. A failed return tick retains prior work.
example : (result { ticks := 2 }).outcome = .error (.external "instructions") := rfl
example : (result { ticks := 2 }).state = ⟨⟨0, 0, 12, 2, 2⟩, ⟨0, 0⟩⟩ := rfl
example : (result { ticks := 0 }).state = ⟨⟨0, 0, 2, 0, 0⟩, ⟨0, 0⟩⟩ := rfl

-- Wrong result arity is caught before retention and also retains backend effects.
def wrongArity : Code := [.release [0], .kernel 2 [] [1]]
example : Safe wrongArity [1] := by simp [wrongArity, Safe, needed]
example : (runScoped (semantics {}) wrongArity [1] env initial).outcome = .error .arity := rfl
example : (runScoped (semantics {}) wrongArity [1] env initial).state =
    ⟨⟨0, 0, 2, 1, 1⟩, ⟨0, 0⟩⟩ := rfl

-- A missing live input agrees as absence on both sides, and is not manufactured.
example : (runScoped (semantics {}) scheduled [3] (fun _ => none) initial).outcome =
    .error (.missing 0) := rfl

-- Concrete counterexamples: dropping a live return or a future kernel operand
-- changes failure into success when erased. Unrestricted erasure is unsound.
def badReturn : Code := [.release [0]]
example : (runScoped (semantics {}) badReturn [0] env initial).outcome = .error (.missing 0) := rfl
example : (runScoped (semantics {}) (eraseReleases badReturn) [0] env initial).outcome = .ok [2] := rfl
example : (runScoped (semantics {}) badReturn [0] env initial).outcome ≠
    (runScoped (semantics {}) (eraseReleases badReturn) [0] env initial).outcome := by
  intro impossible
  cases impossible

def badRead : Code := [.release [0], .kernel 1 [0] [1]]
example : ¬ Safe badRead [1] := by simp [badRead, Safe, needed]
example : (runScoped (semantics {}) badRead [1] env initial).outcome = .error (.missing 0) := rfl
example : (runScoped (semantics {}) (eraseReleases badRead) [1] env initial).outcome = .ok [3] := rfl
example : (runScoped (semantics {}) badRead [1] env initial).state.core.mutations = 0 := rfl
example : (runScoped (semantics {}) (eraseReleases badRead) [1] env initial).state.core.mutations = 1 := rfl

end Tests.Storage
