import Zkc.Transformations.Memoization
import Zkc.Semantics.Preparation.Emission

/-! The immutable memoization client embedded in canonical `PIR.Proc` execution.

The adapter reuses preparation's operation signature, without converting to a
second preparation tree or changing its cost interpreter. These handlers expose
exactly the client's emitted events; they add no cost events. Cache correctness
still requires validity relative to the fixed immutable provider.
-/

set_option autoImplicit false

namespace Zkc.Transformations.Memoization

open Modules.ImmutableCache

variable {K V E O : Type}

/-- Preserve value-dependent requests and explicit emits in the common process. -/
def Client.toProc : Client K V E O →
    PIR.Proc (PIR.Preparation.signature K V (PIR.Preparation.Emission.signature E)) O
  | .done value => .done value
  | .emit event tail => .call (.external event) (fun _ => tail.toProc)
  | .call key next => .call (.prepare key) (fun value => (next value).toProc)

def directHandler (provider : K → V) :
    PIR.Handler (PIR.Preparation.signature K V (PIR.Preparation.Emission.signature E)) Unit E
  | .prepare key, state => ⟨.returned (provider key), state, []⟩
  | .external event, state => ⟨.returned (), state, [event]⟩

def memoHandler [DecidableEq K] (provider : K → V) (store : Cache K V → K → Bool) :
    PIR.Handler (PIR.Preparation.signature K V (PIR.Preparation.Emission.signature E)) (Cache K V) E
  | .prepare key, cache =>
    let result := lookup provider store cache key
    ⟨.returned result.1, result.2, []⟩
  | .external event, cache => ⟨.returned (), cache, [event]⟩

/-- Exact value and ordered-event agreement with the immutable client evaluator. -/
theorem Client.run_toProc (provider : K → V) (client : Client K V E O) :
    client.toProc.run (directHandler provider) () =
      ⟨.returned (run provider client).2, (), (run provider client).1⟩ := by
  induction client with
  | done value => rfl
  | emit event tail ih =>
    simp only [toProc, PIR.Proc.run, directHandler, PIR.Execution.follow, ih, run,
      List.singleton_append]
  | call key next ih =>
    simpa only [toProc, PIR.Proc.run, directHandler, PIR.Execution.follow, List.nil_append,
      run] using ih (provider key)

/-- This execution equation also holds for invalid caches; it asserts agreement
with `runMemo`, not agreement with the provider in the absence of validity. -/
theorem Client.runMemo_toProc [DecidableEq K] (provider : K → V)
    (store : Cache K V → K → Bool) (client : Client K V E O) (cache : Cache K V) :
    client.toProc.run (memoHandler provider store) cache =
      ⟨.returned (runMemo provider store cache client).1.2,
        (runMemo provider store cache client).2, (runMemo provider store cache client).1.1⟩ := by
  induction client generalizing cache with
  | done value => rfl
  | emit event tail ih =>
    simp only [toProc, PIR.Proc.run, memoHandler, PIR.Execution.follow, ih, runMemo,
      List.singleton_append]
  | call key next ih =>
    simpa only [toProc, PIR.Proc.run, memoHandler, PIR.Execution.follow, List.nil_append,
      runMemo] using ih (lookup provider store cache key).1 (lookup provider store cache key).2

/-- A valid cache preserves the observable result and remains valid after the
canonical execution, for every storage policy and adaptive client. -/
theorem Client.toProc_preservation [DecidableEq K] (provider : K → V)
    (store : Cache K V → K → Bool) (client : Client K V E O) (cache : Cache K V)
    (valid : Valid provider cache) :
    let direct := client.toProc.run (directHandler provider) ()
    let memo := client.toProc.run (memoHandler provider store) cache
    memo.outcome = direct.outcome ∧ memo.events = direct.events ∧ Valid provider memo.state := by
  dsimp
  rw [run_toProc, runMemo_toProc]
  obtain ⟨same, valid⟩ := client_preservation provider store client cache valid
  exact ⟨congrArg (fun result => PIR.Outcome.returned result.2) same,
    congrArg Prod.fst same, valid⟩

end Zkc.Transformations.Memoization
