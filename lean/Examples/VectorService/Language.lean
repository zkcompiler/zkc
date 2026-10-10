import Zkc.Compiler.Checking
import Zkc.Source.InputBinding

/-! A consumer language with two heterogeneous external operations. The source
sort is a vector, while the interpreted interface reply has the requested length.
The finite service policy refuses requests above 1024 entries before any call.
This example tests representation boundaries; it makes no cryptographic claim. -/

set_option autoImplicit false
namespace VectorService
open Zkc.Source

inductive Ty where | count | vector | predicate deriving DecidableEq, Repr
abbrev Value : Ty → Type
  | .count => Nat
  | .vector => List (Fin 7)
  | .predicate => Bool
inductive Op where | request | send | requestAndSend | sum deriving DecidableEq, Repr
def arguments : Op → List Ty
  | .request | .send | .requestAndSend => [.count]
  | .sum => [.vector]
def result : Op → Ty
  | .request => .vector
  | .send | .requestAndSend => .predicate
  | .sum => .count
abbrev language : Language := ⟨Ty, Op, arguments, result, .predicate⟩

inductive Request where
  | vector (count : Nat)
  | send (count : Nat)
abbrev Reply : Request → Type
  | .vector n => { xs : List (Fin 7) // xs.length = n }
  | .send n => { b : Bool // b = decide (n = 0) }
abbrev interface : PIR.Signature := ⟨Request, Reply⟩
abbrev meaning : Interpretation language interface where
  Value := Value
  condition := id
  operation
    | .request, .cons n .nil =>
      if n ≤ 1024 then .call (.vector n) (fun xs => .done xs.val)
      else .halt .refused
    | .send, .cons n .nil => .call (.send n) (fun b => .done b.val)
    | .sum, .cons xs .nil => .done (xs.map Fin.val).sum
    | .requestAndSend, .cons n .nil =>
      if n ≤ 1024 then
        .call (.vector n) (fun xs =>
          .call (.send (xs.val.map Fin.val).sum) (fun b => .done b.val))
      else .halt .refused

structure State where
  calls : Nat := 0
  tape : List (Fin 7) := []
inductive Event where
  | requested (count : Nat)
  | sent (count : Nat)
  deriving DecidableEq, Repr
def event : Request → Event
  | .vector n => .requested n
  | .send n => .sent n
def response : (r : Request) → Fin 7 → Reply r
  | .vector n, seed => ⟨List.replicate n seed, by simp⟩
  | .send n, _ => ⟨decide (n = 0), rfl⟩
def handler : PIR.Handler interface State Event := fun r state =>
  let after := { state with calls := state.calls + 1 }
  match state.tape with
  | [] => ⟨.stopped .exhausted, after, [event r]⟩
  | seed :: rest => ⟨.returned (response r seed), { after with tape := rest }, [event r]⟩

/-- Exhaustion still retains the call's state update and observation. -/
theorem exhausted_call_retained (r : Request) (calls : Nat) :
    handler r ⟨calls, []⟩ = ⟨.stopped .exhausted, ⟨calls + 1, []⟩, [event r]⟩ := rfl

/-- A nonzero send returns false successfully; it does not reject execution. -/
theorem nonzero_send_returns (n calls : Nat) (seed : Fin 7) (rest : List (Fin 7)) :
    handler (.send (n + 1)) ⟨calls, seed :: rest⟩ =
      ⟨.returned ⟨false, by simp⟩, ⟨calls + 1, rest⟩, [.sent (n + 1)]⟩ := rfl

end VectorService
