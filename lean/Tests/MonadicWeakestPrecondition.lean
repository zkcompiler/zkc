module

public import Zkc.Source.RegionReturnSpecification
public meta import Std.Tactic.Do

@[expose] public section

set_option autoImplicit false
set_option experimental.vcgen true
namespace Tests.MonadicWeakestPrecondition
open PIR Std.WP Lean.Order PIR.WeakestPrecondition

abbrev interface : Signature := ⟨Unit, fun _ ↦ Nat⟩
def read : Process interface Nat := .call () .done
def handler {M : Type → Type} [Monad M] : MonadHandler M interface Nat Nat :=
  fun _ state ↦ pure ⟨.returned state, state + 1, [state]⟩

variable {M : Type → Type} [Monad M] [LawfulMonad M]
theorem read_spec (state : Nat) (events : List Nat) :
    (letI := wpMonadM (handler (M := M))
     Triple read (fun current preceding ↦ current = state ∧ preceding = events)
       (fun value current reached ↦ value = state ∧ current = state + 1 ∧ reached = events ++ [state])
       estack⟨fun _ _ _ ↦ False⟩) := by
  apply (tripleM_iff_run _ _ _ _ _).mpr
  intro current preceding ⟨rfl, rfl⟩
  simp only [read, Process.runM, handler, pure_bind, Execution.followM, List.append_nil]
  exact Zkc.MonadicPostcondition.pure _ _ ⟨rfl, rfl, rfl⟩

def guarded (limit : Nat) : Process interface Nat := do
  let value ← read
  if value < limit then return value + 1 else .halt .reject

theorem guarded_spec (limit state : Nat) (events : List Nat) :
    (letI := wpMonadM (handler (M := M))
     Triple (guarded limit) (fun current preceding ↦ current = state ∧ preceding = events)
       (fun value current reached ↦ value = state + 1 ∧ state < limit ∧
         current = state + 1 ∧ reached = events ++ [state])
       estack⟨fun reason current reached ↦ reason = .reject ∧ ¬ state < limit ∧
         current = state + 1 ∧ reached = events ++ [state]⟩) := by
  letI := wpMonadM (handler (M := M))
  vcgen [guarded, read_spec (M := M), haltM_spec] with finish

/-- A new component adds a second call and data dependence. Its proof uses the
same local specifications without spelling the execution traversal. -/
def paired (limit : Nat) : Process interface (Nat × Nat) := do
  let first ← guarded limit
  let second ← read
  return (first, second)

theorem paired_spec (limit state : Nat) (events : List Nat) :
    (letI := wpMonadM (handler (M := M))
     Triple (paired limit) (fun current preceding ↦ current = state ∧ preceding = events)
       (fun value current reached ↦ value = (state + 1, state + 1) ∧ state < limit ∧
         current = state + 2 ∧ reached = events ++ [state, state + 1])
       estack⟨fun reason current reached ↦ reason = .reject ∧ ¬ state < limit ∧
         current = state + 1 ∧ reached = events ++ [state]⟩) := by
  letI := wpMonadM (handler (M := M))
  vcgen [paired, guarded_spec (M := M), read_spec (M := M)] with finish

#print axioms guarded_spec
#print axioms paired_spec

theorem arbitrary_handler {I : Signature} {S E A : Type}
    (selected : MonadHandler M I S E) (process : Process I A) (value : A)
    (invariant : S → Prop) (law : Process.ReturnsUnder selected invariant process value) :
    (letI := wpMonadM selected
     Triple (process.bind fun returned ↦ Process.done (returned, returned))
       (fun state _ ↦ invariant state)
       (fun result state _ ↦ invariant state ∧ result = (value, value))
       estack⟨fun _ state _ ↦ invariant state⟩) := by
  letI := wpMonadM selected
  vcgen [bindM_spec, doneM_spec, law.tripleM] with finish

/-- Rejection is not successful completion, and it does not perform the read
after the guarded component. These are semantic refusals, not tactic timeouts. -/
theorem rejecting_pair :
    (paired 0).runM (handler (M := Id)) 3 = ⟨.stopped .reject, 4, [3]⟩ := by
  rfl

theorem rejects_success_only :
    ¬ runMWP (handler (M := Id)) (paired 0)
      (fun _ _ _ ↦ True) estack⟨fun _ _ _ ↦ False⟩ 3 [] := by
  rw [runMWP_id_iff, rejecting_pair]
  exact id

theorem rejects_uncharged_stop :
    ¬ runMWP (handler (M := Id)) (paired 0)
      (fun _ _ _ ↦ True) estack⟨fun _ state _ ↦ state = 3⟩ 3 [] := by
  rw [runMWP_id_iff, rejecting_pair]
  simp only [satisfies, Nat.reduceEqDiff, not_false_eq_true]

theorem rejects_extra_read :
    ¬ runMWP (handler (M := Id)) (paired 0)
      (fun _ _ _ ↦ True) estack⟨fun _ _ events ↦ events = [3, 4]⟩ 3 [] := by
  rw [runMWP_id_iff, rejecting_pair]
  simp [satisfies]

#print axioms arbitrary_handler
#print axioms rejects_success_only
#print axioms rejects_uncharged_stop
#print axioms rejects_extra_read

end Tests.MonadicWeakestPrecondition
