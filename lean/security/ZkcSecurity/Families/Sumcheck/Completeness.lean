module

public import ZkcSecurity.Families.Sumcheck.Process

@[expose] public section

/-! Intermediate honest execution of the same open component. These laws refer
to an actual handler and preserve its complete state and observations. A root
compiled producer, pair association, coins/ROM coupling and failure-probability
theorem are additional obligations. No stopping process proves this result. -/

set_option autoImplicit false
namespace ZkcSecurity.Families.Sumcheck

variable {F : Type} [Field F] {I : PIR.Signature} {Context : Type}
  {State : Nat → Type} {message : Message F} {reference : Reference F}
  {H O : Type} {program : Program I Context State message}

/-- Delivered-message equality is separate from reference admissibility and
from the arbitrary-message consumer. `ready` is justified by actual delivery. -/
def HonestMessageLaw (representation : Representation program reference)
    (ready : Nat → {n : Nat} → Context → State (n + 1) → message.Carrier → H → Prop) : Prop :=
  ∀ count {n} (context : Context) (s : State (n + 1)) m h, ready count context s m h →
    message.polynomial m = reference.polynomial (representation.state s)

/-- Only reached sites need delivery/resource laws. The query law retains the
actual query and delivery executions, threading coins/cache/private state. -/
structure HonestRunLaws (program : Program I Context State message)
    (handler : PIR.Handler I H O)
    (invariant : Nat → {n : Nat} → Context → State n → H → Prop)
    (ready : Nat → {n : Nat} → Context → State (n + 1) → message.Carrier → H → Prop) : Prop where
  receive : ∀ count {n} (context : Context) (s : State (n + 1)) h, invariant (count + 1) context s h →
    ∃ m next events,
      (program.receive context s).run handler h = ⟨.returned (some m), next, events⟩ ∧
      ready count context s m next
  query : ∀ count {n} (context : Context) (s : State (n + 1)) m h, ready count context s m h →
    ∃ reply queried queryEvents next deliveryEvents,
      handler (program.query context s m) h = ⟨.returned reply, queried, queryEvents⟩ ∧
      (program.deliver context s m (program.challenge context s m reply)).run handler queried =
        ⟨.returned (), next, deliveryEvents⟩ ∧
      invariant count context (program.advance context s m (program.challenge context s m reply)) next

namespace Consumers

/-- Exact successful execution with full returned data, poststate and events.
The remaining dimension can be nonzero. Neither zero nor partial rounds ask
for delivery at sites that the component never executes. -/
theorem honest_run [DecidableEq F]
    (representation : Representation program reference)
    {messageDegree referenceDegree : Nat}
    (messageLaws : MessageLaws message messageDegree)
    (referenceLaws : ReferenceLaws reference referenceDegree)
    (handler : PIR.Handler I H O)
    (invariant : Nat → {n : Nat} → Context → State n → H → Prop)
    (ready : Nat → {n : Nat} → Context → State (n + 1) → message.Carrier → H → Prop)
    (execution : HonestRunLaws program handler invariant ready)
    (honestMessage : HonestMessageLaw representation ready)
    {n : Nat} (count : Nat) (context : Context) (s : State (n + count)) (h : H)
    (yes : representation.Yes s) (initial : invariant count context s h) :
    ∃ result final events,
      (program.remaining count context s).run handler h = ⟨.returned result, final, events⟩ ∧
      representation.Yes result ∧ invariant 0 context result final := by
  induction count generalizing h with
  | zero => exact ⟨s, h, [], rfl, yes, initial⟩
  | succ count ih =>
      obtain ⟨m, received, receiveEvents, receivedEq, delivered⟩ := execution.receive count context s h initial
      obtain ⟨reply, queried, queryEvents, advanced, deliveryEvents, queryEq, deliveryEq, nextInv⟩ :=
        execution.query count context s m received delivered
      have honest := honest_round referenceLaws messageLaws (representation.state s) yes.1 m
        (honestMessage count context s m received delivered)
        (program.challenge context s m reply) (program.challenge context s m reply) rfl
      have checked : message.boundary m = program.claim s := honest.1.trans yes.2.symm
      have nextYes : representation.Yes
          (program.advance context s m (program.challenge context s m reply)) := by
        constructor
        · exact representation.advance_allowed referenceLaws context s yes.1 m _
        · rw [representation.claim, representation.advance]
          exact honest.2.1
      obtain ⟨result, final, tailEvents, tailEq, resultYes, resultInv⟩ :=
        ih _ advanced nextYes nextInv
      refine ⟨result, final, receiveEvents ++ (queryEvents ++ (deliveryEvents ++ tailEvents)),
        ?_, resultYes, resultInv⟩
      rw [Program.remaining, PIR.run_bind, receivedEq]
      simp only [PIR.Execution.follow, ite_eq_left checked]
      rw [PIR.Process.run, queryEq]
      simp only [PIR.Execution.follow]
      rw [PIR.run_bind, deliveryEq]
      simp only [PIR.Execution.follow, tailEq]

/-- The binding argument is exactly the equation used by `boundResidual`.
No outcome-only correspondence or changed producer is introduced. -/
theorem bound_honest_run [DecidableEq F]
    (representation : Representation program reference)
    {messageDegree referenceDegree : Nat}
    (messageLaws : MessageLaws message messageDegree)
    (referenceLaws : ReferenceLaws reference referenceDegree)
    (handler : PIR.Handler I H O)
    (invariant : Nat → {n : Nat} → Context → State n → H → Prop)
    (ready : Nat → {n : Nat} → Context → State (n + 1) → message.Carrier → H → Prop)
    (execution : HonestRunLaws program handler invariant ready)
    (honestMessage : HonestMessageLaw representation ready)
    {n : Nat} (count : Nat) (context : Context) (s : State (n + count)) (h : H)
    (actual : PIR.Process I (State n)) (binding : actual = program.remaining count context s)
    (yes : representation.Yes s) (initial : invariant count context s h) :
    ∃ result final events,
      actual.run handler h = ⟨.returned result, final, events⟩ ∧
      representation.Yes result ∧ invariant 0 context result final := by
  rw [binding]
  exact honest_run representation messageLaws referenceLaws handler invariant ready execution
    honestMessage count context s h yes initial

end Consumers
end ZkcSecurity.Families.Sumcheck
