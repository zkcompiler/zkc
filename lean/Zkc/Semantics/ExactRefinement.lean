module

public import Zkc.Semantics.Execution

@[expose] public section

/-! Exact implementation contracts for open processes.

The certificate preserves the entire effect tree, for arbitrary handlers,
including adversarial replies, stopped prefixes, successor state and events.
This is deliberately stronger than equality of an accepting projection.
It supplies no source admission, probability law, or cryptographic property.
-/
set_option autoImplicit false

namespace PIR

/-- Match an effect and leave its reply-dependent continuation as an obligation. -/
theorem Process.call_congr {I : Signature} {A : Type} {action : I.Op}
    {left right : I.Reply action → Process I A} (continuation : ∀ reply, left reply = right reply) :
    Process.call action left = Process.call action right :=
  congrArg (Process.call action) (funext continuation)

/-- Distribute a continuation without changing either stopping branch. -/
theorem Process.bind_ite {I : Signature} {A B : Type} (p : Prop) [Decidable p]
    (left right : Process I A) (next : A → Process I B) :
    (if p then left else right).bind next = if p then left.bind next else right.bind next := by
  split <;> rfl

structure ExactRefinement {I : Signature} {A : Type}
    (implementation specification : Process I A) : Prop where
  process_eq : implementation = specification

namespace ExactRefinement
variable {I : Signature} {A B S E : Type} {p q r : Process I A}

theorem refl (p : Process I A) : ExactRefinement p p := ⟨rfl⟩

theorem trans (first : ExactRefinement p q) (second : ExactRefinement q r) :
    ExactRefinement p r := ⟨first.process_eq.trans second.process_eq⟩

theorem run_eq (certificate : ExactRefinement p q) (handler : Handler I S E) (state : S) :
    p.run handler state = q.run handler state := by rw [certificate.process_eq]

theorem bind (certificate : ExactRefinement p q) (next : A → Process I B) :
    ExactRefinement (p.bind next) (q.bind next) :=
  ⟨congrArg (fun process => process.bind next) certificate.process_eq⟩

/-- Compose both implementation boundaries at the actual returned value.
Execution bind carries the successor state and preserves every stopped prefix. -/
theorem bind_congr (first : ExactRefinement p q) {left right : A → Process I B}
    (suffix : ∀ value, ExactRefinement (left value) (right value)) :
    ExactRefinement (p.bind left) (q.bind right) := by
  have next : left = right := funext (fun value => (suffix value).process_eq)
  exact ⟨by rw [first.process_eq, next]⟩

/-- A caller chooses the observation; the certificate does not erase events. -/
theorem observe {O : Type} (certificate : ExactRefinement p q)
    (handler : Handler I S E) (state : S) (view : Execution S E A → O) :
    view (p.run handler state) = view (q.run handler state) :=
  congrArg view (certificate.run_eq handler state)

end ExactRefinement
end PIR
