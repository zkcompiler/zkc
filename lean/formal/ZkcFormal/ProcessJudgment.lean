module

public import Zkc.Core.Process.Same
public import Zkc.Core.Meaning.Fold

@[expose] public section
set_option autoImplicit false

namespace Zkc.Core
variable {S : Sig} {H A B L : Type}

/-- How a property combines the possible continuations at one effect. -/
structure ProcessJudgment (S : Sig) (L : Type) where
  node : (op : S.Op) → (S.Reply op → L) → L

def Process.interpret (j : ProcessJudgment S L) (done : A → L) (halt : H → L) : Process S H A → L
  | .done a => done a
  | .halt h => halt h
  | .call op k => j.node op fun v => (k v).interpret j done halt

theorem Process.interpret_bind (j : ProcessJudgment S L) (done : B → L) (halt : H → L)
    (k : A → Process S H B) (p : Process S H A) :
    (p.bind k).interpret j done halt = p.interpret j (fun a => (k a).interpret j done halt) halt := by
  induction p with
  | done | halt => rfl
  | call op next ih =>
    exact congrArg (j.node op) (funext ih)

/-- Predicate judgments support weakening when each effect respects implication. -/
def ProcessJudgment.Monotone {T : Type} (j : ProcessJudgment S (T → Prop)) : Prop :=
  ∀ op (p q : S.Reply op → T → Prop), (∀ v t, p v t → q v t) → ∀ t, j.node op p t → j.node op q t

/-- Every instruction composes with its continuation in exactly the same way for traces,
all-path properties, resources and stateful observations. -/
theorem Term.interpret_step {D : Dialect} (sem : Semantics D) {Γ : Ctx D.Ty} {outs mid : List D.Ty}
    (key : Key) (i : Instr D Γ mid) (ns : Names mid) (rest : Term D (Γ.extend ns) outs)
    (path : List Frame) (env : Env sem.Val Γ) (j : ProcessJudgment sem.S L) (done : HList sem.Val outs → L)
    (halt : sem.H → L) :
    ((Term.step key i ns rest).denote sem path env).interpret j done halt =
      (i.denote sem key path env).interpret j (fun vs => (rest.denote sem path (env.extend ns vs)).interpret j done halt) halt := by
  rw [Term.denote_step, Process.interpret_bind]

@[irreducible] def Process.sealed (p : Process S H A) : Process S H A := p

/-- A sealed process is the process. -/
theorem Process.sealed_eq (p : Process S H A) : p.sealed = p := by
  unfold Process.sealed
  rfl

def ProcessJudgment.every (allowed : ∀ op, S.Reply op → Prop) : ProcessJudgment S Prop where
  node op next := ∀ v, allowed op v → next v

def ProcessJudgment.possible (allowed : ∀ op, S.Reply op → Prop) : ProcessJudgment S Prop where
  node op next := ∃ v, allowed op v ∧ next v

abbrev EffectTrace (S : Sig) := List ((op : S.Op) × S.Reply op)

/-- Match both the operation (including its payload) and its dependent reply. -/
def ProcessJudgment.trace (S : Sig) : ProcessJudgment S (EffectTrace S → Prop) where
  node op next trace := ∃ v tail, trace = ⟨op, v⟩ :: tail ∧ next v tail

end Zkc.Core
