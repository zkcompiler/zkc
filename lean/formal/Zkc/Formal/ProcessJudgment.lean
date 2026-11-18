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

theorem Process.interpret_mono {T : Type} {j : ProcessJudgment S (T → Prop)} (mono : j.Monotone)
    {p q : A → T → Prop} {h k : H → T → Prop} (done : ∀ a t, p a t → q a t)
    (halt : ∀ e t, h e t → k e t) (program : Process S H A) :
    ∀ t, program.interpret j p h t → program.interpret j q k t := by
  induction program with
  | done a => exact done a
  | halt e => exact halt e
  | call op next ih => exact mono op _ _ ih

/-- A proof of the indexed body extends to any number of iterations and any initial
position within the stated limit. The judgment determines what the invariant carries. -/
theorem Process.interpret_iterate {T : Type} {j : ProcessJudgment S (T → Prop)} (mono : j.Monotone)
    (step : Nat → A → Process S H A) (inv : Nat → A → T → Prop) (halt : H → T → Prop) (limit : Nat)
    (body : ∀ i a t, i < limit → inv i a t → (step i a).interpret j (inv (i+1)) halt t)
    (count start : Nat) (a : A) (state : T) (within : start + count ≤ limit) (initial : inv start a state) :
    (Process.iterate count step start a).interpret j (inv (start+count)) halt state := by
  induction count generalizing start a state with
  | zero => exact initial
  | succ n ih =>
    rw [Process.iterate, Process.interpret_bind]
    apply Process.interpret_mono mono (fun a' t h => ?_) (fun _ _ h => h) _ state
      (body start a state (by omega) initial)
    have tail := ih (start+1) a' t (by omega) h
    simpa only [Nat.add_right_comm start 1 n, Nat.add_succ, Nat.add_zero] using tail

/-- Every instruction composes with its continuation in exactly the same way for traces,
all-path properties, resources and stateful observations. -/
theorem Term.interpret_step {D : Dialect} (sem : Semantics D) {Γ : Ctx D.Ty} {outs mid : List D.Ty}
    (key : Key) (i : Instr D Γ mid) (ns : Names mid) (rest : Term D (Γ.extend ns) outs)
    (path : List Frame) (env : Env sem.Val Γ) (j : ProcessJudgment sem.S L) (done : HList sem.Val outs → L)
    (halt : sem.H → L) :
    ((Term.step key i ns rest).denote sem path env).interpret j done halt =
      (i.denote sem key path env).interpret j (fun vs => (rest.denote sem path (env.extend ns vs)).interpret j done halt) halt := by
  rw [Term.denote_step, Process.interpret_bind]

def ProcessJudgment.every (allowed : ∀ op, S.Reply op → Prop) : ProcessJudgment S Prop where
  node op next := ∀ v, allowed op v → next v

theorem Process.every_iff_interpret (allowed : ∀ op, S.Reply op → Prop) (p : Process S H A)
    (done : A → Prop) (halt : H → Prop) :
    p.Every allowed done halt ↔ p.interpret (.every allowed) done halt := by
  induction p with
  | done | halt => rfl
  | call op k ih =>
    change (∀ v, allowed op v → _) ↔ ∀ v, allowed op v → _
    exact ⟨fun h v ok => (ih v).mp (h v ok), fun h v ok => (ih v).mpr (h v ok)⟩

/-- A site policy bounds the exceptional replies at a charge chosen before the reply.
All permitted, nonexceptional continuations inherit the remaining path budget. The unit
and the meaning of a charge belong to the policy. -/
def ProcessJudgment.charged (allowed : ∀ op, S.Reply op → Prop)
    (small : (op : S.Op) → Nat → (S.Reply op → Prop) → Prop) : ProcessJudgment S (Nat → Prop) where
  node op next budget := ∃ fee bad, fee ≤ budget ∧ small op fee bad ∧
    ∀ v, allowed op v → ¬bad v → next v (budget - fee)

theorem ProcessJudgment.charged_mono (allowed : ∀ op, S.Reply op → Prop)
    (small : (op : S.Op) → Nat → (S.Reply op → Prop) → Prop) : (charged allowed small).Monotone := by
  rintro op p q implies budget ⟨fee, bad, bound, ok, next⟩
  exact ⟨fee, bad, bound, ok, fun v valid kept => implies v _ (next v valid kept)⟩

theorem Process.every_of_zero_charge (allowed : ∀ op, S.Reply op → Prop)
    (small : (op : S.Op) → Nat → (S.Reply op → Prop) → Prop)
    (zero : ∀ op bad, small op 0 bad → ∀ v, allowed op v → ¬bad v) (p : Process S H A)
    (done : A → Prop) (halt : H → Prop)
    (h : p.interpret (.charged allowed small) (fun a _ => done a) (fun e _ => halt e) 0) :
    p.Every allowed done halt := by
  induction p with
  | done | halt => exact h
  | call op k ih =>
    obtain ⟨fee, bad, bound, ok, next⟩ := h
    obtain rfl := Nat.eq_zero_of_le_zero bound
    exact fun v valid => ih v (next v valid (zero op bad ok v valid))

def ProcessJudgment.possible (allowed : ∀ op, S.Reply op → Prop) : ProcessJudgment S Prop where
  node op next := ∃ v, allowed op v ∧ next v

theorem Process.canReturn_iff_interpret (allowed : ∀ op, S.Reply op → Prop) (p : Process S H A) (a : A) :
    p.CanReturn allowed a ↔ p.interpret (.possible allowed) (· = a) (fun _ => False) := by
  induction p with
  | done x => constructor <;> rintro h <;> cases h <;> constructor
  | halt h => constructor <;> intro h <;> cases h
  | call op k ih =>
    constructor
    · intro h
      cases h with | call _ v ok tail => exact ⟨v, ok, (ih v).mp tail⟩
    · rintro ⟨v, ok, tail⟩
      exact .call op v ok ((ih v).mpr tail)

abbrev EffectTrace (S : Sig) := List ((op : S.Op) × S.Reply op)

/-- Match both the operation (including its payload) and its dependent reply. -/
def ProcessJudgment.trace (S : Sig) : ProcessJudgment S (EffectTrace S → Prop) where
  node op next trace := ∃ v tail, trace = ⟨op, v⟩ :: tail ∧ next v tail

end Zkc.Core
