import Zkc.Realization.Acceptance

/-! Decision-only and output-bearing clients of the same adequacy API.

The second client returns a residual value to an actual PIR continuation.
Acceptance of the prefix does not assert satisfaction of that residual.
-/

namespace Examples.Acceptance

open PIR Zkc.Realization

section Decision

variable {F : Type} [DecidableEq F]

def scalarAccepts (input : F × F) (_ : Unit) : Prop :=
  Relation.scalarTerminal input.1 input.2 = .accepted ()

def scalarConstraints (input : F × F) (_ : Unit) (_ : Unit) : Prop :=
  input.2 = input.1

theorem scalar_realization : Acceptance (scalarAccepts (F := F)) scalarConstraints where
  sound i _ _ h := by simp [scalarAccepts, Relation.scalarTerminal, scalarConstraints] at *; exact h
  complete i _ h := by
    refine ⟨(), ?_⟩
    simpa [scalarAccepts, Relation.scalarTerminal, scalarConstraints] using h

/-- The decision-only specialization exposes no output beyond Unit. -/
theorem scalar_followed (input : F × F) :
    (∃ o w, scalarConstraints input o w ∧ True) ↔
      ∃ o, scalarAccepts input o ∧ True :=
  scalar_realization.followedBy (fun _ _ => True) input

end Decision

def interface : Signature := ⟨Empty, Empty.elim⟩

def handler : Handler interface Unit Unit := fun op => nomatch op

/-- A successful reduction can return a still-unchecked obligation. -/
def defer (value : Nat) : Proc interface (Continuation.Terminal Nat) :=
  .done (.accepted value)

def finish (expected actual : Nat) : Proc interface Bool :=
  .done (decide (actual = expected))

def deferredAccepts (value output : Nat) : Prop :=
  ((defer value).run handler ()).outcome = .returned (.accepted output)

/-- Witnesses can contain arbitrary auxiliary data, but every satisfying
assignment must bind the exposed output to the actual returned value. -/
def deferredConstraints (value output : Nat) (witness : Nat × Bool) : Prop :=
  witness.1 = value ∧ output = witness.1

theorem deferred_realization : Acceptance deferredAccepts deferredConstraints where
  sound i o w h := by
    have eqv : o = i := h.2.trans h.1
    subst o
    rfl
  complete i o h := by
    have eqv : i = o := by simpa [deferredAccepts, defer, Proc.run] using h
    exact ⟨(i, false), rfl, eqv.symm⟩

/-- A consumer can impose an additional obligation on the exact prefix output. -/
theorem deferred_followed (value expected : Nat) :
    (∃ output witness, deferredConstraints value output witness ∧ output = expected) ↔
      ∃ output, deferredAccepts value output ∧ output = expected :=
  deferred_realization.followedBy (fun _ output => output = expected) value

theorem consumer_execution (value expected : Nat) :
    ((Continuation.after (defer value) (finish expected)).run handler ()).outcome =
      .returned (decide (value = expected)) := rfl

/-- Equal acceptance bits do not preserve the result of the actual continuation. -/
theorem changed_output_changes_consumer :
    (∃ output, deferredAccepts 7 output) ∧
    (∃ output, deferredAccepts 8 output) ∧
    ((Continuation.after (defer 7) (finish 7)).run handler ()).outcome = .returned true ∧
    ((Continuation.after (defer 8) (finish 7)).run handler ()).outcome = .returned false :=
  ⟨⟨7, rfl⟩, ⟨8, rfl⟩, rfl, rfl⟩

/-- Closing the output too early makes the same unbound constraints appear
adequate for the acceptance bit; this loses the following consumer's subject. -/
theorem unbound_output_preserves_acceptance_bit (value : Nat) :
    (∃ (_ : Nat) (w : Nat × Bool), w.1 = value) ↔
      ∃ output, deferredAccepts value output :=
  ⟨fun _ => ⟨value, rfl⟩, fun _ => ⟨0, (value, false), rfl⟩⟩

theorem unbound_output_unsound :
    ¬ Acceptance deferredAccepts (fun (value _ : Nat) (w : Nat × Bool) => w.1 = value) := by
  intro realization
  have wrong := realization.sound 7 8 (7, false) rfl
  simp [deferredAccepts, defer, Proc.run] at wrong

/-- A proof about the supplied honest assignment alone misses this witness. -/
theorem bad_auxiliary_branch_unsound :
    ¬ Acceptance deferredAccepts
      (fun (value output : Nat) (w : Nat × Bool) =>
        (w.2 = false ∧ output = value) ∨ w.2 = true) := by
  intro realization
  have wrong := realization.sound 7 8 (7, true) (Or.inr rfl)
  simp [deferredAccepts, defer, Proc.run] at wrong

end Examples.Acceptance
