module

public section

/-! Effect trees: the processes that programs denote.

This is the part of the execution foundation that the core model needs: the stops, an
effect signature, the well-founded tree of calls, sequencing with its laws, and bounded
iteration, with and without the iteration number. It imports nothing.
-/

set_option autoImplicit false

namespace PIR

/-- Terminal execution outcomes. -/
inductive Stop where
  | reject | abort | exhausted | incomplete | refused | undefined
  deriving DecidableEq, Repr

structure Signature where
  Op : Type
  Reply : Op → Type

/-- A well-founded effect tree. Each execution path terminates; reply branching need
not be finite. -/
inductive Process (I : Signature) (A : Type) where
  | done : A → Process I A
  | halt : Stop → Process I A
  | call : (o : I.Op) → (I.Reply o → Process I A) → Process I A

variable {I : Signature} {A B : Type}

@[expose] def Process.bind (p : Process I A) (k : A → Process I B) : Process I B :=
  match p with
  | .done a => k a
  | .halt why => .halt why
  | .call o next => .call o (fun a => (next a).bind k)

namespace Process

theorem done_bind (value : A) (next : A → Process I B) : (Process.done value).bind next = next value :=
  rfl

theorem bind_assoc {C : Type} (source : Process I A) (next : A → Process I B)
    (last : B → Process I C) :
    (source.bind next).bind last = source.bind (fun value => (next value).bind last) := by
  induction source with
  | done value => rfl
  | halt why => rfl
  | call op tail ih =>
    simp only [bind]
    congr 1
    funext reply
    exact ih reply

@[simp] theorem bind_done (source : Process I A) : source.bind .done = source := by
  induction source with
  | done value => rfl
  | halt why => rfl
  | call op tail ih =>
    simp only [bind]
    congr 1
    funext reply
    exact ih reply

end Process

/-- Bounded iteration. -/
@[expose] def repeatN (n : Nat) (step : A → Process I A) (a : A) : Process I A :=
  match n with
  | 0 => .done a
  | n+1 => (step a).bind (fun b => repeatN n step b)

/-- Bounded iteration of a step that takes its iteration number, counted from `start`. -/
@[expose] def iterateN (n : Nat) (step : Nat → A → Process I A) (start : Nat) (a : A) :
    Process I A :=
  match n with
  | 0 => .done a
  | n+1 => (step start a).bind (fun b => iterateN n step (start + 1) b)

end PIR
