import Std

set_option autoImplicit false

namespace Zkc.Source.LocalArithmetic
-- This is an executable first-order scalar fragment. No semantic function
-- supplied by a caller can close over a global reference execution.
inductive Expr where
  | lit : Nat → Expr
  | input : Nat → Expr
  | mem : Nat → Expr
  | add : Expr → Expr → Expr
  | mul : Expr → Expr → Expr
  | mod : Expr → Nat → Expr
  deriving Repr, BEq, DecidableEq

abbrev Memory := List Nat
abbrev Env := Nat → Nat
abbrev View := Nat → Option Nat

def Expr.eval (ρ : Env) (m : Memory) : Expr → Nat
  | .lit n => n
  | .input k => ρ k
  | .mem k => m[k]?.getD 0
  | .add a b => a.eval ρ m + b.eval ρ m
  | .mul a b => a.eval ρ m * b.eval ρ m
  | .mod a q => a.eval ρ m % q

def Expr.check (available : Nat → Bool) : Expr → Bool
  | .lit _ | .mem _ => true
  | .input k => available k
  | .add a b | .mul a b => a.check available && b.check available
  | .mod a _ => a.check available

inductive Program where
  | done : Program
  | save : Expr → Program → Program
  | emit : Expr → Program → Program
  | branch : Expr → Program → Program → Program
  deriving Repr, BEq

structure Result where
  sent : List Nat
  memory : Memory
  deriving Repr, BEq

def Program.eval (ρ : Env) (m : Memory) : Program → Result
  | .done => ⟨[], m⟩
  | .save e p => p.eval ρ (e.eval ρ m :: m)
  | .emit e p => let r := p.eval ρ m; ⟨e.eval ρ m :: r.sent, r.memory⟩
  | .branch e p q => if e.eval ρ m = 0 then p.eval ρ m else q.eval ρ m

def Program.check (available : Nat → Bool) : Program → Bool
  | .done => true
  | .save e p | .emit e p => e.check available && p.check available
  | .branch e p q => e.check available && (p.check available && q.check available)

-- The key lemma concerns an ordinary evaluator, not an instrumented evaluator
-- whose values are declared secure. The executable checker produces its premise.
theorem expr_confinement (e : Expr) (a : Nat → Bool) (ρ σ : Env)
    (agree : ∀ k, a k = true → ρ k = σ k)
    (ok : e.check a = true) (m : Memory) : e.eval ρ m = e.eval σ m := by
  induction e with
  | lit n => rfl
  | input k => exact agree k ok
  | mem k => rfl
  | add x y ihx ihy =>
      simp only [Expr.check, Bool.and_eq_true] at ok
      simp only [Expr.eval, ihx ok.1, ihy ok.2]
  | mul x y ihx ihy =>
      simp only [Expr.check, Bool.and_eq_true] at ok
      simp only [Expr.eval, ihx ok.1, ihy ok.2]
  | mod x q ih => exact congrArg (fun v => v % q) (ih ok)

theorem evaluator_confinement (p : Program) (a : Nat → Bool) (ρ σ : Env)
    (agree : ∀ k, a k = true → ρ k = σ k)
    (ok : p.check a = true) (m : Memory) : p.eval ρ m = p.eval σ m := by
  induction p generalizing m with
  | done => rfl
  | save e p ih =>
      simp only [Program.check, Bool.and_eq_true] at ok
      simp only [Program.eval, expr_confinement e a ρ σ agree ok.1 m]
      exact ih ok.2 _
  | emit e p ih =>
      simp only [Program.check, Bool.and_eq_true] at ok
      simp only [Program.eval, expr_confinement e a ρ σ agree ok.1 m, ih ok.2 m]
  | branch e p q ihp ihq =>
      simp only [Program.check, Bool.and_eq_true] at ok
      simp only [Program.eval, expr_confinement e a ρ σ agree ok.1 m,
        ihp ok.2.1 m, ihq ok.2.2 m]

-- Missing inputs reject before any block effects. The fallback is unreachable
-- for every input referenced by an accepted program.
def checkedRun (p : Program) (v : View) (m : Memory) : Option Result :=
  if p.check (fun k => (v k).isSome) then
    some (p.eval (fun k => (v k).getD 0) m)
  else none

def Realizes (v : View) (ρ : Env) : Prop :=
  ∀ k n, v k = some n → ρ k = n

theorem checkedRun_sound (p : Program) (v : View) (ρ : Env) (m : Memory)
    (realizes : Realizes v ρ)
    (ok : p.check (fun k => (v k).isSome) = true) :
    checkedRun p v m = some (p.eval ρ m) := by
  have agree : ∀ k, (v k).isSome = true → (v k).getD 0 = ρ k := by
    intro k h
    cases hv : v k with
    | none => simp [hv] at h
    | some n => simpa [hv] using (realizes k n hv).symm
  simp only [checkedRun, ok, ↓reduceIte]
  exact congrArg some (evaluator_confinement p _ _ ρ agree ok m)

-- A materialization theorem for an explicit projection, for arbitrary global
-- worlds and arbitrary accepted programs. Projection is a mathematical boundary,
-- not a claim that an actual PIR runtime already constructs it.
def project (a : Nat → Bool) (ρ : Env) : View :=
  fun k => if a k then some (ρ k) else none

theorem projection_realizes (a : Nat → Bool) (ρ : Env) :
    Realizes (project a ρ) ρ := by
  intro k n h
  simp only [project] at h
  split at h
  next => exact Option.some.inj h
  next => contradiction

theorem projected_run (p : Program) (a : Nat → Bool) (ρ : Env) (m : Memory)
    (ok : p.check a = true) :
    checkedRun p (project a ρ) m = some (p.eval ρ m) := by
  apply checkedRun_sound p _ ρ m (projection_realizes a ρ)
  have h : (fun k => ((project a ρ) k).isSome) = a := by
    funext k
    simp only [project]
    cases a k <;> rfl
  rw [h]
  exact ok

-- Occurrences release information strictly before a local decision. Inputs
-- have release=0 and are available at decision 1; a delivered challenge at
-- occurrence 2 is first available at decision 3. Private future tape cells
-- remain absent even when their value is fixed in the global world.
structure Event where
  recipient : Nat
  release : Nat
  key : Nat
  value : Nat
  expires : Option Nat := none
  deriving Repr

def observe (role cut : Nat) (events : List Event) : View := fun k =>
  ((events.reverse.find? (fun e => e.recipient == role && e.release < cut && e.key == k &&
    (e.expires.isNone || cut <= e.expires.getD 0)))).map Event.value

end Zkc.Source.LocalArithmetic
