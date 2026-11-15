module


@[expose] public section

/-!
Processes: well-founded trees of effects, with what a stop carries and what is returned.

A process is the meaning of every program of the core: a function is a process with no effect,
a protocol one whose effects are the events, a role program one whose effects are the role's
part of each event. `Process.Every` is the one definition of "on every path"; its rules
(sequencing, weakening, a loop with an invariant) are the common rules of proof.
-/

namespace Zkc.Core

structure Sig where
  Op : Type
  Reply : Op → Type

/-- A well-founded tree of effects. A stop carries a payload. -/
inductive Process (S : Sig) (H : Type) (A : Type) where
  | done (a : A)
  | halt (payload : H)
  | call (op : S.Op) (k : S.Reply op → Process S H A)

def Process.bind {S : Sig} {H A B : Type} :
    Process S H A → (A → Process S H B) → Process S H B
  | .done a, f => f a
  | .halt payload, _ => .halt payload
  | .call op k, f => .call op fun reply => (k reply).bind f

/-- On every path with permitted replies, what the process returns satisfies `onDone` and how
it stops satisfies `onHalt`. This is the one definition of "on every path". -/
def Process.Every {S : Sig} {H A : Type} (permitted : ∀ op, S.Reply op → Prop)
    (onDone : A → Prop) (onHalt : H → Prop) : Process S H A → Prop
  | .done a => onDone a
  | .halt payload => onHalt payload
  | .call op k => ∀ reply, permitted op reply → (k reply).Every permitted onDone onHalt

/-- Every stop of the process satisfies `P`, on every permitted reply. -/
abbrev Process.StopsWhen {S : Sig} {H A : Type} (permitted : ∀ op, S.Reply op → Prop)
    (P : H → Prop) (p : Process S H A) : Prop :=
  p.Every permitted (fun _ => True) P

/-- Every stop of the process satisfies `P`, on every reply. -/
abbrev Process.Stops {S : Sig} {H A : Type} (P : H → Prop) (p : Process S H A) : Prop :=
  p.StopsWhen (fun _ _ => True) P

/-- No effects. -/
@[reducible] def NoSig : Sig := ⟨Empty, fun op => nomatch op⟩


/-! ## Processes -/

/-- Bounded iteration with the iteration number. -/
def Process.iterate {S : Sig} {H A : Type} :
    Nat → (Nat → A → Process S H A) → Nat → A → Process S H A
  | 0, _, _, a => .done a
  | n + 1, step, i, a => (step i a).bind fun a' => Process.iterate n step (i + 1) a'

def Process.map {S : Sig} {H A B : Type} (f : A → B) : Process S H A → Process S H B
  | .done a => .done (f a)
  | .halt payload => .halt payload
  | .call op k => .call op fun reply => (k reply).map f

/-! ## The rules of every path -/

/-- Sequencing: on every path of `p` then `k`, exactly when on every path of `p` the
continuation satisfies the property on every path. -/
theorem Process.every_bind {S : Sig} {H A B : Type} (p : Process S H A)
    (k : A → Process S H B) (permitted : ∀ op, S.Reply op → Prop) (onDone : B → Prop)
    (onHalt : H → Prop) :
    (p.bind k).Every permitted onDone onHalt ↔
      p.Every permitted (fun a => (k a).Every permitted onDone onHalt) onHalt := by
  induction p with
  | done a => exact Iff.rfl
  | halt why => exact Iff.rfl
  | call op next ih =>
      simp only [Process.bind, Process.Every]
      constructor
      · intro h reply hr
        exact (ih reply).mp (h reply hr)
      · intro h reply hr
        exact (ih reply).mpr (h reply hr)

/-- Weakening: what holds of the returns and of the stops on every path, weakened. -/
theorem Process.every_mono {S : Sig} {H A : Type} (p : Process S H A)
    (permitted : ∀ op, S.Reply op → Prop) {P Q : A → Prop} {R T : H → Prop}
    (values : ∀ a, P a → Q a) (stops : ∀ h, R h → T h) (h : p.Every permitted P R) :
    p.Every permitted Q T := by
  induction p with
  | done a => exact values a h
  | halt why => exact stops why h
  | call op next ih => exact fun reply hr => ih reply (h reply hr)

/-- A loop with a symbolic invariant: when each iteration keeps the invariant, from its number
to the next, so do any number of iterations. -/
theorem Process.every_iterate {S : Sig} {H A : Type} (permitted : ∀ op, S.Reply op → Prop)
    (onHalt : H → Prop) (step : Nat → A → Process S H A) (I : Nat → A → Prop)
    (keeps : ∀ i a, I i a → (step i a).Every permitted (I (i + 1)) onHalt) :
    ∀ (n i : Nat) (a : A), I i a → (Process.iterate n step i a).Every permitted (I (i + n)) onHalt
  | 0, i, a, initial => by simpa [Process.iterate, Process.Every] using initial
  | n + 1, i, a, initial => by
      rw [Process.iterate, Process.every_bind]
      refine Process.every_mono _ permitted (fun b hb => ?_) (fun _ h => h) (keeps i a initial)
      have := Process.every_iterate permitted onHalt step I keeps n (i + 1) b hb
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this

/-- Iteration up to a count: on every path, the invariant holds after the iterations, when each
step keeps it from an iteration below the count to the next. -/
theorem Process.every_iterate_below {S : Sig} {H A : Type} (permitted : ∀ op, S.Reply op → Prop)
    (onHalt : H → Prop) (step : Nat → A → Process S H A) (I : Nat → A → Prop) (count : Nat)
    (keeps : ∀ i a, i < count → I i a → (step i a).Every permitted (I (i + 1)) onHalt) :
    ∀ (n i : Nat) (a : A), i + n ≤ count → I i a →
      (Process.iterate n step i a).Every permitted (I (i + n)) onHalt
  | 0, i, a, _, initial => by simpa [Process.iterate, Process.Every] using initial
  | n + 1, i, a, within, initial => by
      rw [Process.iterate, Process.every_bind]
      refine Process.every_mono _ permitted (fun b hb => ?_) (fun _ h => h)
        (keeps i a (by omega) initial)
      have := Process.every_iterate_below permitted onHalt step I count keeps n (i + 1) b
        (by omega) hb
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this


def Process.mapHalt {S : Sig} {H H' A : Type} (f : H → H') : Process S H A → Process S H' A
  | .done a => .done a
  | .halt payload => .halt (f payload)
  | .call op k => .call op fun reply => (k reply).mapHalt f

def Process.recover {S : Sig} {H H' A : Type} :
    Process S H A → (H → Process S H' A) → Process S H' A
  | .done a, _ => .done a
  | .halt payload, f => f payload
  | .call op k, f => .call op fun reply => (k reply).recover f


namespace Process

variable {S : Sig} {H A B C : Type}

theorem bind_assoc (f : A → Process S H B) (g : B → Process S H C) :
    ∀ p : Process S H A, (p.bind f).bind g = p.bind fun a => (f a).bind g
  | .done _ => rfl
  | .halt _ => rfl
  | .call op k => by
      simp only [Process.bind]
      congr 1
      funext reply
      exact bind_assoc f g (k reply)

theorem bind_pure : ∀ p : Process S H A, (p.bind fun a => .done a) = p
  | .done _ => rfl
  | .halt _ => rfl
  | .call op k => by
      simp only [Process.bind]
      congr 1
      funext reply
      exact bind_pure (k reply)

theorem map_eq_bind (f : A → B) : ∀ p : Process S H A, p.map f = p.bind fun a => .done (f a)
  | .done _ => rfl
  | .halt _ => rfl
  | .call op k => by
      simp only [Process.map, Process.bind]
      congr 1
      funext reply
      exact map_eq_bind f (k reply)

theorem map_bind (f : A → Process S H B) (g : B → C) (p : Process S H A) :
    (p.bind f).map g = p.bind fun a => (f a).map g := by
  rw [map_eq_bind, bind_assoc]
  simp only [map_eq_bind]

theorem bind_map (f : A → B) (g : B → Process S H C) (p : Process S H A) :
    (p.map f).bind g = p.bind fun a => g (f a) := by
  rw [map_eq_bind, bind_assoc]
  rfl

theorem map_map (f : A → B) (g : B → C) (p : Process S H A) :
    (p.map f).map g = p.map fun a => g (f a) := by
  rw [map_eq_bind, map_eq_bind, map_eq_bind, bind_assoc]
  rfl

theorem map_id' (p : Process S H A) : p.map (fun a => a) = p := by
  rw [map_eq_bind, bind_pure]

/-- A loop that also gathers something has, without what it gathers, the loop's process. -/
theorem iterate_fst {X : Type} {step : Nat → A → Process S H A}
    {gather : Nat → A × X → Process S H (A × X)}
    (h : ∀ i a x, (gather i (a, x)).map Prod.fst = step i a) :
    ∀ n i a x, (Process.iterate n gather i (a, x)).map Prod.fst = Process.iterate n step i a
  | 0, _, _, _ => rfl
  | n + 1, i, a, x => by
      simp only [Process.iterate]
      rw [map_bind, ← h i a x, bind_map]
      congr 1
      funext s
      exact iterate_fst h n (i + 1) s.1 s.2

theorem bind_iterate_fst {X D : Type} {step : Nat → A → Process S H A}
    {gather : Nat → A × X → Process S H (A × X)} {F1 : A × X → Process S H D}
    {F2 : A → Process S H D}
    (h : ∀ i a x, (gather i (a, x)).map Prod.fst = step i a) (hF : ∀ s, F1 s = F2 s.1)
    (n i : Nat) (a : A) (x : X) :
    (Process.iterate n gather i (a, x)).bind F1 = (Process.iterate n step i a).bind F2 := by
  rw [← iterate_fst h n i a x, bind_map]
  congr 1
  funext s
  exact hF s

end Process

end Zkc.Core

#print axioms Zkc.Core.Process.every_bind
#print axioms Zkc.Core.Process.every_mono
#print axioms Zkc.Core.Process.every_iterate
#print axioms Zkc.Core.Process.every_iterate_below
