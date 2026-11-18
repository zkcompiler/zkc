module

public import Zkc.Core.Process.Handler

@[expose] public section

/-!
The base relation: two processes mean the same.

Two processes agree along every path of permitted replies: the same effects in the same order,
the same result where they return, the same payload where they stop. On a reply that is not
permitted nothing is compared, since an admitted program promises nothing there. Every "mean
the same" of the core is this relation.

It is an equivalence and a congruence for everything a process is built with (`bind`, `map`,
`mapHalt`, `recover`, bounded iteration, with steps that mean the same on every state or only
below a count); it carries a property on every path from one process to the other; and it is
kept by a handler whose replies are permitted, retry included (`Handler.run_same`). So a part of
a role program may be replaced by a part with the same process without a new argument about the
layers of a deployment. Between processes without effects it is equality (`eq_of_noSig`), and
on them what holds on every path does not depend on the replies permitted (`every_noSig`).

A value that a process can return on some path of permitted replies (`Process.CanReturn`) is
what a congruence for a sequence needs of the first process: what follows it is compared only
from such values. Its rules: what holds on every path holds of it, every result is one, a
sequence returns what its parts return, processes that mean the same return the same values, and
an iteration reaches each of its steps from such a value.
-/

namespace Zkc.Core

variable {S T : Sig} {H H' σ A B : Type}

/-- Two processes agree along every path of permitted replies. -/
inductive Process.SameWhen (permitted : ∀ op, S.Reply op → Prop) :
    Process S H A → Process S H A → Prop where
  | done (a : A) : SameWhen permitted (.done a) (.done a)
  | halt (payload : H) : SameWhen permitted (.halt payload) (.halt payload)
  | call (op : S.Op) {k k' : S.Reply op → Process S H A}
      (next : ∀ reply, permitted op reply → SameWhen permitted (k reply) (k' reply)) :
      SameWhen permitted (.call op k) (.call op k')

namespace Process.SameWhen

variable {permitted : ∀ op, S.Reply op → Prop}

theorem refl (p : Process S H A) : SameWhen permitted p p := by
  induction p with
  | done a => exact .done a
  | halt payload => exact .halt payload
  | call op k ih => exact .call op fun reply _ => ih reply

theorem symm {p q : Process S H A} (same : SameWhen permitted p q) : SameWhen permitted q p := by
  induction same with
  | done a => exact .done a
  | halt payload => exact .halt payload
  | call op _ ih => exact .call op fun reply hr => ih reply hr

theorem trans {p q r : Process S H A} (first : SameWhen permitted p q)
    (second : SameWhen permitted q r) : SameWhen permitted p r := by
  induction first generalizing r with
  | done a => exact second
  | halt payload => exact second
  | call op _ ih =>
      cases second with
      | call _ next' => exact .call op fun reply hr => ih reply hr (next' reply hr)

/-- A property on every path of one holds on every path of the other. -/
theorem every {p q : Process S H A} (same : SameWhen permitted p q) {onDone : A → Prop}
    {onHalt : H → Prop} (holds : p.Every permitted onDone onHalt) :
    q.Every permitted onDone onHalt := by
  induction same with
  | done a => exact holds
  | halt payload => exact holds
  | call op _ ih => exact fun reply hr => ih reply hr (holds reply hr)

/-- What follows two processes that mean the same, where it means the same on every result that
the first can return, means the same. -/
theorem bind {p q : Process S H A} (same : SameWhen permitted p q) {onDone : A → Prop}
    (reached : p.Every permitted onDone fun _ => True) {f g : A → Process S H B}
    (after : ∀ a, onDone a → SameWhen permitted (f a) (g a)) :
    SameWhen permitted (p.bind f) (q.bind g) := by
  induction same with
  | done a => exact after a reached
  | halt payload => exact .halt payload
  | call op _ ih => exact .call op fun reply hr => ih reply hr (reached reply hr)

theorem map {p q : Process S H A} (same : SameWhen permitted p q) (f : A → B) :
    SameWhen permitted (p.map f) (q.map f) := by
  induction same with
  | done a => exact .done (f a)
  | halt payload => exact .halt payload
  | call op _ ih => exact .call op fun reply hr => ih reply hr

theorem mapHalt {p q : Process S H A} (same : SameWhen permitted p q) (f : H → H') :
    SameWhen permitted (p.mapHalt f) (q.mapHalt f) := by
  induction same with
  | done a => exact .done a
  | halt payload => exact .halt (f payload)
  | call op _ ih => exact .call op fun reply hr => ih reply hr

/-- Recovery from the stops that the first can make, where the recoveries mean the same. -/
theorem recover {p q : Process S H A} (same : SameWhen permitted p q) {onHalt : H → Prop}
    (reached : p.Every permitted (fun _ => True) onHalt) {f g : H → Process S H' A}
    (after : ∀ payload, onHalt payload → SameWhen permitted (f payload) (g payload)) :
    SameWhen permitted (p.recover f) (q.recover g) := by
  induction same with
  | done a => exact .done a
  | halt payload => exact after payload reached
  | call op _ ih => exact .call op fun reply hr => ih reply hr (reached reply hr)

/-- Bounded iteration of steps that mean the same on every state that satisfies an invariant
which every step keeps. -/
theorem iterate (invariant : Nat → A → Prop) {step step' : Nat → A → Process S H A}
    (same : ∀ i a, invariant i a → SameWhen permitted (step i a) (step' i a))
    (kept : ∀ i a, invariant i a →
      (step i a).Every permitted (invariant (i + 1)) fun _ => True) :
    ∀ (n i : Nat) (a : A), invariant i a →
      SameWhen permitted (Process.iterate n step i a) (Process.iterate n step' i a) := by
  intro n
  induction n with
  | zero => intro i a _; exact refl _
  | succ n ih =>
      intro i a holds
      simp only [Process.iterate]
      exact bind (same i a holds) (kept i a holds) fun a' kept' => ih (i + 1) a' kept'

/-- Bounded iteration of steps that mean the same below a count, on every state that satisfies an
invariant which every step below the count keeps. -/
theorem iterate_below (invariant : Nat → A → Prop)
    {step step' : Nat → A → Process S H A} (count : Nat)
    (same : ∀ i a, i < count → invariant i a →
      SameWhen permitted (step i a) (step' i a))
    (kept : ∀ i a, i < count → invariant i a →
      (step i a).Every permitted (invariant (i + 1)) fun _ => True) :
    ∀ (n i : Nat) (a : A), i + n ≤ count → invariant i a →
      SameWhen permitted (Process.iterate n step i a) (Process.iterate n step' i a) := by
  intro n
  induction n with
  | zero => intro i a _ _; exact refl _
  | succ n ih =>
      intro i a within holds
      simp only [Process.iterate]
      exact bind (same i a (by omega) holds) (kept i a (by omega) holds)
        fun a' kept' => ih (i + 1) a' (by omega) kept'

end Process.SameWhen

/-- Processes without effects that mean the same are equal: there is no reply along which they
could differ. -/
theorem Process.SameWhen.eq_of_noSig {permitted : ∀ op, NoSig.Reply op → Prop}
    {p q : Process NoSig H A} (same : Process.SameWhen permitted p q) : p = q := by
  cases same with
  | done a => rfl
  | halt payload => rfl
  | call op _ => exact nomatch op

/-- On a process without effects, what holds on every path holds whatever replies are
permitted: there is no reply. -/
theorem Process.every_noSig {permitted permitted' : ∀ op, NoSig.Reply op → Prop}
    {onDone : A → Prop} {onHalt : H → Prop} :
    ∀ {p : Process NoSig H A}, p.Every permitted onDone onHalt → p.Every permitted' onDone onHalt
  | .done _, holds => holds
  | .halt _, holds => holds
  | .call op _, _ => nomatch op

/-! ## A value that a process can return -/

/-- The process returns the value on some path of permitted replies. -/
inductive Process.CanReturn (permitted : ∀ op, S.Reply op → Prop) : Process S H A → A → Prop where
  | done (a : A) : CanReturn permitted (.done a) a
  | call (op : S.Op) {k : S.Reply op → Process S H A} (reply : S.Reply op)
      (allowed : permitted op reply) {a : A} (next : CanReturn permitted (k reply) a) :
      CanReturn permitted (.call op k) a

section
variable {permitted : ∀ op, S.Reply op → Prop}

/-- What holds of every result on every path holds of a value that the process can return. -/
theorem Process.Every.canReturn {p : Process S H A} {onDone : A → Prop} {onHalt : H → Prop}
    (holds : p.Every permitted onDone onHalt) {a : A} (returns : p.CanReturn permitted a) :
    onDone a := by
  induction returns with
  | done a => exact holds
  | call op reply allowed _ ih => exact ih (holds reply allowed)

/-- On every path, what a process returns is a value that it can return. -/
theorem Process.every_canReturn (p : Process S H A) :
    p.Every permitted (fun a => p.CanReturn permitted a) fun _ => True := by
  induction p with
  | done a => exact .done a
  | halt _ => trivial
  | call op k ih =>
      exact fun reply allowed => Process.every_mono _ permitted
        (fun _ returns => .call op reply allowed returns) (fun _ h => h) (ih reply)

/-- A value that a process can return, followed by a value that what follows can return from it,
is a value that the sequence can return. -/
theorem Process.CanReturn.bind {p : Process S H A} {f : A → Process S H B} {a : A} {b : B}
    (first : p.CanReturn permitted a) (second : (f a).CanReturn permitted b) :
    (p.bind f).CanReturn permitted b := by
  induction first with
  | done _ => exact second
  | call op reply allowed _ ih => exact .call op reply allowed (ih second)

/-- A value that a sequence can return comes from a value that its first process can return. -/
theorem Process.CanReturn.of_bind {p : Process S H A} {f : A → Process S H B} {b : B}
    (returns : (p.bind f).CanReturn permitted b) :
    ∃ a, p.CanReturn permitted a ∧ (f a).CanReturn permitted b := by
  induction p with
  | done a => exact ⟨a, .done a, returns⟩
  | halt _ =>
      simp only [Process.bind] at returns
      cases returns
  | call op k ih =>
      simp only [Process.bind] at returns
      cases returns with
      | call _ reply allowed next =>
          obtain ⟨a, first, second⟩ := ih reply next
          exact ⟨a, .call op reply allowed first, second⟩

/-- Processes that mean the same can return the same values. -/
theorem Process.SameWhen.canReturn {p q : Process S H A} (same : Process.SameWhen permitted p q)
    {a : A} (returns : p.CanReturn permitted a) : q.CanReturn permitted a := by
  induction returns generalizing q with
  | done a =>
      cases same
      exact .done a
  | call op reply allowed _ ih =>
      cases same with
      | call _ next => exact .call op reply allowed (ih (next reply allowed))

/-- Bounded iteration, one iteration more: the iterations up to some number, then the step at
that number. -/
theorem Process.iterate_succ_eq_bind (step : Nat → A → Process S H A) :
    ∀ (n i : Nat) (a : A),
      Process.iterate (n + 1) step i a = (Process.iterate n step i a).bind (step (i + n))
  | 0, i, a => by
      show (step i a).bind (fun a' => Process.iterate 0 step (i + 1) a') = step (i + 0) a
      exact Process.bind_pure (step i a)
  | n + 1, i, a => by
      show (step i a).bind (fun a' => Process.iterate (n + 1) step (i + 1) a') =
        ((step i a).bind fun a' => Process.iterate n step (i + 1) a').bind (step (i + (n + 1)))
      rw [Process.bind_assoc]
      congr 1
      funext a'
      rw [Process.iterate_succ_eq_bind step n (i + 1) a', Nat.add_assoc, Nat.add_comm 1 n]

/-- A value that one more iteration can return, from a value that the iterations before it can
return and a value that the next step can return from it. -/
theorem Process.CanReturn.iterate_succ {step : Nat → A → Process S H A} {n i : Nat} {a b c : A}
    (before : (Process.iterate n step i a).CanReturn permitted b)
    (next : (step (i + n) b).CanReturn permitted c) :
    (Process.iterate (n + 1) step i a).CanReturn permitted c := by
  rw [Process.iterate_succ_eq_bind]
  exact before.bind next

/-- What holds on every path of a process and what follows it holds on every path of what
follows, from a value that the process can return. -/
theorem Process.Every.of_bind_canReturn {p : Process S H A} {f : A → Process S H B}
    {onDone : B → Prop} {onHalt : H → Prop} (holds : (p.bind f).Every permitted onDone onHalt)
    {a : A} (returns : p.CanReturn permitted a) : (f a).Every permitted onDone onHalt :=
  ((Process.every_bind p f permitted onDone onHalt).mp holds).canReturn returns

/-- The stops of a process and what follows it include the stops of the process. -/
theorem Process.Every.of_bind {p : Process S H A} {f : A → Process S H B} {onDone : B → Prop}
    {onHalt : H → Prop} (holds : (p.bind f).Every permitted onDone onHalt) :
    p.Every permitted (fun _ => True) onHalt :=
  Process.every_mono _ permitted (fun _ _ => trivial) (fun _ h => h)
    ((Process.every_bind p f permitted onDone onHalt).mp holds)

/-- The stops of an iteration include the stops of each step that it reaches below its count. -/
theorem Process.Every.iterate_step {step : Nat → A → Process S H A} {onDone : A → Prop}
    {onHalt : H → Prop} : ∀ (i count j : Nat) (a s : A), i < count →
      (Process.iterate count step j a).Every permitted onDone onHalt →
      (Process.iterate i step j a).CanReturn permitted s →
      (step (j + i) s).Every permitted (fun _ => True) onHalt
  | 0, count, j, a, s, below, holds, returns => by
      obtain ⟨c, rfl⟩ : ∃ c, count = c + 1 := ⟨count - 1, by omega⟩
      cases returns
      simp only [Process.iterate] at holds
      rw [Nat.add_zero]
      exact holds.of_bind
  | i + 1, count, j, a, s, below, holds, returns => by
      obtain ⟨c, rfl⟩ : ∃ c, count = c + 1 := ⟨count - 1, by omega⟩
      simp only [Process.iterate] at holds returns
      obtain ⟨a', first, rest⟩ := Process.CanReturn.of_bind returns
      have := Process.Every.iterate_step i c (j + 1) a' s (by omega)
        (holds.of_bind_canReturn first) rest
      rw [show j + (i + 1) = j + 1 + i by omega]
      exact this

end

/-- A handler and a retry whose replies to the program are permitted: every reply of a clause,
the number that begins an attempt and the reply that ends its body are permitted to the program
above, and the mark of an attempt keeps what holds on every path below. -/
structure Handler.Permits (h : Handler S T H σ) (retry : Retry S T H)
    (above : ∀ op, S.Reply op → Prop) (below : ∀ op, T.Reply op → Prop) : Prop where
  clause : ∀ op s, (h.clause op s).Every below (fun out => above op out.1) fun _ => True
  begins : ∀ op exhausted number, retry.begins op = some (exhausted, number) →
    ∀ i, above op (number i)
  ends : ∀ op reply, retry.ends op = some reply → above op reply
  mark : ∀ {H'' X : Type} (i : Nat) (p : Process T H'' X) (onDone : X → Prop)
    (onHalt : H'' → Prop), p.Every below onDone onHalt → (retry.mark i p).Every below onDone onHalt

/-- Every process satisfies the trivial property on every path. -/
theorem Process.every_true (permitted : ∀ op, S.Reply op → Prop) :
    ∀ p : Process S H A, p.Every permitted (fun _ => True) fun _ => True
  | .done _ => trivial
  | .halt _ => trivial
  | .call _ k => fun reply _ => every_true permitted (k reply)

/-- A property on every path of a process, with a map applied to its stops, holds on every path
of the process whose stops are mapped. -/
theorem Process.every_mapHalt (permitted : ∀ op, S.Reply op → Prop) (f : H → H')
    {onDone : A → Prop} {onHalt : H' → Prop} :
    ∀ p : Process S H A, p.Every permitted onDone (fun payload => onHalt (f payload)) →
      (p.mapHalt f).Every permitted onDone onHalt
  | .done _, holds => holds
  | .halt _, holds => holds
  | .call _ k, holds => fun reply hr => every_mapHalt permitted f (k reply) (holds reply hr)

/-- The attempts of bodies that mean the same, attempt by attempt and from every state, mean the
same. -/
theorem attempts_same {below : ∀ op, T.Reply op → Prop} (retriable : H → Bool) (exhausted : H)
    (again : Nat → σ → σ → Except H σ)
    {body body' : Nat → σ → Process T ((Bool × H) × σ) (A × σ)} (entry : σ)
    (same : ∀ i s, Process.SameWhen below (body i s) (body' i s)) :
    ∀ n i s, Process.SameWhen below (attempts retriable exhausted again body entry n i s)
      (attempts retriable exhausted again body' entry n i s) := by
  intro n
  induction n with
  | zero => intro i s; exact .refl _
  | succ n ih =>
      intro i s
      simp only [attempts]
      refine Process.SameWhen.recover (same i s) (Process.every_true below (body i s))
        fun stop _ => ?_
      cases hc : (stop.1.1 && retriable stop.1.2) with
      | false =>
          rw [ite_eq_right Bool.false_ne_true, ite_eq_right Bool.false_ne_true]
          exact .refl _
      | true =>
          rw [ite_eq_left rfl, ite_eq_left rfl]
          cases n with
          | zero => exact .refl _
          | succ m =>
              cases again (i + 1) entry stop.2 with
              | ok next => exact ih (i + 1) next
              | error why => exact .refl _

/-- Programs that mean the same have runs, and bodies of every attempt, that mean the same under
a handler whose replies are permitted. -/
theorem Handler.run_inside_same {h : Handler S T H σ} {retry : Retry S T H}
    {above : ∀ op, S.Reply op → Prop} {below : ∀ op, T.Reply op → Prop}
    (permits : h.Permits retry above below) {p q : Process S H A}
    (same : Process.SameWhen above p q) :
    (∀ s, Process.SameWhen below (h.run retry p s) (h.run retry q s)) ∧
      ∀ i s, Process.SameWhen below (h.inside retry i p s) (h.inside retry i q s) := by
  induction same with
  | done a => exact ⟨fun _ => .refl _, fun _ _ => .refl _⟩
  | halt payload => exact ⟨fun _ => .refl _, fun _ _ => .refl _⟩
  | call op _ ih =>
      constructor
      · intro s
        cases hb : retry.begins op with
        | none =>
            simp only [Handler.run, hb]
            exact Process.SameWhen.bind (.refl _) (permits.clause op s)
              fun out hout => (ih out.1 hout).1 out.2
        | some begun =>
            obtain ⟨exhausted, number⟩ := begun
            simp only [Handler.run, hb]
            exact attempts_same _ _ _ _
              (fun i s' => (ih (number i) (permits.begins op exhausted number hb i)).2 i s') _ _ _
      · intro i s
        cases he : retry.ends op with
        | some reply =>
            simp only [Handler.inside, he]
            exact ((ih reply (permits.ends op reply he)).1 s).mapHalt _
        | none =>
            simp only [Handler.inside, he]
            exact Process.SameWhen.bind (.refl _) (onDone := fun out => above op out.1)
              (Process.every_mapHalt below _ _
                (permits.mark i (h.clause op s) _ _ (permits.clause op s)))
              fun out hout => (ih out.1 hout).2 i out.2

/-- Programs that mean the same have runs that mean the same under a handler whose replies are
permitted, from every state, retry included. -/
theorem Handler.run_same {h : Handler S T H σ} {retry : Retry S T H}
    {above : ∀ op, S.Reply op → Prop} {below : ∀ op, T.Reply op → Prop}
    (permits : h.Permits retry above below) {p q : Process S H A}
    (same : Process.SameWhen above p q) (s : σ) :
    Process.SameWhen below (h.run retry p s) (h.run retry q s) := by
  exact (Handler.run_inside_same permits same).1 s

end Zkc.Core
