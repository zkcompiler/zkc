module

public import Zkc.Core.Process.Process

@[expose] public section

/-!
Handlers and the retry of an attempt.

A handler answers the effects of a process by processes of the layer below, from a state.
Handlers compose; a stop carries what stops and the state reached. The retry of an attempt
runs its body again, up to the end of the body, while it stops retriably and attempts are
left; when none is left, the stop is the one that the retry's `begins` gives with the
beginning; the rest runs once. Nothing here depends on a vocabulary.
-/

namespace Zkc.Core

/-! ## Handlers -/

/-- The meaning of a handler: it answers each effect of `S` by a process of `T`, from a
state; a stop carries what stops (of type `H`) and the state to report. `again i entry stop`
is the state with which attempt `i` starts, from the state at the attempt and the state where
the attempt before it stopped; it is code, and may stop. -/
structure Handler (S T : Sig) (H σ : Type) where
  clause : (op : S.Op) → σ → Process T (H × σ) (S.Reply op × σ)
  again : Nat → σ → σ → Except H σ

/-- The retry of a program's attempts. `begins` says which effect begins a retried attempt,
with the stop to give when the attempts run out and the reply for attempt `i`; `ends` says
which effect ends its body, with its reply. A stop inside the body that `retriable` accepts
starts the next attempt, at most `bound` attempts in all. In attempt `i`, what the body asks
below is marked by `mark i`. -/
structure Retry (S T : Sig) (H : Type) where
  bound : Nat
  begins : (op : S.Op) → Option (H × (Nat → S.Reply op))
  ends : (op : S.Op) → Option (S.Reply op)
  retriable : H → Bool
  mark : ∀ {H' A : Type}, Nat → Process T H' A → Process T H' A

/-- The attempts of the body of an attempt. `body i s` is attempt `i` from the state `s`, and
the rest after it; it stops with `(true, why)` inside the body and with `(false, why)` after
it. An attempt that stops inside the body with a retriable stop is followed by the next, from
the state that `again` gives, while attempts are left; when none is left, the stop is
`exhausted` (the stop that the retry's `begins` gave), with the state reached. A stop of
`again`, and a stop after the body, is the stop. -/
def attempts {T : Sig} {H σ A : Type} (retriable : H → Bool) (exhausted : H)
    (again : Nat → σ → σ → Except H σ)
    (body : Nat → σ → Process T ((Bool × H) × σ) (A × σ)) (entry : σ) :
    Nat → Nat → σ → Process T (H × σ) (A × σ)
  | 0, _, s => .halt (exhausted, s)
  | n + 1, i, s => (body i s).recover fun stop =>
      if stop.1.1 && retriable stop.1.2 then
        match n with
        | 0 => .halt (exhausted, stop.2)
        | _ + 1 =>
            match again (i + 1) entry stop.2 with
            | .ok next => attempts retriable exhausted again body entry n (i + 1) next
            | .error why => .halt (why, stop.2)
      else .halt (stop.1.2, stop.2)

mutual
  /-- The interpretation of a program by a handler, outside an attempt that is retried: the
  state is returned with the result, and is in the payload of a stop. At the beginning of a
  retried attempt, its attempts: each runs the body, up to its end, and then the rest. -/
  def Handler.run {S T : Sig} {H σ A : Type} (h : Handler S T H σ) (retry : Retry S T H) :
      Process S H A → σ → Process T (H × σ) (A × σ)
    | .done a, s => .done (a, s)
    | .halt why, s => .halt (why, s)
    | .call op k, s =>
        match retry.begins op with
        | some (exhausted, number) =>
            attempts retry.retriable exhausted h.again
              (fun i s' => Handler.inside h retry i (k (number i)) s') s retry.bound 0 s
        | none => (h.clause op s).bind fun out => Handler.run h retry (k out.1) out.2
  /-- Inside the body of attempt `i`: every effect goes to the handler's clause under the
  retry's mark for `i`, and every stop is inside the body. At the end of the body, the rest
  runs once, unmarked, and its stops are after the body. -/
  def Handler.inside {S T : Sig} {H σ A : Type} (h : Handler S T H σ) (retry : Retry S T H)
      (i : Nat) : Process S H A → σ → Process T ((Bool × H) × σ) (A × σ)
    | .done a, s => .done (a, s)
    | .halt why, s => .halt ((true, why), s)
    | .call op k, s =>
        match retry.ends op with
        | some reply =>
            (Handler.run h retry (k reply) s).mapHalt fun stop => ((false, stop.1), stop.2)
        | none =>
            ((retry.mark i (h.clause op s)).mapHalt fun stop => ((true, stop.1), stop.2)).bind
              fun out => Handler.inside h retry i (k out.1) out.2
end

/-- The interpretation of a process of `T` by a handler of `T`: at a stop of the process, the
state that it carries and the handler's state as reached; at a stop of one of the handler's
clauses, `upper` for the process and the state that the clause carries. -/
def Handler.answer {T U : Sig} {H τ X E : Type} (h : Handler T U H τ) :
    Process T (H × E) X → E → τ → Process U (H × E × τ) (X × τ)
  | .done x, _, t => .done (x, t)
  | .halt stop, _, t => .halt (stop.1, stop.2, t)
  | .call op k, upper, t =>
      ((h.clause op t).mapHalt fun stop => (stop.1, upper, stop.2)).bind fun out =>
        answer h (k out.1) upper out.2

/-- `inner` nearest the program, `outer` below it. The order is part of a deployment. At a
stop, the upper layer's state is what its clause reports (a layer's clause that stops reports
its state as before the clause), and the lower layer's state is as reached: a stop above does
not undo what was done below. -/
def Handler.over {S T U : Sig} {H σ τ : Type} (inner : Handler S T H σ) (outer : Handler T U H τ) :
    Handler S U H (σ × τ) where
  clause op st :=
    ((outer.answer (inner.clause op st.1) st.1 st.2).mapHalt fun stop =>
        (stop.1, (stop.2.1, stop.2.2))).bind fun out =>
      .done (out.1.1, (out.1.2, out.2))
  again i entry stop :=
    match inner.again i entry.1 stop.1, outer.again i entry.2 stop.2 with
    | .ok mine, .ok below => .ok (mine, below)
    | .error why, _ => .error why
    | .ok _, .error why => .error why

/-- The handler that answers nothing: every effect goes below. -/
def Handler.none (S : Sig) (H : Type) : Handler S S H Unit where
  clause op s := .call op fun reply => .done (reply, s)
  again _ _ _ := .ok ()

end Zkc.Core
