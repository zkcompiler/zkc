module

public import Zkc.Core.ThreadRules

public section

/-! Reading what an entry emits around its threaded body.

- `Operands.eval_newest`, `Operands.eval_inputs`: the operands that name the values bound
  last evaluate to those values.
- `Operands.eval_extend`: operands in an extension of their context evaluate as before,
  in an environment that holds every earlier value where it was.
- `Emitted.Gives`: an emitted sequence runs as a process of something that is read in the
  environment it leaves. The sequence may bind more values than the process returns. A
  region that follows it and reads only the earlier values and what the process returns
  runs after the process (`Emitted.Gives.wrap_denote`); a sequence that gives a process,
  followed by one that yields a process, gives what is read after the second
  (`Emitted.Gives.andThen`).
- `PIR.Process.Quiet.done`, `PIR.Process.Quiet.halt`: a process that returns or stops
  performs no effect.

The module reads the bodies of `Operands.extend` and `PIR.Process.Quiet`, which their
modules do not expose.
-/

set_option autoImplicit false

namespace PIR

variable {I : Signature} {A : Type}

/-- A process that returns performs no effect. -/
theorem Process.Quiet.done (value : A) : (Process.done value : Process I A).Quiet := trivial

/-- A process that stops performs no effect. -/
theorem Process.Quiet.halt (why : Stop) : (Process.halt why : Process I A).Quiet := trivial

end PIR

namespace Zkc.Source

namespace Operands

variable {Ty : Type} {Value : Ty → Type}

/-- The operands that name the values bound last evaluate to those values. -/
theorem eval_newest :
    ∀ (added : List Ty) {Γ : List Ty} (env : Environment Value Γ) (values : Values Value added),
      Operands.eval (Environment.bindAll env values) (Operands.newest added) = values
  | [], _, _, .nil => rfl
  | ty :: rest, Γ, env, .cons value values => by
      show Values.cons (Environment.bindAll (env.push value) values
          ((Var.here : Var (ty :: Γ) ty).weaken rest))
        (Operands.eval (Environment.bindAll (env.push value) values) (Operands.newest rest)) = _
      rw [Environment.bindAll_weaken, eval_newest rest]
      rfl

/-- The operands that name the inputs of a closed region evaluate to the inputs. -/
theorem eval_inputs (inputs : List Ty) (values : Values Value inputs) :
    Operands.eval (Environment.ofValues values) (Operands.newest inputs) = values :=
  eval_newest inputs Environment.empty values

/-- Operands in an extension of their context evaluate as before. -/
theorem eval_extend {Δ Δ' : List Ty} (grows : Extends Δ Δ') (env : Environment Value Δ)
    (later : Environment Value Δ')
    (keeps : ∀ {ty : Ty} (reference : Var Δ ty), later (reference.extend grows) = env reference) :
    ∀ {types : List Ty} (operands : Operands Δ types),
      Operands.eval later (operands.extend grows) = Operands.eval env operands
  | _, .nil => by
      unfold Operands.extend
      rfl
  | _, .cons reference rest => by
      unfold Operands.extend
      exact congr (congrArg Values.cons (keeps reference)) (eval_extend grows env later keeps rest)

end Operands

variable {dialect : Dialect} {I : PIR.Signature} {Δ : List dialect.Ty}

/-- A value of a context read after two extensions is the value read after their
composition. -/
theorem Var.extend_trans {α : Type} {Γ Γ' Γ'' : List α} {ty : α} (reference : Var Γ ty)
    (first : Extends Γ Γ') (second : Extends Γ' Γ'') :
    reference.extend (first.trans second) = (reference.extend first).extend second :=
  Var.ext (Nat.add_assoc ..).symm

/-- An emitted sequence runs as a process of what `read` finds in the environment the
sequence leaves, and that environment holds every earlier value where it was. -/
@[expose] def Emitted.Gives {results : List dialect.Ty} (emitted : Emitted dialect Δ results)
    (meaning : RegionMeaning dialect I) (env : Environment meaning.Value Δ) {A : Type}
    (process : PIR.Process I A) (read : Environment meaning.Value emitted.context → A) : Prop :=
  ∃ (R : Type) (full : PIR.Process I R) (later : R → Environment meaning.Value emitted.context),
    emitted.Yields meaning env full later ∧
      process = full.bind fun result => .done (read (later result))

namespace Emitted

/-- A region after a sequence that reads only the earlier values and what the sequence
gives runs after the sequence's process. -/
theorem Gives.wrap_denote {results out : List dialect.Ty} {meaning : RegionMeaning dialect I}
    {emitted : Emitted dialect Δ results} {env : Environment meaning.Value Δ} {A : Type}
    {process : PIR.Process I A} {read : Environment meaning.Value emitted.context → A}
    (gives : emitted.Gives meaning env process read) (next : Region dialect emitted.context out)
    (after : A → PIR.Process I (Values meaning.Value out))
    (reads : ∀ later : Environment meaning.Value emitted.context,
      (∀ {ty : dialect.Ty} (reference : Var Δ ty),
        later (reference.extend emitted.grows) = env reference) →
      next.denote meaning later = after (read later)) :
    (emitted.wrap next).denote meaning env = process.bind after := by
  obtain ⟨R, full, later, yields, same⟩ := gives
  subst same
  refine (yields.runs next).trans ?_
  simp only [PIR.Process.bind_assoc, PIR.Process.done_bind]
  congr 1
  funext result
  exact reads (later result) (yields.keeps result)

/-- A sequence that gives a process, then a second one that yields a process in every
environment: together they give the first process followed by a process that the second
one's is, in the environments the first may leave. -/
theorem Gives.andThen {first second results : List dialect.Ty} {meaning : RegionMeaning dialect I}
    {before : Emitted dialect Δ first} {after : Emitted dialect before.context second}
    {env : Environment meaning.Value Δ} {A B S : Type} {process : PIR.Process I A}
    {readBefore : Environment meaning.Value before.context → A}
    {next : A → PIR.Process I B} {readAfter : Environment meaning.Value after.context → B}
    {fullAfter : Environment meaning.Value before.context → PIR.Process I S}
    {laterAfter : Environment meaning.Value before.context → S →
      Environment meaning.Value after.context}
    (givesBefore : before.Gives meaning env process readBefore)
    (yieldsAfter : ∀ middle : Environment meaning.Value before.context,
      after.Yields meaning middle (fullAfter middle) (laterAfter middle))
    (same : ∀ middle : Environment meaning.Value before.context,
      (∀ {ty : dialect.Ty} (reference : Var Δ ty),
        middle (reference.extend before.grows) = env reference) →
      next (readBefore middle) =
        (fullAfter middle).bind fun last => .done (readAfter (laterAfter middle last)))
    (values : Operands after.context results) :
    (before.andThen after values).Gives meaning env (process.bind next) readAfter := by
  obtain ⟨R, full, later, yields, given⟩ := givesBefore
  subst given
  refine ⟨R × S, _, _, yields.andThen (fun result => yieldsAfter (later result)) values, ?_⟩
  simp only [PIR.Process.bind_assoc, PIR.Process.done_bind]
  congr 1
  funext result
  exact same (later result) (yields.keeps result)

end Emitted

end Zkc.Source
