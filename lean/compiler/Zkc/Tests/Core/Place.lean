import Zkc.Core.Meaning.Place
import Zkc.Tests.Core.Shapes

/-!
Places inside a term, with their meaning, on terms of a dialect of truth values written by hand.

The dialect is written here: the toy dialect of `Following.lean` has no condition, so no
guard, and a function has no attempt. Its values are truth values, it has no effect, a guard
holds when its condition is true, and an attempt has the number `false`.

Replacement (`Hole.fill_same`): a value that nothing uses dropped from the body of a loop inside
an attempt, the two wholes meaning the same on every environment; there too, the input read for
the carried value, which differs from it on environments of the body that no run reaches, since
the loop carries the input in each iteration; a replacement after a guard that differs from the
original only where the guard stops, accepted on every environment; and the control, a
replacement after the same guard that differs where the guard holds: the premise of replacement
fails for it, and the two wholes do not mean the same on that input. Then the
names that a term reads (`Term.denote_reads`): a term means the same in two environments that
agree on what it reads, and gives different results in two that differ there. Then the split of
a term (`Term.fill_splitAt`), after two of its three instructions and after seven, which is all
of them; and the structural rule on contexts, for the meaning (`Term.denote_reindex`), with the
control of an environment that does not agree, on which the meaning differs, and for the erased
form (`eraseBody_reindex`). The split and the erased form are equalities without a premise, so
they have no control: their tests compare what is computed.
-/

namespace Zkc.Core.PlaceTests

/-! ## A dialect of truth values -/

/-- The operations: a written truth value, and the negation. -/
inductive BitOp : List Unit → List Unit → Type where
  | constant (value : Bool) : BitOp [] [()]
  | negation : BitOp [()] [()]

/-- The written forms of the operations. -/
inductive BitRaw where
  | constant (value : Bool)
  | negation

/-- The written form of an operation. -/
def BitOp.print {ins res : List Unit} : BitOp ins res → BitRaw
  | .constant value => .constant value
  | .negation => .negation

/-- A dialect of one type, which anyone may guard and choose on; loops of a written number of
iterations, attempts that anyone may own, and no variant or count. -/
@[reducible] def bits : Dialect where
  Ty := Unit
  Op := BitOp
  Who := Unit
  Condition _ _ := True
  Alternatives _ _ _ := False
  Count _ _ := False
  index _ := ()
  Attempt _ := True
  Gives _ _ := True
  collected _ _ := ()

/-- Its semantics: values are truth values; no effect; a guard holds when its condition is
`true`, and stops with its reason; an attempt has the number `false` and ends at once; what a
loop collects is `false`. -/
def bitsSem : Semantics bits where
  Val _ := Bool
  S := NoSig
  H := Reason
  op := fun {_ _} _ o _ values => match o, values with
    | .constant value, _ => .done (.cons value .nil)
    | .negation, .cons v .nil => .done (.cons (!v) .nil)
  holds := fun {_ _} _ v => v
  stop := fun _ why _ => why
  pick := fun {_ _ _} ok _ => nomatch ok
  count := fun {_ _} ok _ => nomatch ok
  index := fun _ _ => false
  begin := fun _ _ _ => .done false
  settle := fun _ _ _ => .done ()
  collect := fun _ _ _ => false

/-- Every reply is permitted: there is none. -/
abbrev any : ∀ op, bitsSem.S.Reply op → Prop := fun _ _ => True

/-- One input, the name `0`. -/
abbrev one : Ctx Unit := Ctx.positional [()]

/-- Two inputs, the names `0` and `1`. -/
abbrev two : Ctx Unit := Ctx.positional [(), ()]

/-- The input `true`. -/
def withTrue : Env bitsSem.Val one := Env.positional (.cons true .nil)

/-- The input `false`. -/
def withFalse : Env bitsSem.Val one := Env.positional (.cons false .nil)

/-- The erased form of a term of the dialect: its instructions and its exit, by names. -/
def erased {Γ : Ctx Unit} {outs : List Unit} (t : Term bits Γ outs) :
    List (Instruction BitRaw Unit) × List Name :=
  eraseBody (fun o => BitOp.print o) (fun _ => ()) t

/-! ## Replacement inside a loop inside an attempt -/

/-- The context of the body of the loop below: the input `0`, the number `10` of the attempt,
the iteration number `20` and the carried value `21`. -/
abbrev inLoop : Ctx Unit :=
  (one.extend (types := [()]) (.cons 10 .nil)).extend (types := [(), ()]) (.cons 20 (.cons 21 .nil))

/-- An attempt whose body is a loop of two iterations that carries the input, with the body of
the loop left open; the attempt gives what the loop gives. -/
def loopInAttempt : Hole bits one [()] inLoop [()] :=
  .inAttempt ⟨1⟩ () trivial (.cons 10 .nil)
    (.inLoop (each := []) ⟨2⟩ () (.fixed 2) (fun _ _ => trivial) (.cons (var 0) .nil)
      (.cons 20 (.cons 21 .nil)) .here (.cons 30 .nil) (.ret (.cons (var 30) .nil)))
    (.cons 40 .nil) (.ret (.cons (var 40) .nil))

/-- In the body of the loop: a written value that nothing uses, then the carried value. -/
def withUnused : Term bits inLoop [()] :=
  .op ⟨3⟩ (BitOp.constant true) .nil (.cons 22 .nil) (.ret (.cons (var 21) .nil))

/-- In the body of the loop: the carried value. -/
def withoutUnused : Term bits inLoop [()] := .ret (.cons (var 21) .nil)

/-- The value that nothing uses, dropped from the body of the loop: the two wholes mean the same
on every environment, since the two bodies mean the same with every environment with which a run
reaches the place. -/
example (path : List Frame) (env : Env bitsSem.Val one) :
    Process.SameWhen any ((loopInAttempt.fill withUnused).denote bitsSem path env)
      ((loopInAttempt.fill withoutUnused).denote bitsSem path env) :=
  Hole.fill_same bitsSem any loopInAttempt withUnused withoutUnused path env
    fun _ _ _ => .refl _

/-- In the body of the loop: the input. -/
def readsLoopInput : Term bits inLoop [()] := .ret (.cons (var 0) .nil)

/-- The input for the carried value in the body of the loop: the two differ on environments of
the body, but every run reaches the place with the carried value equal to the input, in each of
the two iterations, since the body gives back what it carries. Replacement accepts them, by the
environments with which a run reaches the place inside the loop. -/
example (path : List Frame) (env : Env bitsSem.Val one) :
    Process.SameWhen any ((loopInAttempt.fill withoutUnused).denote bitsSem path env)
      ((loopInAttempt.fill readsLoopInput).denote bitsSem path env) :=
  Hole.fill_same bitsSem any loopInAttempt withoutUnused readsLoopInput path env (by
    rintro _ _ ⟨_, -, iteration, ⟨⟨carried, ⟨⟩⟩, _⟩, below, returns, -, rfl⟩
    match iteration, below with
    | 0, _ =>
        cases returns
        exact .refl _
    | 1, _ =>
        cases returns
        exact .refl _
    | later + 2, below =>
        have twoIterations : later + 2 < 2 := below
        omega)

/-- An environment of the body of the loop whose carried value is not the input. -/
def carriedApart : Env bitsSem.Val inLoop :=
  (withTrue.extend (types := [()]) (.cons 10 .nil) (.cons false .nil)).extend
    (types := [(), ()]) (.cons 20 (.cons 21 .nil)) (.cons false (.cons false .nil))

/-- The two do differ there, which no run reaches. -/
example : ¬ Process.SameWhen any (withoutUnused.denote bitsSem [] carriedApart)
    (readsLoopInput.denote bitsSem [] carriedApart) := by
  intro same
  cases same

/-! ## Replacement after a guard, and its control -/

/-- A guard on the input, with what follows it left open. -/
def afterGuard : Hole bits one [()] one [()] :=
  .guard ⟨1⟩ () (var 0) trivial .reject .here

/-- What follows: the input. -/
def readsInput : Term bits one [()] := .ret (.cons (var 0) .nil)

/-- What follows: a written `true`. -/
def writesTrue : Term bits one [()] :=
  .op ⟨2⟩ (BitOp.constant true) .nil (.cons 5 .nil) (.ret (.cons (var 5) .nil))

/-- What follows: a written `false`. -/
def writesFalse : Term bits one [()] :=
  .op ⟨2⟩ (BitOp.constant false) .nil (.cons 5 .nil) (.ret (.cons (var 5) .nil))

/-- Where the input is `true`, reading it and writing `true` mean the same. -/
theorem readsInput_writesTrue (path : List Frame) (env : Env bitsSem.Val one)
    (holds : env.get (var 0 : Var one ()) = true) :
    Process.SameWhen any (readsInput.denote bitsSem path env)
      (writesTrue.denote bitsSem path env) := by
  have reads : readsInput.denote bitsSem path env = .done (.cons (env.get (var 0)) .nil) := rfl
  have writes : writesTrue.denote bitsSem path env = .done (.cons true .nil) := rfl
  rw [reads, writes, holds]
  exact .refl _

/-- Written `true` for the input after the guard: the two differ only where the input is
`false`, where the guard stops and no run reaches the place. Replacement accepts them: the
wholes mean the same on every environment. -/
example (path : List Frame) (env : Env bitsSem.Val one) :
    Process.SameWhen any ((afterGuard.fill readsInput).denote bitsSem path env)
      ((afterGuard.fill writesTrue).denote bitsSem path env) :=
  Hole.fill_same bitsSem any afterGuard readsInput writesTrue path env
    fun path' _ ⟨holds, _, reached⟩ => by
      rw [reached]
      exact readsInput_writesTrue path' env holds

/-- The two do differ where the input is `false`: reading it gives `false`. -/
example : ¬ Process.SameWhen any (readsInput.denote bitsSem [] withFalse)
    (writesTrue.denote bitsSem [] withFalse) := by
  intro same
  cases same

/-- There, both wholes stop at the guard. -/
example : (afterGuard.fill readsInput).denote bitsSem [] withFalse = .halt .reject ∧
    (afterGuard.fill writesTrue).denote bitsSem [] withFalse = .halt .reject := ⟨rfl, rfl⟩

/-- Control: written `false` for the input after the guard differs where a run reaches the
place, on the input `true`. The premise of replacement fails there. -/
example : ¬ afterGuard.Holds bitsSem any readsInput [] withTrue fun path' env' =>
    Process.SameWhen any (readsInput.denote bitsSem path' env')
      (writesFalse.denote bitsSem path' env') := by
  intro holds
  have same := holds [] withTrue (And.intro rfl (And.intro rfl rfl))
  cases same

/-- And the two wholes do not mean the same on the input `true`: one gives `true`, the other
`false`. -/
example : ¬ Process.SameWhen any ((afterGuard.fill readsInput).denote bitsSem [] withTrue)
    ((afterGuard.fill writesFalse).denote bitsSem [] withTrue) := by
  intro same
  cases same

/-! ## The names that a term reads -/

/-- The negation of the first of two inputs. -/
def negated : Term bits two [()] :=
  .op ⟨1⟩ BitOp.negation (.cons (var 0) .nil) (.cons 5 .nil) (.ret (.cons (var 5) .nil))

/-- It reads the first input, and not the name `5`, which it binds. -/
theorem negated_reads : negated.reads = [0] := by decide +kernel

/-- Two inputs. -/
def inputs (first second : Bool) : Env bitsSem.Val two :=
  Env.positional (.cons first (.cons second .nil))

/-- In two environments that agree on the first input and differ on the second, the term means
the same. -/
example : negated.denote bitsSem [] (inputs true false) =
    negated.denote bitsSem [] (inputs true true) :=
  Term.denote_reads bitsSem negated [] _ _ fun name read _ _ => by
    rw [negated_reads, List.mem_singleton] at read
    subst read
    rfl

/-- Control: in two environments that differ on the first input, which it reads, it gives
`false` in one and `true` in the other. -/
example : negated.denote bitsSem [] (inputs true false) = .done (.cons false .nil) ∧
    negated.denote bitsSem [] (inputs false false) = .done (.cons true .nil) := ⟨rfl, rfl⟩

example : negated.denote bitsSem [] (inputs true false) ≠
    negated.denote bitsSem [] (inputs false false) := by
  intro same
  cases same

/-! ## What follows some instructions -/

/-- Three instructions: the negation of the first input, a guard on it, and the negation of the
second input; then both negations. -/
def threeSteps : Term bits two [(), ()] :=
  .op ⟨1⟩ BitOp.negation (.cons (var 0) .nil) (.cons 5 .nil) <|
  .guard ⟨2⟩ () (var 5) trivial .reject <|
  .op ⟨3⟩ BitOp.negation (.cons (var 1) .nil) (.cons 6 .nil) <|
  .ret (.cons (var 5) (.cons (var 6) .nil))

/-- After two instructions, what follows them is the last negation and the exit. -/
example : erased (threeSteps.splitAt 2).2.2 = ([.op ⟨3⟩ [6] .negation [1]], [5, 6]) := rfl

/-- The term is its first two instructions with what follows them filled in. -/
example : (threeSteps.splitAt 2).2.1.fill (threeSteps.splitAt 2).2.2 = threeSteps :=
  Term.fill_splitAt 2 threeSteps

/-- Seven instructions asked for, of three: the open place is after all of them, and what
follows them is the exit alone. -/
example : erased (threeSteps.splitAt 7).2.2 = ([], [5, 6]) := rfl

example : (threeSteps.splitAt 7).2.1.fill (threeSteps.splitAt 7).2.2 = threeSteps :=
  Term.fill_splitAt 7 threeSteps

/-! ## The structural rule on contexts -/

/-- The context of the input with the name `1` bound as well. -/
abbrev wider : Ctx Unit := one.insert 1 ()

/-- The context of the input is within it: the name `1` is fresh. -/
theorem keeps : one.Within wider := Ctx.Within.fresh rfl ()

/-- The attempt around the loop, with the value that nothing uses in its body. -/
def whole : Term bits one [()] := loopInAttempt.fill withUnused

/-- The input `true`, with `false` at the name `1`, agrees with the input `true`. -/
theorem agrees : Env.Agrees keeps (withTrue.insert 1 (τ := ()) false) withTrue := by
  intro name τ found
  by_cases same : name = 1
  · subst same
    exact nomatch found
  · exact Env.insert_at_other withTrue 1 false same _

/-- The whole in the wider context, on the environment that agrees, means what it means. -/
example : (whole.reindex keeps).denote bitsSem [] (withTrue.insert 1 (τ := ()) false) =
    whole.denote bitsSem [] withTrue :=
  Term.denote_reindex bitsSem keeps whole [] agrees

/-- Which is to return the input. -/
theorem whole_returns : whole.denote bitsSem [] withTrue = .done (.cons true .nil) := rfl

/-- Control: the input `false`, with `false` at the name `1`, does not agree with the input
`true`, at the name `0`. -/
example : ¬ Env.Agrees keeps (withFalse.insert 1 (τ := ()) false) withTrue := by
  intro agree
  have atInput := agree 0 () rfl
  cases atInput

/-- And on it the whole in the wider context returns `false`. -/
theorem wider_returns :
    (whole.reindex keeps).denote bitsSem [] (withFalse.insert 1 (τ := ()) false) =
      .done (.cons false .nil) := rfl

/-- Which is not what the whole returns on the input `true`. -/
example : (whole.reindex keeps).denote bitsSem [] (withFalse.insert 1 (τ := ()) false) ≠
    whole.denote bitsSem [] withTrue := by
  rw [wider_returns, whole_returns]
  intro same
  cases same

/-- The whole in the wider context erases to the same program by names. -/
example : erased (whole.reindex keeps) = erased whole := eraseBody_reindex _ _ keeps whole

/-- Which is the attempt around the loop, with its names. -/
example : erased whole = ([.attempt ⟨1⟩ () [40] (.mk [10] [
    .loop ⟨2⟩ () (.fixed 2) [0] [30] (.mk [20, 21] [.op ⟨3⟩ [22] (.constant true) []] [21])]
    [30])], [40]) := rfl

end Zkc.Core.PlaceTests
