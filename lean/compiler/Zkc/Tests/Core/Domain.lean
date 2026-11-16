import Zkc.Core.Facts.Theorems

/-!
The domain of an operation that is kept in order, what an operation kept in order guarantees,
and a body analysed under a summary, on a dialect written here.

The dialect has two types, a natural and a positive natural, and four operations, each kept in
order. The decrement, from either type to a natural, has a domain and an effect: on zero it stops
`undefined`; otherwise it asks the world one question, ignores the reply, and returns its operand
less one; its written form requires its operand to be at least one. The half of a natural asks
the world one question and returns the half of its operand, rounded down; its written form
guarantees that its result is at most its operand. The opaque half computes the same, and its
written form guarantees nothing. The subtraction of a natural from a natural stops `undefined`
when the second is larger, and otherwise returns the first less the second; its written form
requires the second to be at most the first. The rules are lawful for the semantics, with every
law and for every permitted reply (`domainRules_lawful`): the law `effect` holds because the
requirements are asked of the operands, and because the half of a natural is at most the natural.

The decrement applied to a positive input: the check of facts accepts, and the soundness of the
analysis (`Analysis.analyse_sound`) gives that it never stops `undefined`. Applied to a natural
input: refused at the operation, with the requirement that is not justified and what was known of
the operand. The control on the semantics: on the input zero the term on naturals stops
`undefined`, so the refusal keeps out a term that does; on a positive input the term asks its
question, then returns. Following: the term on positive naturals with other names follows the
first and is accepted, so the requirement is decided while following too.

Under a summary: the decrement applied to a natural input, under the summary that requires the
input to be at least one, is accepted, and satisfies the summary (`Analysis.analyse_holds`);
the input zero, on which it stops `undefined`, is excluded by the summary's requirement. A body
that returns its input, under a summary that guarantees the result to be at least one, is
accepted when the summary also requires the input to be at least one, and refused at the
definition's exit by the rule `guarantee` when it does not. And a guarantee learned at an
application: the subtraction of the half of the input from the input is accepted, since what the
half guarantees is learned where it returns, and refused with the opaque half.
-/

namespace Zkc.Core.DomainTests

-- What the check of facts returns is compared whole.
deriving instance DecidableEq for Except

/-! ## A dialect with operations that have domains, effects and guarantees -/

/-- The types: a natural, and a positive natural. -/
inductive DomainTy where
  | natural
  | positive
deriving DecidableEq, Repr

/-- The operations: the decrement, from a natural or a positive natural to a natural; the half
of a natural, with and without a guarantee; and the subtraction of a natural from a natural. -/
inductive DomainOp : List DomainTy → List DomainTy → Type where
  | decrement (operand : DomainTy) : DomainOp [operand] [.natural]
  | half : DomainOp [.natural] [.natural]
  | opaqueHalf : DomainOp [.natural] [.natural]
  | subtract : DomainOp [.natural, .natural] [.natural]

/-- The written forms of the operations: the decrement whatever the type of its operand. -/
inductive DomainRaw where
  | decrement
  | half
  | opaqueHalf
  | subtract
deriving DecidableEq, Repr

/-- The written form of an operation. -/
def domainWritten : ∀ {ins res : List DomainTy}, DomainOp ins res → DomainRaw
  | _, _, .decrement _ => .decrement
  | _, _, .half => .half
  | _, _, .opaqueHalf => .opaqueHalf
  | _, _, .subtract => .subtract

/-- A dialect of the two types, with one performer and no condition, variant, count or attempt;
the number of an iteration is a natural, and so is what a loop collects. -/
@[reducible] def domainDialect : Dialect where
  Ty := DomainTy
  Op := DomainOp
  Who := Unit
  Condition _ _ := False
  Alternatives _ _ _ := False
  Count _ _ := False
  index _ := .natural
  Attempt _ := False
  Gives _ _ := False
  collected _ _ := .natural

/-- Its semantics: values are naturals; the decrement stops `undefined` on zero, and otherwise
asks the world one question, whose reply is a truth value that it ignores, and returns its operand
less one; either half asks one question and returns the half of its operand, rounded down; the
subtraction stops `undefined` when the second is larger than the first, and otherwise returns the
first less the second; a guard stops with its reason, declared. -/
@[reducible] def domainSem : Semantics domainDialect where
  Val _ := Nat
  S := ⟨Unit, fun _ => Bool⟩
  H := Stop
  op := fun {_ _} _ o _ values => match o, values with
    | .decrement _, .cons n .nil =>
        if n = 0 then .halt .undefined else .call () fun _ => .done (.cons (n - 1) .nil)
    | .half, .cons n .nil => .call () fun _ => .done (.cons (n / 2) .nil)
    | .opaqueHalf, .cons n .nil => .call () fun _ => .done (.cons (n / 2) .nil)
    | .subtract, .cons first (.cons second .nil) =>
        if second ≤ first then .done (.cons (first - second) .nil) else .halt .undefined
  holds := fun {_ _} ok _ => nomatch ok
  stop := fun _ why occurrence => .declared why occurrence
  pick := fun {_ _ _} ok _ => nomatch ok
  count := fun {_ _} ok _ => nomatch ok
  index := fun _ i => i
  begin := fun _ _ _ => .done 0
  settle := fun _ _ _ => .done ()
  collect := fun _ _ _ => 0

/-- A natural is valid; a positive natural is valid when it is at least one. -/
def domainValid : domainSem.Dyn → Prop
  | ⟨.natural, _⟩ => True
  | ⟨.positive, n⟩ => 1 ≤ n

/-- How a value reads: as the natural that it is. -/
def domainReading : Reading domainSem.Dyn where
  nat value := some value.2
  bool _ := none

/-- The relation of written operations: empty, since no operation is shared and no requirement or
guarantee names an application. -/
def domainRun : DomainRaw → List domainSem.Dyn → List domainSem.Dyn → Prop := fun _ _ _ => False

/-- The rules: every operation is kept in order; the decrement requires its operand to be at
least one, the subtraction its second operand to be at most its first, and the half guarantees
that its result is at most its operand; the opaque half guarantees nothing; a natural is at least
zero, a positive natural at least one; nothing commutes, no type is without value, and nothing is
known of a result beyond what its type and its operation's guarantee say. -/
def domainRules : FactRules domainDialect DomainRaw where
  written := domainWritten
  shared := fun _ => false
  commutes := fun _ => false
  range
    | .natural => some ⟨0, none⟩
    | .positive => some ⟨1, none⟩
  noValue := fun _ => false
  ops :=
    { requires
        | .decrement => [.atLeast (.arg 0) 1]
        | .subtract => [.le (.arg 1) (.arg 0)]
        | _ => []
      ensures
        | .half => [.le (.arg 1) (.arg 0)]
        | _ => []
      ranges := fun _ _ => []
      form := fun _ => none }
  place := fun _ => 0

/-- Following decides types and performers by equality, and two operations on operands of the
same types by their written forms, which with those types name them. -/
def domainChecks : SkelRules domainDialect where
  sameTy := inferInstanceAs (DecidableEq DomainTy)
  sameWho := inferInstanceAs (DecidableEq Unit)
  sameOp := fun o o' => domainWritten o == domainWritten o'

/-- On a natural that is not zero, the decrement asks its question, then returns the natural less
one. -/
theorem decrement_nonzero (τ : DomainTy) (key : Key) (path : List Frame) (n : Nat)
    (nonzero : n ≠ 0) :
    domainSem.op key (DomainOp.decrement τ) path (.cons n .nil) =
      .call () fun _ => .done (.cons (n - 1) .nil) := by
  simp only [domainSem, nonzero, ↓reduceIte]

/-- On a second natural at most the first, the subtraction returns the first less the second. -/
theorem subtract_within (key : Key) (path : List Frame) (first second : Nat)
    (within : second ≤ first) :
    domainSem.op key DomainOp.subtract path (.cons first (.cons second .nil)) =
      .done (.cons (first - second) .nil) := by
  simp only [domainSem, within, ↓reduceIte]

/-- Operations that following finds the same are the same. -/
theorem domainChecks_lawful : domainChecks.Lawful := by
  intro ins res res' o o' same
  cases o <;> cases o' <;> first | exact ⟨rfl, HEq.rfl⟩ | exact absurd same (by decide)

/-- **The rules of the dialect are lawful for its semantics**, for every permitted reply: with
`domainRun`, the validity `domainValid`, the reading `domainReading` and the stop `undefined`. The
law `effect` holds because an operation is applied only where its requirement holds (the operand
of the decrement is at least one, the second operand of the subtraction at most the first), and
because the half of a natural is at most the natural. -/
theorem domainRules_lawful (permitted : ∀ op, domainSem.S.Reply op → Prop) :
    domainRules.Lawful domainSem permitted domainReading domainRun domainValid
      (· = .undefined) where
  binding :=
    { computes := fun o raw written => by
        cases (domainRules.values_written_kept (o := o) rfl).symm.trans written
      functional := fun _ _ _ _ ran => ran.elim
      commutative := fun _ _ _ _ _ ran => ran.elim }
  ops :=
    { functional := fun _ _ _ _ ran => ran.1.elim
      form := fun _ _ _ _ _ ran => ran.1.elim
      ranges := fun _ _ _ _ ran => ran.1.elim
      ensures := fun _ _ _ ran => ran.1.elim }
  keeps := fun _ _ _ ran => ran.elim
  defined := fun _ shared => by cases shared
  named := by
    intro ins res o values _ requirement listed operand named written positions applied
    subst applied
    cases o <;>
      simp only [domainRules, domainWritten, List.mem_singleton, List.not_mem_nil] at listed <;>
      subst listed <;>
      simp [Requirement.operands] at named
  effect := by
    intro ins res o _ key path values _ required
    cases o with
    | decrement τ =>
        obtain ⟨n, rfl⟩ := HList.one values
        obtain ⟨vs, denoted, relation⟩ := required (.atLeast (.arg 0) 1)
          (by simp only [domainRules, domainWritten, List.mem_singleton])
        obtain ⟨v, rfl, at0⟩ := DenotesAll.one denoted
        have read : v = ⟨τ, n⟩ :=
          (Option.some.inj (show (some ⟨τ, n⟩ : Option domainSem.Dyn) = some v from at0)).symm
        subst read
        have positive : 1 ≤ (n : Nat) := relation n rfl
        rw [decrement_nonzero τ key path n (Nat.pos_iff_ne_zero.mp positive)]
        intro _ _
        refine ⟨fun v returned => ?_, fun _ listed => nomatch listed⟩
        cases returned with
        | head => trivial
        | tail _ rest => cases rest
    | half =>
        obtain ⟨n, rfl⟩ := HList.one values
        intro _ _
        refine ⟨fun v returned => ?_, fun guarantee listed => ?_⟩
        · cases returned with
          | head => trivial
          | tail _ rest => cases rest
        · simp only [domainRules, domainWritten, List.mem_singleton] at listed
          subst listed
          refine ⟨[⟨.natural, n / 2⟩, ⟨.natural, n⟩], ⟨rfl, rfl, trivial⟩, ?_⟩
          intro x y hx hy
          cases hx
          cases hy
          exact Nat.div_le_self n 2
    | opaqueHalf =>
        obtain ⟨n, rfl⟩ := HList.one values
        intro _ _
        refine ⟨fun v returned => ?_, fun _ listed => nomatch listed⟩
        cases returned with
        | head => trivial
        | tail _ rest => cases rest
    | subtract =>
        cases values with
        | cons first rest =>
            cases rest with
            | cons second rest =>
                cases rest
                obtain ⟨vs, denoted, relation⟩ := required (.le (.arg 1) (.arg 0))
                  (by simp only [domainRules, domainWritten, List.mem_singleton])
                obtain ⟨v, v', rfl, at1, at0⟩ := DenotesAll.two denoted
                cases at1
                cases at0
                have within : second ≤ first := relation second first rfl rfl
                rw [subtract_within key path first second within]
                refine ⟨fun v returned => ?_, fun _ listed => nomatch listed⟩
                cases returned with
                | head => trivial
                | tail _ rest => cases rest
  range := by
    intro τ r v found valid
    cases τ with
    | natural =>
        simp only [domainRules, Option.some.injEq] at found
        subst found
        exact ⟨v, rfl, Nat.zero_le _, fun _ e => nomatch e⟩
    | positive =>
        simp only [domainRules, Option.some.injEq] at found
        subst found
        exact ⟨v, rfl, valid, fun _ e => nomatch e⟩
  noValue := fun _ _ _ => rfl
  condition := fun ok => nomatch ok
  count := fun ok => nomatch ok
  pick := fun ok => nomatch ok
  index := fun _ _ => ⟨trivial, rfl⟩
  collect := fun _ _ _ _ _ => trivial
  begin := fun _ _ _ => trivial
  settle := fun _ _ _ => trivial
  stop := fun _ _ _ => nofun

/-! ## The decrement applied -/

/-- The decrement applied, with the key 1, to the input `0` of the type given; its result, the
name `1`, is returned. -/
def decrementOf (τ : DomainTy) :
    Term domainDialect (Ctx.empty.extend (types := [τ]) (.cons 0 .nil)) [.natural] :=
  .op ⟨1⟩ (DomainOp.decrement τ) (.cons ⟨0, rfl⟩ .nil) (.cons 1 .nil) (.ret (.cons ⟨1, rfl⟩ .nil))

/-- On a positive input the check of facts accepts: the type says that the operand is at least
one. There is no loop, so no bound. -/
example : checkFacts domainRules domainChecks ⟨1⟩ none ⟨[], []⟩ (.cons 0 .nil)
    (decrementOf .positive) = .ok [] := by
  decide +kernel

/-- So, by the soundness of the analysis, on every valid input, which is at least one, and every
permitted reply, the decrement applied to a positive input never stops `undefined` and returns a
valid value. -/
theorem decrementPositive_safe (permitted : ∀ op, domainSem.S.Reply op → Prop) (n : Nat)
    (positive : 1 ≤ n) :
    ((decrementOf .positive).denote domainSem []
        (Env.empty.extend (.cons 0 .nil) (.cons n .nil))).Every
      permitted (fun returned => ∀ v, v ∈ domainSem.dyns returned → domainValid v)
      (fun stop => ¬ stop = .undefined) :=
  Process.every_mono _ _ (fun _ returned => returned.1) (fun _ stop => stop)
    (Analysis.analyse_sound domainRules domainChecks domainSem permitted domainReading domainRun
      domainValid (· = .undefined) (domainRules_lawful permitted) domainChecks_lawful ⟨1⟩ none
      ⟨[], []⟩ (.cons 0 .nil) (decrementOf .positive) (by unfold Term.Distinct; decide +kernel)
      (by decide +kernel) [] (fun _ _ inside => nomatch inside) (.cons n .nil)
      (fun _ inputs => by
        cases inputs with
        | head => exact positive
        | tail _ rest => cases rest)
      (fun _ listed => nomatch listed)).2.1

/-- On a natural input the check of facts refuses the decrement, at its place, with the
requirement that is not justified and what was known of its operand: at least zero. -/
example : checkFacts domainRules domainChecks ⟨1⟩ none ⟨[], []⟩ (.cons 0 .nil)
    (decrementOf .natural) =
    .error [⟨.domain, ⟨⟨1⟩, [], some ⟨1⟩, none⟩,
      .unjustified .decrement (.atLeast (.arg 0) 1) [some ⟨0, none⟩]⟩] := by
  decide +kernel

/-! ## The control on the semantics -/

/-- On the input zero, the process of the decrement applied to a natural is the stop `undefined`:
the refusal keeps out a term that stops so. -/
example : (decrementOf .natural).denote domainSem []
    (Env.empty.extend (.cons 0 .nil) (.cons (0 : Nat) .nil)) =
      .halt .undefined := rfl

/-- On a positive input, three, the process is the question, followed, whatever the reply, by the
return of two. -/
example : (decrementOf .positive).denote domainSem []
    (Env.empty.extend (.cons 0 .nil) (.cons (3 : Nat) .nil)) =
      .call () fun _ => .done (.cons (2 : Nat) .nil) := rfl

/-! ## Following -/

/-- The decrement applied to a positive input with other names: the input `5` and the result
`6`. -/
def decrementOtherNames :
    Term domainDialect (Ctx.empty.extend (types := [.positive]) (.cons 5 .nil)) [.natural] :=
  .op ⟨1⟩ (DomainOp.decrement .positive) (.cons ⟨5, rfl⟩ .nil) (.cons 6 .nil)
    (.ret (.cons ⟨6, rfl⟩ .nil))

/-- It follows the analysis of the first: the decrement is the skeleton's entry, its requirement
is decided where it is applied, and nothing is refused. The whole verdict accepts it. -/
example : (Analysis.follow domainRules domainChecks ⟨1⟩ none ⟨[], []⟩
    (Analysis.analyse domainRules domainChecks ⟨1⟩ none ⟨[], []⟩ (.cons 0 .nil)
      (decrementOf .positive))
    (.cons 5 .nil) decrementOtherNames).accepted = true := by
  decide +kernel

/-! ## A body under a summary -/

/-- The summary that requires the input to be at least one, and guarantees nothing. -/
def inputAtLeastOne : Summary DomainRaw := ⟨[.atLeast (.arg 0) 1], []⟩

/-- Under the summary that requires its input to be at least one, the decrement applied to a
natural input is accepted: the requirement is known at the start, so the requirement of the
decrement is known where it is applied. Under the summary with no requirement it is refused, as
above. -/
example : checkFacts domainRules domainChecks ⟨1⟩ none inputAtLeastOne (.cons 0 .nil)
    (decrementOf .natural) = .ok [] := by
  decide +kernel

/-- So, by the corollary of the soundness of the analysis, the decrement applied to a natural
input satisfies the summary, as a function of its input: on every valid input that is at least
one and every permitted reply, it never stops `undefined` and returns a valid value. -/
theorem decrementNatural_holds (permitted : ∀ op, domainSem.S.Reply op → Prop) :
    Summary.Holds domainSem permitted domainReading (ValidRun domainSem domainRun domainValid)
      domainValid (· = .undefined) inputAtLeastOne
      (fun values => (decrementOf .natural).denote domainSem [] (Env.empty.extend (.cons 0 .nil)
        values)) :=
  Analysis.analyse_holds domainRules domainChecks domainSem permitted domainReading domainRun
    domainValid (· = .undefined) (domainRules_lawful permitted) domainChecks_lawful ⟨1⟩ none
    inputAtLeastOne (.cons 0 .nil) (decrementOf .natural) (by unfold Term.Distinct; decide +kernel)
    (by decide +kernel)

/-- The control: the input zero, on which the decrement applied to a natural is the stop
`undefined` (above), is the one input that the summary's requirement excludes. -/
example : ¬ (Requirement.atLeast (.arg 0) 1 : Requirement DomainRaw).Holds
    (ValidRun domainSem domainRun domainValid) domainReading [⟨.natural, (0 : Nat)⟩] := by
  rintro ⟨vs, denoted, relation⟩
  obtain ⟨v, rfl, at0⟩ := DenotesAll.one denoted
  cases at0
  exact absurd (relation 0 rfl) (by decide)

/-- A body that returns its natural input, the name `0`. -/
def returnsInput :
    Term domainDialect (Ctx.empty.extend (types := [.natural]) (.cons 0 .nil)) [.natural] :=
  .ret (.cons ⟨0, rfl⟩ .nil)

/-- The summary that requires nothing and guarantees that the result is at least one. -/
def resultAtLeastOne : Summary DomainRaw := ⟨[], [.atLeast (.arg 1) 1]⟩

/-- The summary that requires the input to be at least one and guarantees that the result is. -/
def bothAtLeastOne : Summary DomainRaw := ⟨[.atLeast (.arg 0) 1], [.atLeast (.arg 1) 1]⟩

/-- A guarantee decided where the body returns: when the summary requires the input to be at least
one, the result, which is the input, is known to be at least one, and the body is accepted. -/
example : checkFacts domainRules domainChecks ⟨1⟩ none bothAtLeastOne (.cons 0 .nil)
    returnsInput = .ok [] := by
  decide +kernel

/-- When the summary requires nothing, the guarantee is not known where the body returns: refused
at the definition's exit (the place with no instruction) by the rule `guarantee`, with the
guarantee and what was known of the result: at least zero. -/
example : checkFacts domainRules domainChecks ⟨1⟩ none resultAtLeastOne (.cons 0 .nil)
    returnsInput =
    .error [⟨.guarantee, ⟨⟨1⟩, [], none, none⟩,
      .unestablished (.atLeast (.arg 1) 1) [some ⟨0, none⟩]⟩] := by
  decide +kernel

/-! ## A guarantee learned at an application -/

/-- A half, by the operation given, of the natural input `0`, with the key 1, named `1`; then the
subtraction of it from the input, with the key 2, named `2`, which is returned. -/
def subtractHalf (halve : DomainOp [.natural] [.natural]) :
    Term domainDialect (Ctx.empty.extend (types := [.natural]) (.cons 0 .nil)) [.natural] :=
  .op ⟨1⟩ halve (.cons ⟨0, rfl⟩ .nil) (.cons 1 .nil)
    (.op ⟨2⟩ DomainOp.subtract (.cons ⟨0, rfl⟩ (.cons ⟨1, rfl⟩ .nil)) (.cons 2 .nil)
      (.ret (.cons ⟨2, rfl⟩ .nil)))

/-- After the half, what it guarantees, that its result is at most its operand, is learned, and the
requirement of the subtraction follows from it: accepted. -/
example : checkFacts domainRules domainChecks ⟨1⟩ none ⟨[], []⟩ (.cons 0 .nil)
    (subtractHalf .half) = .ok [] := by
  decide +kernel

/-- After the opaque half, which computes the same and guarantees nothing, the requirement of the
subtraction is not known: refused at the subtraction, with what was known of its two operands, in
the order in which the requirement names them: each at least zero. -/
example : checkFacts domainRules domainChecks ⟨1⟩ none ⟨[], []⟩ (.cons 0 .nil)
    (subtractHalf .opaqueHalf) =
    .error [⟨.domain, ⟨⟨1⟩, [], some ⟨2⟩, none⟩,
      .unjustified .subtract (.le (.arg 1) (.arg 0)) [some ⟨0, none⟩, some ⟨0, none⟩]⟩] := by
  decide +kernel

end Zkc.Core.DomainTests
