import Zkc.Core.Facts.Theorems

/-!
The domain of an operation that is kept in order, on a dialect written here.

The dialect has two types, a natural and a positive natural, and one operation, from either to a
natural, which has a domain and an effect: on zero it stops `undefined`; otherwise it asks the
world one question, ignores the reply, and returns its operand less one. It is not shared, so it
is kept in order, and its written form requires its operand to be at least one. Its rules are
lawful for its semantics, with every law and for every permitted reply (`domainRules_lawful`):
the law `effect` holds because the requirement is asked of the operand.

The operation applied to a positive input: the check of facts accepts, and the soundness of the
analysis (`Analysis.analyse_sound`) gives that it never stops `undefined`. Applied to a natural
input: refused at the operation, with the requirement that is not justified and what was known of
the operand. The control on the semantics: on the input zero the term on naturals stops
`undefined`, so the refusal keeps out a term that does; on a positive input the term asks its
question, then returns. And following: the term on positive naturals with other names follows the
first and is accepted, so the requirement is decided while following too.
-/

namespace Zkc.Core.DomainTests

-- What the check of facts returns is compared whole.
deriving instance DecidableEq for Except

/-! ## A dialect with an operation that has a domain and an effect -/

/-- The types: a natural, and a positive natural. -/
inductive DomainTy where
  | natural
  | positive
deriving DecidableEq, Repr

/-- The operation: from a natural or a positive natural to a natural. -/
inductive DomainOp : List DomainTy → List DomainTy → Type where
  | decrement (operand : DomainTy) : DomainOp [operand] [.natural]

/-- The written form of the operation, whatever the type of its operand. -/
inductive DomainRaw where
  | decrement
deriving DecidableEq, Repr

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

/-- Its semantics: values are naturals; the operation stops `undefined` on zero, and otherwise
asks the world one question, whose reply is a truth value that it ignores, and returns its
operand less one; a guard stops with its reason, declared. -/
@[reducible] def domainSem : Semantics domainDialect where
  Val _ := Nat
  S := ⟨Unit, fun _ => Bool⟩
  H := Stop
  op := fun {_ _} _ o _ values => match o, values with
    | .decrement _, .cons n .nil =>
        if n = 0 then .halt .undefined else .call () fun _ => .done (.cons (n - 1) .nil)
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

/-- The relation of written operations: empty, since no operation is shared and no requirement
names an application. -/
def domainRun : DomainRaw → List domainSem.Dyn → List domainSem.Dyn → Prop := fun _ _ _ => False

/-- The rules: the operation is kept in order, and its written form requires its operand to be at
least one; a natural is at least zero, a positive natural at least one; nothing commutes, no type
is without value, and nothing is known of a result. -/
def domainRules : FactRules domainDialect DomainRaw where
  written := fun _ => .decrement
  shared := fun _ => false
  commutes := fun _ => false
  range
    | .natural => some ⟨0, none⟩
    | .positive => some ⟨1, none⟩
  noValue := fun _ => false
  ops := ⟨fun | .decrement => [.atLeast (.arg 0) 1], fun _ _ => [], fun _ => none⟩
  place := fun _ => 0

/-- Following decides types and performers by equality, and finds two operations on operands of
the same types the same, which they are: the type of the operand names the operation. -/
def domainChecks : SkelRules domainDialect where
  sameTy := inferInstanceAs (DecidableEq DomainTy)
  sameWho := inferInstanceAs (DecidableEq Unit)
  sameOp := fun _ _ => true

/-- On a natural that is not zero, the operation asks its question, then returns the natural less
one. -/
theorem decrement_nonzero (τ : DomainTy) (key : Key) (path : List Frame) (n : Nat)
    (nonzero : n ≠ 0) :
    domainSem.op key (DomainOp.decrement τ) path (.cons n .nil) =
      .call () fun _ => .done (.cons (n - 1) .nil) := by
  simp only [domainSem, nonzero, ↓reduceIte]

/-- Operations that following finds the same are the same. -/
theorem domainChecks_lawful : domainChecks.Lawful := by
  intro ins res res' o o' _
  cases o
  cases o'
  exact ⟨rfl, HEq.rfl⟩

/-- **The rules of the dialect are lawful for its semantics**, for every permitted reply: with
`domainRun`, the validity `domainValid`, the reading `domainReading` and the stop `undefined`. The
law `effect` holds because the operation is applied only where its requirement holds: its operand
is at least one, so it asks its question and returns a natural. -/
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
      ranges := fun _ _ _ _ ran => ran.1.elim }
  keeps := fun _ _ _ ran => ran.elim
  defined := fun _ shared => by cases shared
  named := by
    intro ins res o values _ requirement listed operand named written positions applied
    cases o
    simp only [domainRules, List.mem_singleton] at listed
    subst listed
    simp only [Requirement.operands, List.mem_singleton] at named
    subst named
    cases applied
  effect := by
    intro ins res o _ key path values _ required
    cases o with
    | decrement τ =>
        obtain ⟨n, rfl⟩ := HList.one values
        obtain ⟨vs, denoted, relation⟩ := required (.atLeast (.arg 0) 1)
          (by simp only [domainRules, List.mem_singleton])
        obtain ⟨v, rfl, at0⟩ := DenotesAll.one denoted
        have read : v = ⟨τ, n⟩ :=
          (Option.some.inj (show (some ⟨τ, n⟩ : Option domainSem.Dyn) = some v from at0)).symm
        subst read
        have positive : 1 ≤ (n : Nat) := relation n rfl
        rw [decrement_nonzero τ key path n (Nat.pos_iff_ne_zero.mp positive)]
        intro _ _ v returned
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

/-! ## The operation applied -/

/-- The operation applied, with the key 1, to the input `0` of the type given; its result, the
name `1`, is returned. -/
def decrementOf (τ : DomainTy) :
    Term domainDialect (Ctx.empty.extend (types := [τ]) (.cons 0 .nil)) [.natural] :=
  .op ⟨1⟩ (DomainOp.decrement τ) (.cons ⟨0, rfl⟩ .nil) (.cons 1 .nil) (.ret (.cons ⟨1, rfl⟩ .nil))

/-- On a positive input the check of facts accepts: the type says that the operand is at least
one. There is no loop, so no bound. -/
example : checkFacts domainRules domainChecks ⟨1⟩ none (.cons 0 .nil) (decrementOf .positive) =
    .ok [] := by
  decide +kernel

/-- So, by the soundness of the analysis, on every valid input, which is at least one, and every
permitted reply, the operation applied to a positive input never stops `undefined` and returns a
valid value. -/
theorem decrementPositive_safe (permitted : ∀ op, domainSem.S.Reply op → Prop) (n : Nat)
    (positive : 1 ≤ n) :
    ((decrementOf .positive).denote domainSem []
        (Env.empty.extend (.cons 0 .nil) (.cons n .nil))).Every
      permitted (fun returned => ∀ v, v ∈ domainSem.dyns returned → domainValid v)
      (fun stop => ¬ stop = .undefined) :=
  (Analysis.analyse_sound domainRules domainChecks domainSem permitted domainReading domainRun
    domainValid (· = .undefined) (domainRules_lawful permitted) domainChecks_lawful ⟨1⟩ none
    (.cons 0 .nil) (decrementOf .positive) (by unfold Term.Distinct; decide +kernel)
    (by decide +kernel) [] (fun _ _ inside => nomatch inside) (.cons n .nil)
    (fun _ inputs => by
      cases inputs with
      | head => exact positive
      | tail _ rest => cases rest)).2.1

/-- On a natural input the check of facts refuses the operation, at its place, with the
requirement that is not justified and what was known of its operand: at least zero. -/
example : checkFacts domainRules domainChecks ⟨1⟩ none (.cons 0 .nil) (decrementOf .natural) =
    .error [⟨.domain, ⟨⟨1⟩, [], some ⟨1⟩, none⟩,
      .unjustified .decrement (.atLeast (.arg 0) 1) [some ⟨0, none⟩]⟩] := by
  decide +kernel

/-! ## The control on the semantics -/

/-- On the input zero, the process of the operation applied to a natural is the stop `undefined`:
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

/-- The operation applied to a positive input with other names: the input `5` and the result
`6`. -/
def decrementOtherNames :
    Term domainDialect (Ctx.empty.extend (types := [.positive]) (.cons 5 .nil)) [.natural] :=
  .op ⟨1⟩ (DomainOp.decrement .positive) (.cons ⟨5, rfl⟩ .nil) (.cons 6 .nil)
    (.ret (.cons ⟨6, rfl⟩ .nil))

/-- It follows the analysis of the first: the operation is the skeleton's entry, its requirement
is decided where it is applied, and nothing is refused. The whole verdict accepts it. -/
example : (Analysis.follow domainRules domainChecks ⟨1⟩ none
    (Analysis.analyse domainRules domainChecks ⟨1⟩ none (.cons 0 .nil) (decrementOf .positive))
    (.cons 5 .nil) decrementOtherNames).accepted = true := by
  decide +kernel

end Zkc.Core.DomainTests
