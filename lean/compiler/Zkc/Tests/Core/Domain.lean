import Zkc.Core.Facts.Body.Traversal
import Zkc.Core.Facts.Body.Verdicts
import Zkc.Core.Facts.Knowledge.Soundness
import Zkc.Core.Evidence.Summary
import Zkc.Core.Facts.Contracts.HeaderPredicates

/-! A dialect of effectful operations, checked under contracts and compared after renaming.
The predicates of its contracts are zero, numeric comparison and Boolean negation. -/

namespace Zkc.Core.DomainTests
open BodyAnalysis

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
  | zero | less | negate
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
  bool value := some (value.2 != 0)

def bit (b : Bool) : domainSem.Dyn := ⟨.natural, b.toNat⟩

@[simp] theorem read_bit (b : Bool) : domainReading.bool (bit b) = some b := by cases b <;> rfl

/-- The relation of the operations available in assertions. The four instructions are effects. -/
inductive domainRun : DomainRaw → List domainSem.Dyn → List domainSem.Dyn → Prop where
  | zero : domainRun .zero [] [⟨.natural, 0⟩]
  | less (a b : domainSem.Dyn) : domainRun .less [a,b] [bit (decide (a.2 < b.2))]
  | negate (a : domainSem.Dyn) : domainRun .negate [a] [bit (a.2 == 0)]

abbrev Runs := ValidRun domainSem domainRun domainValid

def zero : Expr DomainRaw := .apply .zero .nil 0
def lt (a b : Expr DomainRaw) : Expr DomainRaw := .apply .less (.cons a (.cons b .nil)) 0
def neg (a : Expr DomainRaw) : Expr DomainRaw := .apply .negate (.cons a .nil) 0
def positive (i : Nat) := lt zero (.arg i)
def secondLeFirst := neg (lt (.arg 0) (.arg 1))

def contract : DomainRaw → BodyAnalysis.Contract DomainRaw
  | .decrement => ⟨[⟨positive 0, none⟩], []⟩
  | .subtract => ⟨[⟨secondLeFirst, none⟩], []⟩
  | .half => ⟨[], [⟨secondLeFirst, none⟩]⟩
  | _ => ⟨[], []⟩

def types : KnowledgeTypes DomainTy where
  range t := some ⟨match t with | .natural => 0 | .positive => 1, none⟩
  empty _ := false

def observations : KnowledgeOperations DomainRaw where
  ranges op _ := if op == .zero then [some (Range.point 0)] else []
  form
    | .less => some .less
    | .negate => some .negation
    | _ => none

def domainRules : BodyAnalysis.Rules domainDialect DomainRaw where
  written := domainWritten
  shared _ := false
  commutes _ := false
  place := DomainRaw.ctorIdx
  results _ := 1
  contract := contract
  assertable
    | .zero | .less | .negate => true
    | _ => false
  numbered _ := true
  indexAt _ _ := none
  indexFromCount ok := nomatch ok
  indexNext _ := none

private def signature : DomainRaw → List DomainTy → Option (List DomainTy)
  | .zero, [] => some [.natural]
  | .less, [_,_] => some [.natural]
  | .negate, [_] => some [.natural]
  | _, _ => none

/-- Recover source-operand order from the two predicates used by this dialect. -/
private def diagnosticOperands : Expr DomainRaw → List Nat
  | .apply .less (.cons (.apply .zero .nil 0) (.cons (.arg i) .nil)) 0 => [i]
  | .apply .negate (.cons (.apply .less (.cons (.arg a) (.cons (.arg b) .nil)) 0) .nil) 0 => [b,a]
  | _ => []

def configFor (summary : BodyAnalysis.Contract DomainRaw) : Config domainDialect DomainRaw where
  rules := domainRules
  domain := Knowledge.domain types observations
  lemmas := []
  definition := ⟨1⟩
  role := none
  assertions := ⟨signature, fun _ => true⟩
  explain concern index positions _ known :=
    let clauses := match concern with
      | .requirement op => (contract op).requires
      | .guarantee => summary.ensures
      | _ => []
    ((clauses[index]?).toList.flatMap diagnosticOperands).map fun i => do
      known.rangeOf (← (← positions[i]?).map Ident.key)

def cfg := configFor ⟨[],[]⟩

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

theorem validResults {t : DomainTy} {n : Nat} (ok : domainValid ⟨t,n⟩) :
    ∀ v ∈ [⟨t,n⟩], domainValid v := by simpa using ok

private theorem zero_denotes (args : List domainSem.Dyn) : zero.Denotes Runs args ⟨.natural,0⟩ :=
  .apply .nil ⟨.zero, by simp, validResults trivial⟩ rfl

private theorem lt_denotes {args : List domainSem.Dyn} {a b x y}
    (one : a.Denotes Runs args x) (two : b.Denotes Runs args y)
    (vx : domainValid x) (vy : domainValid y) :
    (lt a b).Denotes Runs args (bit (decide (x.2 < y.2))) :=
  .apply (.cons one (.cons two .nil)) ⟨.less x y, by simpa using And.intro vx vy, validResults trivial⟩ rfl

private theorem neg_denotes {args : List domainSem.Dyn} {a x}
    (one : a.Denotes Runs args x) (vx : domainValid x) :
    (neg a).Denotes Runs args (bit (x.2 == 0)) :=
  .apply (.cons one .nil) ⟨.negate x, validResults vx, validResults trivial⟩ rfl

theorem functional {w xs ys zs} (h : domainRun w xs ys) (h' : domainRun w xs zs) : ys = zs := by
  cases h <;> cases h' <;> rfl

private theorem agrees {e : Expr DomainRaw} {args v} (den : e.Denotes Runs args v) :
    e.Holds Runs domainReading args ↔ domainReading.bool v = some true := by
  constructor
  · rintro ⟨v', other, yes⟩
    obtain rfl := den.unique (fun _ _ _ _ x y => functional x.1 y.1) other
    exact yes
  · exact fun yes => ⟨v, den, yes⟩

private theorem positive_iff {args : List domainSem.Dyn} {i t n}
    (found : args[i]? = some ⟨t,n⟩) (valid : domainValid ⟨t,n⟩) :
    (positive i).Holds Runs domainReading args ↔ 0 < n := by
  unfold positive
  rw [agrees (lt_denotes (zero_denotes args) (.arg found) trivial valid), read_bit]
  simp

private theorem le_iff {args : List domainSem.Dyn} {a b : Nat}
    (left : args[0]? = some ⟨.natural,a⟩) (right : args[1]? = some ⟨.natural,b⟩) :
    secondLeFirst.Holds Runs domainReading args ↔ b ≤ a := by
  unfold secondLeFirst
  rw [agrees (neg_denotes (lt_denotes (.arg left) (.arg right) trivial trivial) trivial), read_bit]
  by_cases a < b <;> simp_all [bit]

theorem domainRules_lawful (permitted : ∀ op, domainSem.S.Reply op → Prop) :
    domainRules.Lawful domainSem permitted domainReading domainRun domainValid (· = .undefined) where
  computes := fun _ h => nomatch h
  observedOperand := by intro _ _ _ _ h; cases h
  functional := fun _ _ _ _ => functional
  commutative := fun _ h => nomatch h
  keeps := by intro w xs ys run _; cases run <;> exact ⟨validResults trivial, rfl⟩
  defined := fun _ h => nomatch h
  assertable := by intro _ _ o; cases o <;> exact nofun
  effect := by
    intro ins outs o _ key path args valid req
    cases o with
    | decrement t =>
      obtain ⟨n,rfl⟩ := HList.one args
      have pos := (positive_iff (args := [⟨t,n⟩]) (i := 0) rfl (valid _ List.mem_cons_self)).mp
        (req _ List.mem_cons_self)
      rw [decrement_nonzero _ _ _ _ (Nat.ne_of_gt pos)]
      exact fun _ _ => ⟨validResults trivial, fun _ m => nomatch m⟩
    | half =>
      obtain ⟨n,rfl⟩ := HList.one args
      intro _ _
      refine ⟨validResults trivial, fun g m => ?_⟩
      obtain rfl := List.mem_singleton.mp m
      exact (le_iff rfl rfl).mpr (Nat.div_le_self n 2)
    | opaqueHalf =>
      obtain ⟨n,rfl⟩ := HList.one args
      exact fun _ _ => ⟨validResults trivial, fun _ m => nomatch m⟩
    | subtract =>
      obtain ⟨a,b,rfl⟩ := HList.two args
      have within := (le_iff (args := [⟨.natural,a⟩, ⟨.natural,b⟩]) rfl rfl).mp (req _ List.mem_cons_self)
      rw [subtract_within _ _ _ _ within]
      exact ⟨validResults trivial, fun _ m => nomatch m⟩
  condition := fun ok => nomatch ok
  count := fun ok => nomatch ok
  pick := fun ok => nomatch ok
  index := fun _ _ => ⟨trivial, fun _ => rfl⟩
  indexAt := fun _ _ _ h => nomatch h
  indexFromCount := fun ok => nomatch ok
  indexNext := fun _ _ h => nomatch h
  collect := fun _ _ _ _ _ => trivial
  begin := fun _ _ _ => trivial
  settle := fun _ _ _ => trivial
  stop := fun _ _ _ => nofun

private theorem observationLaws : observations.Lawful domainReading Runs where
  functional := fun _ _ _ _ x y => functional x.1 y.1
  form := by
    intro op xs ys f found run
    cases run.1 <;> cases found
    · exact ⟨_, rfl, _, _, _, _, rfl, rfl, rfl, read_bit _⟩
    · exact ⟨_, rfl, _, _, rfl, rfl, by rw [read_bit]; change some _ = some (!(!( _ == 0))); simp⟩
  preservesNumber := by intro _ _ _ h; cases h
  ranges := by
    intro op xs ys known run _ i r found
    cases run.1 <;> cases i <;> simp [observations] at found
    subst r
    exact ⟨_, 0, rfl, rfl, Range.has_point.mpr rfl⟩

private theorem typeLaws : types.Lawful domainReading (TypedValue domainSem domainValid) where
  range := by
    rintro _ ⟨t,n⟩ r ⟨valid,rfl⟩ found
    cases t <;> cases found
    · exact ⟨n, rfl, Nat.zero_le _, nofun⟩
    · exact ⟨n, rfl, valid, nofun⟩
  inhabited := fun _ => rfl

private def setting (permitted : ∀ op, domainSem.S.Reply op → Prop) : Setting domainDialect DomainRaw where
  cfg := cfg
  notes := []
  sem := domainSem
  permitted := permitted
  R := domainReading
  Run := domainRun
  Valid := domainValid
  undefined := (· = .undefined)
  domain := Knowledge.lawful observationLaws typeLaws
  F := []

private theorem settingLawful (permitted) : (setting permitted).Lawful where
  rules := domainRules_lawful permitted
  lemmas := fun _ m => nomatch m
  requires := by
    intro ins outs op e m args valid
    cases op with
    | decrement t =>
      obtain rfl := List.mem_singleton.mp m
      obtain ⟨n,rfl⟩ := HList.one args
      exact ⟨_, lt_denotes (zero_denotes _) (.arg (position := 0) rfl) trivial (valid _ List.mem_cons_self)⟩
    | subtract =>
      obtain rfl := List.mem_singleton.mp m
      obtain ⟨a,b,rfl⟩ := HList.two args
      exact ⟨_, neg_denotes (lt_denotes (.arg (position := 0) rfl) (.arg (position := 1) rfl) trivial trivial) trivial⟩
    | half | opaqueHalf => cases m

private theorem readerLawful (permitted) : cfg.assertions.Lawful (setting permitted) where
  admissible := by
    intro op ins outs h
    change signature op ins = some outs at h
    unfold signature at h
    split at h <;> cases h <;> rfl
  total := by
    intro op ins outs h args typed
    change signature op ins = some outs at h
    unfold signature at h
    split at h <;> cases h
    · cases typed
      exact ⟨_, ⟨.zero, by simp, validResults trivial⟩, .cons ⟨trivial,rfl⟩ .nil⟩
    · cases typed with
      | cons a tail =>
        cases tail with
        | cons b tail =>
          cases tail
          exact ⟨_, ⟨.less _ _, by simpa using And.intro a.1 b.1, validResults trivial⟩, .cons ⟨trivial,rfl⟩ .nil⟩
    · cases typed with
      | cons a tail =>
        cases tail
        exact ⟨_, ⟨.negate _, validResults a.1, validResults trivial⟩, .cons ⟨trivial,rfl⟩ .nil⟩
  boolean := fun _ _ _ => ⟨_,rfl⟩

/-! ## The decrement applied -/

/-- The decrement applied, with the key 1, to the input `0` of the type given; its result, the
name `1`, is returned. -/
def decrementOf (τ : DomainTy) :
    Term domainDialect (Ctx.empty.extend (types := [τ]) (.cons 0 .nil)) [.natural] :=
  .op ⟨1⟩ (DomainOp.decrement τ) (.cons ⟨0, rfl⟩ .nil) (.cons 1 .nil) (.ret (.cons ⟨1, rfl⟩ .nil))

def check {ins outs : List DomainTy} (summary : BodyAnalysis.Contract DomainRaw) (inputs : Names ins)
    (body : Term domainDialect (Ctx.empty.extend inputs) outs) :=
  BodyAnalysis.checkFacts (configFor summary) [] summary inputs body

abbrev emptyContract : BodyAnalysis.Contract DomainRaw := ⟨[], []⟩

example : check emptyContract (.cons 0 .nil) (decrementOf .positive) = .ok [] := rfl
example : check emptyContract (.cons 0 .nil) (decrementOf .natural) =
    .error (.refused [⟨⟨⟨1⟩, [], some ⟨1⟩, none⟩, .requirement .decrement, 0,
      some (positive 0), .unknown, [some ⟨0, none⟩]⟩]) := rfl

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

example : followChecked cfg domainChecks ⟨1⟩ [] [] emptyContract (.cons 0 .nil) (.cons 5 .nil)
    (decrementOf .positive) decrementOtherNames = .ok [] := rfl

def pre : BodyAnalysis.Contract DomainRaw := ⟨[⟨positive 0, none⟩], []⟩
example : check pre (.cons 0 .nil) (decrementOf .natural) = .ok [] := rfl

/-- Project the public checker's soundness back to the original term and its valid results. -/
private theorem decrementChecked (permitted) (t : DomainTy) (n : Nat)
    (summary : BodyAnalysis.Contract DomainRaw)
    (ok : BodyAnalysis.checkFacts cfg [] summary (.cons 0 .nil) (decrementOf t) = .ok [])
    (valid : domainValid ⟨t,n⟩)
    (requires : ∀ e ∈ summary.requires, e.Holds Runs domainReading [⟨t,n⟩]) :
    ((decrementOf t).denote domainSem [] (Env.empty.extend (.cons 0 .nil) (.cons n .nil))).Every
      permitted (fun ys => ∀ v ∈ domainSem.dyns ys, domainValid v) (· ≠ .undefined) := by
  let σ := setting permitted
  have safe := (checkFacts_safe σ (settingLawful _) (readerLawful _) summary (.cons 0 .nil)
    (decrementOf t) [] ok (by cases t <;> decide +kernel) (fun _ _ m => nomatch m) []
    (.cons n .nil) (validResults valid) requires (noGivenFacts σ rfl _ _ _)).2
  exact Process.every_mono _ _ (fun _ ys => ys.1) (fun _ h => h) safe

theorem decrementPositive_safe (permitted : ∀ op, domainSem.S.Reply op → Prop) (n : Nat)
    (positive : 1 ≤ n) :
    ((decrementOf .positive).denote domainSem []
        (Env.empty.extend (.cons 0 .nil) (.cons n .nil))).Every
      permitted (fun returned => ∀ v, v ∈ domainSem.dyns returned → domainValid v)
      (fun stop => ¬ stop = .undefined) :=
  decrementChecked permitted .positive n emptyContract rfl positive (fun _ m => nomatch m)

def inputAtLeastOne : Summary DomainRaw := ⟨[.atLeast (.arg 0) 1], []⟩

theorem decrementNatural_holds (permitted : ∀ op, domainSem.S.Reply op → Prop) :
    Summary.Holds domainSem permitted domainReading Runs domainValid (· = .undefined) inputAtLeastOne
      (fun values => (decrementOf .natural).denote domainSem [] (Env.empty.extend (.cons 0 .nil)
        values)) := by
  intro args _ req
  obtain ⟨n,rfl⟩ := HList.one args
  obtain ⟨vs, den, relation⟩ := req (.atLeast (.arg 0) 1) List.mem_cons_self
  obtain ⟨v, eqs, first⟩ := DenotesAll.one den
  subst vs
  have eqv : some (⟨.natural,n⟩ : domainSem.Dyn) = some v := first
  obtain rfl := Option.some.inj eqv
  obtain ⟨_, read, positive⟩ := relation
  cases read
  have run := decrementChecked permitted .natural n pre rfl trivial (by
    intro e m
    obtain rfl := List.mem_singleton.mp m
    exact (positive_iff (i := 0) (t := .natural) (n := n) rfl trivial).mpr positive)
  exact Process.every_mono _ _ (fun _ valid => ⟨valid, fun _ m => nomatch m⟩) (fun _ h => h) run

/-- The control: the input zero, on which the decrement applied to a natural is the stop
`undefined` (above), is the one input that the summary's requirement excludes. -/
example : ¬ (Requirement.atLeast (.arg 0) 1 : Requirement DomainRaw).Holds
    (ValidRun domainSem domainRun domainValid) domainReading [⟨.natural, (0 : Nat)⟩] := by
  rintro ⟨vs, denoted, relation⟩
  obtain ⟨v, rfl, at0⟩ := DenotesAll.one denoted
  cases at0
  obtain ⟨x, read, positive⟩ := relation
  cases read
  exact absurd positive (by decide)

/-- A body that returns its natural input, the name `0`. -/
def returnsInput :
    Term domainDialect (Ctx.empty.extend (types := [.natural]) (.cons 0 .nil)) [.natural] :=
  .ret (.cons ⟨0, rfl⟩ .nil)

def post : BodyAnalysis.Contract DomainRaw := ⟨[], [⟨positive 1, none⟩]⟩
example : check ⟨pre.preconditions, post.postconditions⟩ (.cons 0 .nil) returnsInput = .ok [] := rfl
example : check post (.cons 0 .nil) returnsInput =
    .error (.refused [⟨⟨⟨1⟩, [], none, none⟩, .guarantee, 0, some (positive 1),
      .unknown, [some ⟨0, none⟩]⟩]) := rfl

/-- A half, by the operation given, of the natural input `0`, with the key 1, named `1`; then the
subtraction of it from the input, with the key 2, named `2`, which is returned. -/
def subtractHalf (halve : DomainOp [.natural] [.natural]) :
    Term domainDialect (Ctx.empty.extend (types := [.natural]) (.cons 0 .nil)) [.natural] :=
  .op ⟨1⟩ halve (.cons ⟨0, rfl⟩ .nil) (.cons 1 .nil)
    (.op ⟨2⟩ DomainOp.subtract (.cons ⟨0, rfl⟩ (.cons ⟨1, rfl⟩ .nil)) (.cons 2 .nil)
      (.ret (.cons ⟨2, rfl⟩ .nil)))

example : check emptyContract (.cons 0 .nil) (subtractHalf .half) = .ok [] := rfl
example : check emptyContract (.cons 0 .nil) (subtractHalf .opaqueHalf) =
    .error (.refused [⟨⟨⟨1⟩, [], some ⟨2⟩, none⟩, .requirement .subtract, 0,
      some secondLeFirst, .unknown, [some ⟨0, none⟩, some ⟨0, none⟩]⟩]) := rfl

end Zkc.Core.DomainTests
