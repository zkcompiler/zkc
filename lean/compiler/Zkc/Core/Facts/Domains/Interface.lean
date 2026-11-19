module

public import Zkc.Core.Facts.Contracts.Expressions

@[expose] public section

/-!
The seam of the analysis on the term in steps, part 3: domains.

What is known is a domain behind an interface (`Domain`): a state and the operations by which
the walk tells it of what happens. What a state means, and the law of each operation, are for
an interpretation (`Domain.Lawful`): each law is about concretization only, and speaks of what
identifiers read. A domain asks the others (`Asks`); a question is about the state in which
its answer holds. Two domains make one (`Domain.prod`).
-/

namespace Zkc.Core.BodyAnalysis

/-! ## Questions -/

/-- What a domain may ask the others of an identifier. "Unknown" is always an answer. -/
structure Asks where
  /-- Its truth. -/
  truth : Ident → Option Bool
  /-- The number it is. -/
  exact : Ident → Option Nat
  /-- A number that it is at most. -/
  upper : Ident → Option Nat
  /-- Another live identifier with the same numeric reading. -/
  numberSource : Ident → Option Ident := fun _ => none

def Asks.numberAt (asks : Asks) (id : Ident) := (asks.numberSource id).getD id

/-- A dynamic count may use a bound established on an earlier reading. -/
def Asks.upperAt (asks : Asks) (id : Ident) : Option Nat :=
  (asks.upper id).orElse fun _ => (asks.numberSource id).bind asks.upper

theorem Asks.upperAt_source {asks : Asks} {id n} (found : asks.upperAt id = some n) :
    asks.upper id = some n ∨ ∃ other, asks.numberSource id = some other ∧ asks.upper other = some n := by
  cases direct : asks.upper id with
  | some cap => exact .inl (by simpa [Asks.upperAt, direct] using found)
  | none =>
    apply Or.inr
    apply Option.bind_eq_some_iff.mp
    simpa [Asks.upperAt, direct] using found

/-- Nobody to ask. -/
def Asks.nobody : Asks := {truth := fun _ => none, exact := fun _ => none, upper := fun _ => none}

/-- The first's answer, or the second's. -/
def Asks.orElse (first second : Asks) : Asks where
  truth id := (first.truth id).orElse fun _ => second.truth id
  exact id := (first.exact id).orElse fun _ => second.exact id
  upper id := (first.upper id).orElse fun _ => second.upper id
  numberSource id := (first.numberSource id).orElse fun _ => second.numberSource id

section
variable {Raw Val : Type} (Run : Raw → List Val → List Val → Prop) (R : Reading Val)

/-- The answers are true of what identifiers read: an answer says that the identifier reads a
value, and something of that value. -/
structure Asks.Sound (table : Table Raw) (ρ : Leaves Val) (asks : Asks) : Prop where
  truth : ∀ id b, asks.truth id = some b → ∃ v, Reads Run R.bool table ρ id v ∧ R.bool v = some b
  exact : ∀ id n, asks.exact id = some n → ∃ v, Reads Run R.bool table ρ id v ∧ R.nat v = some n
  upper : ∀ id n, asks.upper id = some n →
    ∃ v k, Reads Run R.bool table ρ id v ∧ R.nat v = some k ∧ k ≤ n
  numberSource : ∀ id other, asks.numberSource id = some other →
    ∃ v w, Reads Run R.bool table ρ id v ∧ Reads Run R.bool table ρ other w ∧ R.nat v = R.nat w


end

/-! ## A loop, as a domain is told of it -/

/-- A loop: how often it runs (a written number, or the identifier of a value), the leaf of its
index with its type and whether that index reads as the number of the iteration (the dialect's
rules say), the identifiers of the initial carried values, and the leaves of the carried values
in the body with their types. -/
structure Loop (T : Type) where
  count : Nat ⊕ Ident
  index : Ident
  indexType : T
  numbered : Bool
  initial : List Ident
  carried : List Ident
  types : List T

section
variable {T Raw Val : Type} (Run : Raw → List Val → List Val → Prop) (R : Reading Val)

/-- A loop runs `N` times, under these leaves. -/
def Loop.Counts (table : Table Raw) (ρ : Leaves Val) (L : Loop T) (N : Nat) : Prop :=
  match L.count with
  | .inl written => N = written
  | .inr id => ∃ v, Reads Run R.bool table ρ id v ∧ R.nat v = some N

/-- The leaves of an iteration: the index reads a value of its type, which is the number of the
iteration where the loop's index is numbered, and the carried leaves read the values given,
each of its type. -/
def Loop.At (Typed : Val → T → Prop) (table : Table Raw) (ρ : Leaves Val) (L : Loop T) (k : Nat)
    (carried : List Val) : Prop :=
  (∃ index, Reads Run R.bool table ρ L.index index ∧ Typed index L.indexType ∧
      (L.numbered = true → R.nat index = some k)) ∧
    ReadsAll Run R.bool table ρ L.carried carried ∧
    carried.length = L.types.length ∧
    ∀ (i : Nat) (v : Val) (τ : T), carried[i]? = some v → L.types[i]? = some τ → Typed v τ

end

/-! ## The interface -/

/-- A domain: what the analysis knows, behind operations. `T` is the dialect's types, `Raw` its
written operations. What a domain is told about an operation is its own: it reads the written
operation of an entry. -/
structure Domain (T Raw : Type) where
  State : Type
  /-- The state at the start. -/
  init : State
  /-- The state holds of nothing: the place cannot be reached. -/
  dead : State → Bool
  /-- Identifiers that are new to the domain, with their types. -/
  leaves : State → List (Ident × T) → State
  /-- An entry whose values read. -/
  transfer : Asks → Table Raw → State → Entry Raw → State
  /-- Observe a result whose subject and scalar readings agree with an operand. -/
  observe : Asks → Table Raw → State → Ident → Ident → State
  /-- An identifier that reads the given truth. -/
  assume : Asks → Table Raw → State → Ident → Bool → State
  /-- What is known of the truth of an identifier that reads. -/
  truth : Asks → Table Raw → State → Ident → Option Bool
  /-- After regions: the state before them; for each region that can run, the others' answers
  in its exit state, its exit state and what it returns; the identifiers of the results. -/
  after : Table Raw → State → List (Asks × State × List Ident) → List Ident → State
  /-- At the entry of a loop's body, from the state before the loop. -/
  enter : Asks → Table Raw → State → Loop T → State
  /-- After a loop: the others' answers in the state before it and in the body's exit state;
  the state before it; the loop; the body's exit state; what the body returns as the carried
  values; the leaves of the carried results. Of what a loop collects a domain is told the
  types only (`leaves`). -/
  afterLoop : Asks → Asks → Table Raw → State → Loop T → State → List Ident → List Ident → State
  /-- What it answers the others. -/
  answers : State → Asks

/-- The meaning of a domain's states and the laws of its operations, for an interpretation:
what written operations give (`Run`), how values read as numbers and truths (`R`), and which
values are of a type (`Typed`). Each law is about concretization only. -/
structure Domain.Lawful {T Raw Val : Type} (D : Domain T Raw)
    (Run : Raw → List Val → List Val → Prop) (R : Reading Val) (Typed : Val → T → Prop) where
  /-- What a state says of a table and the leaves. -/
  Means : D.State → Table Raw → Leaves Val → Prop
  /-- It is kept when the table grows and more leaves get values. -/
  mono : ∀ {s table table' ρ ρ'}, table.Le table' → ρ.Le ρ' → Means s table ρ → Means s table' ρ'
  init : ∀ table ρ, Means D.init table ρ
  dead : ∀ {s table ρ}, D.dead s = true → ¬ Means s table ρ
  answers : ∀ {s table ρ}, Means s table ρ → (D.answers s).Sound Run R table ρ
  leaves : ∀ {s table ρ} {ids : List (Ident × T)}, Table.WF table → Means s table ρ →
    (∀ p, p ∈ ids → ∃ v, Reads Run R.bool table ρ p.1 v ∧ Typed v p.2) →
    Means (D.leaves s ids) table ρ
  transfer : ∀ {asks s table ρ} {e : Entry Raw}, Table.WF table → asks.Sound Run R table ρ → Means s table ρ →
    e ∈ table → (∀ j, j < e.count → ∃ v, Reads Run R.bool table ρ (.val (e.lo + j)) v) →
    Means (D.transfer asks table s e) table ρ
  observe : ∀ {asks s table ρ source result x y}, Table.WF table → asks.Sound Run R table ρ →
    Means s table ρ → Reads Run R.bool table ρ source x → Reads Run R.bool table ρ result y →
    R.Agrees x y → Means (D.observe asks table s source result) table ρ
  assume : ∀ {asks s table ρ id v b}, Table.WF table → asks.Sound Run R table ρ → Means s table ρ →
    Reads Run R.bool table ρ id v → R.bool v = some b → Means (D.assume asks table s id b) table ρ
  truth : ∀ {asks s table ρ id v b}, Table.WF table → asks.Sound Run R table ρ → Means s table ρ →
    Reads Run R.bool table ρ id v → D.truth asks table s id = some b → R.bool v = some b
  /-- The region that ran is one of the exits; the results read what it returned. -/
  after : ∀ {table before} {exits : List (Asks × D.State × List Ident)} {results ρ asks s returned},
    Table.WF table → Means before table ρ → (asks, s, returned) ∈ exits → Means s table ρ →
    asks.Sound Run R table ρ →
    (∃ values, ReadsAll Run R.bool table ρ returned values ∧
      ReadsAll Run R.bool table ρ results values) →
    Means (D.after table before exits results) table ρ
  /-- At every iteration: the leaves extend those at the loop's entry and are those of an
  iteration below the count. -/
  enter : ∀ {asks s table ρ ρk} {L : Loop T} {N k : Nat} {carried : List Val}, Table.WF table → Means s table ρ →
    L.Counts Run R table ρ N → ρ.Le ρk → k < N → L.At Run R Typed table ρk k carried →
    asks.Sound Run R table ρk → Means (D.enter asks table s L) table ρk
  /-- Over all iterations, none included: `carried k` are the carried values at the entry of
  iteration `k`, and each iteration below the count ran to leaves of which the exit state
  holds and in which the body returns `carried (k + 1)`. -/
  afterLoop : ∀ {before exit : Asks} {table s out} {L : Loop T} {returned made : List Ident}
    {ρ σ} {N : Nat} {carried : Nat → List Val},
    Table.WF table → before.Sound Run R table ρ → Means s table ρ → L.Counts Run R table ρ N →
    ReadsAll Run R.bool table ρ L.initial (carried 0) →
    (∀ k, k < N → ∃ ρk, ρ.Le ρk ∧ L.At Run R Typed table ρk k (carried k) ∧ Means out table ρk ∧
      exit.Sound Run R table ρk ∧ ReadsAll Run R.bool table ρk returned (carried (k + 1))) →
    ρ.Le σ → ReadsAll Run R.bool table σ made (carried N) →
    Means (D.afterLoop before exit table s L out returned made) table σ

/-! ## The product -/

/-- Two domains together. In `transfer`, `assume` and `enter` the second sees the first's new
state; in `truth` each sees the other's state; at a join and after a loop each is given the
other's answers in each exit state. The order is part of the analysis's configuration: it can
change what is found, never soundness. -/
def Domain.prod {T Raw : Type} (A B : Domain T Raw) : Domain T Raw where
  State := A.State × B.State
  init := (A.init, B.init)
  dead s := A.dead s.1 || B.dead s.2
  leaves s ids := (A.leaves s.1 ids, B.leaves s.2 ids)
  transfer asks table s e :=
    let a := A.transfer (asks.orElse (B.answers s.2)) table s.1 e
    (a, B.transfer (asks.orElse (A.answers a)) table s.2 e)
  observe asks table s source result :=
    let a := A.observe (asks.orElse (B.answers s.2)) table s.1 source result
    (a, B.observe (asks.orElse (A.answers a)) table s.2 source result)
  assume asks table s id b :=
    let a := A.assume (asks.orElse (B.answers s.2)) table s.1 id b
    (a, B.assume (asks.orElse (A.answers a)) table s.2 id b)
  truth asks table s id :=
    (A.truth (asks.orElse (B.answers s.2)) table s.1 id).orElse fun _ =>
      B.truth (asks.orElse (A.answers s.1)) table s.2 id
  after table before exits results :=
    (A.after table before.1 (exits.map fun x => (x.1.orElse (B.answers x.2.1.2), x.2.1.1, x.2.2))
        results,
      B.after table before.2 (exits.map fun x => (x.1.orElse (A.answers x.2.1.1), x.2.1.2, x.2.2))
        results)
  enter asks table s L :=
    let a := A.enter (asks.orElse (B.answers s.2)) table s.1 L
    (a, B.enter (asks.orElse (A.answers a)) table s.2 L)
  afterLoop before exit table s L out returned made :=
    (A.afterLoop (before.orElse (B.answers s.2)) (exit.orElse (B.answers out.2)) table s.1 L out.1
        returned made,
      B.afterLoop (before.orElse (A.answers s.1)) (exit.orElse (A.answers out.1)) table s.2 L out.2
        returned made)
  answers s := (A.answers s.1).orElse (B.answers s.2)

/-- The product of two lawful domains is lawful, with the meaning "both hold". -/
def ProdLawfulStatement : Prop :=
  ∀ {T Raw Val : Type} (A B : Domain T Raw) (Run : Raw → List Val → List Val → Prop)
    (R : Reading Val) (Typed : Val → T → Prop) (a : A.Lawful Run R Typed)
    (b : B.Lawful Run R Typed),
    ∃ both : (A.prod B).Lawful Run R Typed,
      ∀ s table ρ, both.Means s table ρ ↔ a.Means s.1 table ρ ∧ b.Means s.2 table ρ

end Zkc.Core.BodyAnalysis
