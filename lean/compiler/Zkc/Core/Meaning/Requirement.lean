module

public import Zkc.Core.Program.Requirement
public import Zkc.Core.Meaning.Fold

@[expose] public section

/-!
What a requirement says of values.

A requirement (`Program/Requirement.lean`) names values: operands of an application by their
positions, or the first result of a written operation applied to some of them. How a value
reads, as a natural or as a truth value, is a `Reading`; what a written operation gives on
operands is a relation `Run`. Both are given by the dialect. A requirement holds of the values of
an application's operands when the values that it names are there and it says of them what is
true (`Requirement.Holds`). Nothing here depends on an analysis: this is the language in which an
operation states its domain, and in which a definition states what it requires and what it
guarantees (`Summary`, `Program/Requirement.lean`).

A definition satisfies a summary when, on valid inputs of which every requirement holds, it never
stops undefined, and what it returns is valid and, with the inputs, satisfies every guarantee
(`Summary.Holds`). A requirement that names operands by their positions only names no application,
so it holds of the same values whatever the relation of written operations
(`Requirement.holds_positional`), and so does a summary that names positions only
(`Summary.holds_positional`).
-/

namespace Zkc.Core

/-- How a value reads: as a natural, as a truth value; nothing for a value that is not one. -/
structure Reading (Val : Type) where
  nat : Val → Option Nat
  bool : Val → Option Bool

section
variable {Val : Type} {Raw : Type}

/-- The value that an operand of a requirement names, among the operands' values. -/
def Operand.Denotes (Run : Raw → List Val → List Val → Prop) (args : List Val) :
    Operand Raw → Val → Prop
  | .arg position, v => args[position]? = some v
  | .apply written positions, v => ∃ operands rs, atPositions args positions = some operands ∧
      Run written operands rs ∧ rs.head? = some v

/-- The values that operands name, in order. -/
def DenotesAll (Run : Raw → List Val → List Val → Prop) (args : List Val) :
    List (Operand Raw) → List Val → Prop
  | [], [] => True
  | o :: os, v :: vs => Operand.Denotes Run args o v ∧ DenotesAll Run args os vs
  | _, _ => False

/-- The value that one operand names. -/
theorem DenotesAll.one {Run : Raw → List Val → List Val → Prop} {args : List Val}
    {o : Operand Raw} {vs : List Val} (h : DenotesAll Run args [o] vs) :
    ∃ v, vs = [v] ∧ o.Denotes Run args v := by
  match vs, h with
  | [v], ⟨d, _⟩ => exact ⟨v, rfl, d⟩

/-- The values that two operands name. -/
theorem DenotesAll.two {Run : Raw → List Val → List Val → Prop} {args : List Val}
    {o o' : Operand Raw} {vs : List Val} (h : DenotesAll Run args [o, o'] vs) :
    ∃ v v', vs = [v, v'] ∧ o.Denotes Run args v ∧ o'.Denotes Run args v' := by
  match vs, h with
  | [v, v'], ⟨d, d', _⟩ => exact ⟨v, v', rfl, d, d'⟩

/-- What a requirement says of the values it names: an order, a bound, a number, a truth
value. An order, a bound, a number and a difference are of naturals: the values that it names
read as naturals, and the numbers are so related. -/
def Requirement.Relation (R : Reading Val) : Requirement Raw → List Val → Prop
  | .le .., [a, b] => ∃ x y, R.nat a = some x ∧ R.nat b = some y ∧ x ≤ y
  | .lt .., [a, b] => ∃ x y, R.nat a = some x ∧ R.nat b = some y ∧ x < y
  | .atLeast _ n, [a] => ∃ x, R.nat a = some x ∧ n ≤ x
  | .below _ n, [a] => ∃ x, R.nat a = some x ∧ x < n
  | .exactly _ n, [a] => ∃ x, R.nat a = some x ∧ x = n
  | .difference _ _ n, [b, a] => ∃ x y, R.nat b = some x ∧ R.nat a = some y ∧ x - y = n
  | .holds _, [a] => R.bool a = some true
  | .bounded _, [a] => ∃ x, R.nat a = some x
  | _, _ => False

/-- A requirement holds of the operands' values: the values it names are there, and it says
of them what is true. -/
def Requirement.Holds (Run : Raw → List Val → List Val → Prop) (R : Reading Val)
    (args : List Val) (requirement : Requirement Raw) : Prop :=
  ∃ vs, DenotesAll Run args requirement.operands vs ∧ requirement.Relation R vs

/-- Operands by their positions name the same values whatever the relation of written
operations. -/
theorem DenotesAll.positional {Run Run' : Raw → List Val → List Val → Prop} {args : List Val} :
    ∀ {operands : List (Operand Raw)} {vs : List Val},
      (∀ operand, operand ∈ operands → ∃ position, operand = .arg position) →
      DenotesAll Run args operands vs → DenotesAll Run' args operands vs
  | [], [], _, _ => trivial
  | [], _ :: _, _, denoted => denoted.elim
  | _ :: _, [], _, denoted => denoted.elim
  | operand :: operands, _ :: _, positions, ⟨denoted, others⟩ => by
      obtain ⟨position, rfl⟩ := positions operand List.mem_cons_self
      exact ⟨denoted, DenotesAll.positional
        (fun operand' listed => positions operand' (List.mem_cons_of_mem _ listed)) others⟩

/-- A requirement that names operands by their positions only holds of the same values whatever
the relation of written operations: it names no application. -/
theorem Requirement.holds_positional {Run Run' : Raw → List Val → List Val → Prop}
    {R : Reading Val} {args : List Val} {requirement : Requirement Raw} {count : Nat}
    (positional : requirement.positional count = true)
    (holds : requirement.Holds Run R args) : requirement.Holds Run' R args := by
  obtain ⟨vs, denoted, relation⟩ := holds
  refine ⟨vs, DenotesAll.positional (fun operand listed => ?_) denoted, relation⟩
  obtain ⟨position, same, -⟩ := Requirement.positional_operands positional operand listed
  exact ⟨position, same⟩

end

/-! ## What it is for a definition to satisfy a summary -/

/-- A definition satisfies a summary: on valid inputs of which every requirement holds, it
never stops undefined, and what it returns is valid and, with the inputs, satisfies every
guarantee. With no requirement and no guarantee this is what it is for the definition to be
assured (`Summary.holds_empty`, `Evidence/Summary.lean`). -/
def Summary.Holds {D : Dialect} {Raw : Type} (sem : Semantics D)
    (permitted : ∀ op, sem.S.Reply op → Prop) (R : Reading sem.Dyn)
    (Run : Raw → List sem.Dyn → List sem.Dyn → Prop) (Valid : sem.Dyn → Prop)
    (undefined : sem.H → Prop) (summary : Summary Raw) {ins outs : List D.Ty}
    (run : HList sem.Val ins → Process sem.S sem.H (HList sem.Val outs)) : Prop :=
  ∀ inputs : HList sem.Val ins, (∀ v, v ∈ sem.dyns inputs → Valid v) →
    (∀ requirement, requirement ∈ summary.requires →
      requirement.Holds Run R (sem.dyns inputs)) →
    (run inputs).Every permitted
      (fun returned => (∀ v, v ∈ sem.dyns returned → Valid v) ∧
        ∀ guarantee, guarantee ∈ summary.ensures →
          guarantee.Holds Run R (sem.dyns inputs ++ sem.dyns returned))
      (fun stop => ¬ undefined stop)

/-- **A summary that names positions only holds whatever the relation of written operations**:
a definition that satisfies it for one relation satisfies it for every other. -/
theorem Summary.holds_positional {D : Dialect} {Raw : Type} {sem : Semantics D}
    {permitted : ∀ op, sem.S.Reply op → Prop} {R : Reading sem.Dyn}
    {Run Run' : Raw → List sem.Dyn → List sem.Dyn → Prop} {Valid : sem.Dyn → Prop}
    {undefined : sem.H → Prop} {summary : Summary Raw} {inputs results : Nat}
    (positional : summary.Positional inputs results) {ins outs : List D.Ty}
    {run : HList sem.Val ins → Process sem.S sem.H (HList sem.Val outs)}
    (holds : Summary.Holds sem permitted R Run Valid undefined summary run) :
    Summary.Holds sem permitted R Run' Valid undefined summary run := by
  intro values valid required
  exact Process.every_mono _ _
    (fun returned post => ⟨post.1, fun guarantee listed =>
      Requirement.holds_positional (positional.ensures guarantee listed) (post.2 guarantee listed)⟩)
    (fun _ stop => stop)
    (holds values valid fun requirement listed =>
      Requirement.holds_positional (positional.requires requirement listed)
        (required requirement listed))

end Zkc.Core
