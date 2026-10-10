import Mathlib.Data.List.Defs

/-! A finite, proof-producing requirement language for generic source.

Equality is congruence over named associated members and pure applications.
Relations retain every argument. Only explicitly installed unary implications can strengthen a fact.
This layer does not prove installed algebraic or cryptographic declarations;
soundness is relative to their stated interpretation and satisfied assumptions.
-/

set_option autoImplicit false

namespace Zkc.Source.Requirements

inductive Term where
  | root (name : String)
  | project (base : Term) (member : String)
  | apply (head : String) (arguments : List Term)
  deriving Repr, BEq, Hashable

-- Nested lists require an explicit structural decision procedure. This also
-- keeps executable certificate equality independent of a classical oracle.
mutual
  private def termDecEq (a b : Term) : Decidable (a = b) :=
    match a, b with
    | .root x, .root y => decidable_of_iff (x = y) (by simp)
    | .project x m, .project y n =>
        haveI := termDecEq x y
        decidable_of_iff (x = y ∧ m = n) (by simp)
    | .apply f xs, .apply g ys =>
        haveI := termsDecEq xs ys
        decidable_of_iff (f = g ∧ xs = ys) (by simp)
    | .root _, .project _ _ | .root _, .apply _ _ |
      .project _ _, .root _ | .project _ _, .apply _ _ |
      .apply _ _, .root _ | .apply _ _, .project _ _ => isFalse (by intro h; cases h)
  private def termsDecEq (xs ys : List Term) : Decidable (xs = ys) :=
    match xs, ys with
    | [], [] => isTrue rfl
    | x :: xs, y :: ys =>
        haveI := termDecEq x y
        haveI := termsDecEq xs ys
        decidable_of_iff (x = y ∧ xs = ys) (by simp)
    | [], _ :: _ | _ :: _, [] => isFalse (by intro h; cases h)
end
instance : DecidableEq Term := termDecEq

inductive Predicate where
  | equal (left right : Term)
  | relation (name : String) (arguments : List Term)
  deriving DecidableEq, Repr, BEq, Hashable

structure Implication where
  premise : String
  conclusion : String
  deriving DecidableEq, Repr

/-- The semantic interpretation of static identities and their associated
members. Runtime values, target eligibility and assurance levels are separate. -/
structure Model where
  Identity : Type
  root : String → Identity
  project : Identity → String → Identity
  relation : String → List Identity → Prop
  apply : String → List Identity → Identity := fun head _ => root head

def Term.denote (model : Model) : Term → model.Identity
  | .root name => model.root name
  | .project base member => model.project (base.denote model) member
  | .apply head arguments => model.apply head (arguments.map (Term.denote model))

def Predicate.Holds (model : Model) : Predicate → Prop
  | .equal left right => left.denote model = right.denote model
  | .relation name arguments => model.relation name (arguments.map (Term.denote model))

def Implication.Holds (model : Model) (rule : Implication) : Prop :=
  ∀ identity, model.relation rule.premise [identity] →
    model.relation rule.conclusion [identity]

/-- Derivations use the public promises as assumptions. Body obligations must
be conclusions; the implication direction cannot be reversed. -/
inductive Derives (assumptions : List Predicate) (rules : List Implication) : Predicate → Prop
  | assumption {p} : p ∈ assumptions → Derives assumptions rules p
  | reflexivity (term) : Derives assumptions rules (.equal term term)
  | symmetry {left right} : Derives assumptions rules (.equal left right) →
      Derives assumptions rules (.equal right left)
  | transitivity {left middle right} :
      Derives assumptions rules (.equal left middle) →
      Derives assumptions rules (.equal middle right) →
      Derives assumptions rules (.equal left right)
  | projection {left right} (member) : Derives assumptions rules (.equal left right) →
      Derives assumptions rules (.equal (.project left member) (.project right member))
  | application {left right} (head) :
      List.Forall₂ (fun a b => Derives assumptions rules (.equal a b)) left right →
      Derives assumptions rules (.equal (.apply head left) (.apply head right))
  | transport {name left right} : Derives assumptions rules (.relation name left) →
      List.Forall₂ (fun a b => Derives assumptions rules (.equal a b)) left right →
      Derives assumptions rules (.relation name right)
  | implication {rule term} : rule ∈ rules →
      Derives assumptions rules (.relation rule.premise [term]) →
      Derives assumptions rules (.relation rule.conclusion [term])

theorem Derives.sound {assumptions : List Predicate} {rules : List Implication}
    (model : Model)
    (provided : ∀ p ∈ assumptions, p.Holds model)
    (installed : ∀ r ∈ rules, r.Holds model)
    {p : Predicate} (proof : Derives assumptions rules p) : p.Holds model := by
  induction proof using Derives.rec
      (motive_2 := fun left right _ =>
        left.map (Term.denote model) = right.map (Term.denote model)) with
  | assumption member => exact provided _ member
  | reflexivity => rfl
  | symmetry _ ih => exact ih.symm
  | transitivity _ _ first second => exact first.trans second
  | projection member _ ih =>
      simpa only [Predicate.Holds, Term.denote] using congrArg (fun x => model.project x member) ih
  | application head _ ih =>
      simpa only [Predicate.Holds, Term.denote] using congrArg (model.apply head) ih
  | transport _ _ source arguments =>
      simp only [Predicate.Holds] at source ⊢
      rw [← arguments]
      exact source
  | implication member _ ih => exact installed _ member _ ih
  | nil => rfl
  | cons _ _ head tail => exact congrArg₂ List.cons head tail

/-- A certificate step can only refer to earlier established facts. These
indices are not assumed valid: the executable checker bounds-checks them. -/
inductive Rule where
  | assumption (index : Nat)
  | reflexivity
  | symmetry (premise : Nat)
  | transitivity (first second : Nat)
  | projection (premise : Nat)
  | application (equalities : List Nat)
  | transport (source : Nat) (equalities : List Nat)
  | implication (premise declaration : Nat)
  deriving Repr

structure Step where
  conclusion : Predicate
  rule : Rule
  deriving Repr

abbrev Fact (assumptions : List Predicate) (rules : List Implication) :=
  {p : Predicate // Derives assumptions rules p}

private def equalities {assumptions : List Predicate} {rules : List Implication}
    (previous : Array (Fact assumptions rules)) :
    (left right : List Term) → List Nat →
      Option (PLift (List.Forall₂ (fun a b => Derives assumptions rules (.equal a b)) left right))
  | [], [], [] => some ⟨.nil⟩
  | a :: left, b :: right, index :: rest => do
      let fact ← previous[index]?
      if h : fact.val = .equal a b then
        let tail ← equalities previous left right rest
        return ⟨.cons (h ▸ fact.property) tail.down⟩
      else none
  | _, _, _ => none

/-- Check the actual conclusion and premises of one emitted certificate step.
The returned proof is erased by Lean's compiler; the checks are executable. -/
def checkStep (assumptions : List Predicate) (rules : List Implication)
    (previous : Array (Fact assumptions rules)) (step : Step) :
    Option (Fact assumptions rules) := do
  match step.rule, step.conclusion with
  | .assumption index, p =>
      if h : assumptions[index]? = some p then
        return ⟨p, .assumption (List.mem_of_getElem? h)⟩
      else none
  | .reflexivity, .equal a b =>
      if h : a = b then return ⟨.equal a b, h ▸ .reflexivity a⟩ else none
  | .symmetry index, .equal a b =>
      let fact ← previous[index]?
      if h : fact.val = .equal b a then
        return ⟨.equal a b, .symmetry (h ▸ fact.property)⟩
      else none
  | .transitivity first second, .equal a c =>
      let left ← previous[first]?
      let right ← previous[second]?
      match hleft : left.val with
      | .equal x b =>
          if h : x = a ∧ right.val = .equal b c then
            return ⟨.equal a c, .transitivity (h.1 ▸ hleft ▸ left.property)
              (h.2 ▸ right.property)⟩
          else none
      | _ => none
  | .projection index, .equal (.project a member) (.project b other) =>
      let fact ← previous[index]?
      if h : member = other ∧ fact.val = .equal a b then
        return ⟨.equal (.project a member) (.project b other),
          h.1 ▸ .projection member (h.2 ▸ fact.property)⟩
      else none
  | .application indices, .equal (.apply head left) (.apply other right) =>
      if h : head = other then
        let pairs ← equalities previous left right indices
        return ⟨.equal (.apply head left) (.apply other right),
          h ▸ .application head pairs.down⟩
      else none
  | .transport index indices, .relation name arguments =>
      let fact ← previous[index]?
      match hfact : fact.val with
      | .relation source original =>
          if h : source = name then
            let pairs ← equalities previous original arguments indices
            return ⟨.relation name arguments,
              .transport (h ▸ hfact ▸ fact.property) pairs.down⟩
          else none
      | _ => none
  | .implication index declaration, .relation name [term] =>
      let fact ← previous[index]?
      match hrule : rules[declaration]? with
      | none => none
      | some rule =>
          if h : rule.conclusion = name ∧ fact.val = .relation rule.premise [term] then
            return ⟨.relation name [term], h.1 ▸
              .implication (List.mem_of_getElem? hrule) (h.2 ▸ fact.property)⟩
          else none
  | _, _ => none

def check (assumptions : List Predicate) (rules : List Implication)
    (certificate : List Step) : Option (Array (Fact assumptions rules)) :=
  certificate.foldlM (fun previous step => do
    let fact ← checkStep assumptions rules previous step
    return previous.push fact) #[]

/-- All facts accepted by the executable checker hold under every model of
the declared assumptions and installed implication rules. -/
theorem checked_sound {assumptions : List Predicate} {rules : List Implication}
    (model : Model) (provided : ∀ p ∈ assumptions, p.Holds model)
    (installed : ∀ r ∈ rules, r.Holds model)
    (fact : Fact assumptions rules) : fact.val.Holds model :=
  fact.property.sound model provided installed

end Zkc.Source.Requirements
