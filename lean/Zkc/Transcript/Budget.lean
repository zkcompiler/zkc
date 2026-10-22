module

public import Zkc.Transcript.Interface
public import Zkc.Semantics.Interaction
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Prod
public import Mathlib.Algebra.Order.Pi
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Order.Group.Nat

@[expose] public section

/-! # Path bounds over processes

A path bound charges the operations on every path of a process against a budget.
A walk (`Walk`) states how: at each position, which operations are admitted (a
shape admissibility, kept apart from charges), what an operation costs, and
which positions follow each reply. `Walk.Bound` holds when every path from a
position charges at most the budget and admits every operation it performs.

The combinators are shared; the metrics stay distinct. Costs form an additive
commutative monoid with an order on which addition is monotone, so vector
budgets, one coordinate per kind of resource, are allowed:

- `Walk.Bound.mono` raises the budget;
- `Walk.Bound.bind` sequences two bounded processes, `Walk.Bound.repeatN`
  bounds a repetition by its count times the body's budget, both over
  nonnegative costs;
- `Walk.Bound.convert` converts one metric into another by a monotone additive
  map that dominates the target walk's charges, on the target walk's paths.

Transcript interfaces give two families of walks (`Interface.walk`,
`Interface.replyWalk`): positions are absorbed histories, and a receive
continues only with the replies its absorbed events recover; or there is no
position, and a receive continues with every reply. Their metrics are the
transcript queries (`Interface.queryCharge`), the weighted security loss of a
per-key charge (`Interface.lossCharge`), and the counts of queries and messages
(`Interface.messageQueryCharge`), from which a provider's primitive calls follow
by a conversion. The executable instruction budget is a separate operational
contract: its exhaustion changes behaviour and its charges depend on executable
environments, so it is not a walk.
-/

set_option autoImplicit false

namespace Zkc.Transcript

/-- How a path bound walks a process over the operations of `I`: the operations
admitted at a position, the charge of an operation at a position, and the
positions after each reply. -/
structure Walk (I : PIR.Signature) (Position Cost : Type) where
  admits : Position → I.Op → Prop
  charge : Position → I.Op → Cost
  next : Position → (operation : I.Op) → I.Reply operation → Position → Prop

namespace Walk
variable {I : PIR.Signature} {Position Cost A B : Type}

/-- Every path of the process from `position` admits its operations and charges
at most `budget`. -/
def Bound [Add Cost] [LE Cost] (walk : Walk I Position Cost) :
    PIR.Process I A → Position → Cost → Prop
  | .done _, _, _ => True
  | .halt _, _, _ => True
  | .call operation next, position, budget =>
      walk.admits position operation ∧ ∃ remaining,
        walk.charge position operation + remaining ≤ budget ∧
          ∀ reply after, walk.next position operation reply after →
            Bound walk (next reply) after remaining

/-- One step of a path bound. -/
theorem bound_call [Add Cost] [LE Cost] (walk : Walk I Position Cost) (operation : I.Op)
    (next : I.Reply operation → PIR.Process I A) (position : Position) (budget : Cost) :
    walk.Bound (.call operation next) position budget ↔
      walk.admits position operation ∧ ∃ remaining,
        walk.charge position operation + remaining ≤ budget ∧
          ∀ reply after, walk.next position operation reply after →
            walk.Bound (next reply) after remaining :=
  Iff.rfl

variable [AddCommMonoid Cost] [Preorder Cost] (walk : Walk I Position Cost)

/-- A larger budget keeps the bound. -/
theorem Bound.mono :
    ∀ (process : PIR.Process I A) {position : Position} {budget larger : Cost},
      walk.Bound process position budget → budget ≤ larger → walk.Bound process position larger
  | .done _, _, _, _, _, _ => trivial
  | .halt _, _, _, _, _, _ => trivial
  | .call _ _, _, _, _, ⟨admitted, remaining, charged, after⟩, le =>
      ⟨admitted, remaining, charged.trans le, after⟩

variable [IsOrderedAddMonoid Cost]

/-- Sequencing: a head bounded by `first` followed by continuations bounded by
`second` from every position is bounded by `first + second`. -/
theorem Bound.bind (nonneg : ∀ cost : Cost, 0 ≤ cost) (continuation : A → PIR.Process I B)
    {second : Cost} (bounded : ∀ value position, walk.Bound (continuation value) position second) :
    ∀ (head : PIR.Process I A) {position : Position} {first : Cost},
      walk.Bound head position first →
        walk.Bound (head.bind continuation) position (first + second)
  | .done value, position, first, _ =>
      Bound.mono walk _ (bounded value position) (le_add_of_nonneg_left (nonneg first))
  | .halt _, _, _, _ => trivial
  | .call operation next, position, first, ⟨admitted, remaining, charged, after⟩ =>
      ⟨admitted, remaining + second, by rw [← add_assoc]; exact add_le_add_left charged second,
        fun reply later step =>
          Bound.bind nonneg continuation bounded (next reply) (after reply later step)⟩

/-- Repetition: `count` iterations of a body bounded by `each` from every state
and position are bounded by `count • each`. -/
theorem Bound.repeatN (nonneg : ∀ cost : Cost, 0 ≤ cost) (step : A → PIR.Process I A) {each : Cost}
    (bounded : ∀ state position, walk.Bound (step state) position each) :
    ∀ (count : ℕ) (state : A) (position : Position),
      walk.Bound (PIR.repeatN count step state) position (count • each)
  | 0, _, _ => trivial
  | count + 1, state, position => by
      have sequenced := Bound.bind walk nonneg (PIR.repeatN count step)
        (fun value position => Bound.repeatN nonneg step bounded count value position)
        (step state) (bounded state position)
      rw [succ_nsmul', show PIR.repeatN (count + 1) step state =
        (step state).bind (PIR.repeatN count step) from rfl]
      exact sequenced

omit [IsOrderedAddMonoid Cost] in
/-- Conversion between metrics: a monotone additive map that dominates the
target walk's charges converts a bound on the source walk into one on the
target walk, which admits at least the source's operations and follows a subset
of its transitions. -/
theorem Bound.convert {Cost' : Type} [AddCommMonoid Cost'] [Preorder Cost']
    (target : Walk I Position Cost') (convert : Cost →+ Cost') (monotone : Monotone convert)
    (admits : ∀ position operation, walk.admits position operation →
      target.admits position operation)
    (dominates : ∀ position operation,
      target.charge position operation ≤ convert (walk.charge position operation))
    (follows : ∀ position operation reply after, target.next position operation reply after →
      walk.next position operation reply after)
    [IsOrderedAddMonoid Cost'] :
    ∀ (process : PIR.Process I A) {position : Position} {budget : Cost},
      walk.Bound process position budget → target.Bound process position (convert budget)
  | .done _, _, _, _ => trivial
  | .halt _, _, _, _ => trivial
  | .call operation next, position, budget, ⟨admitted, remaining, charged, after⟩ =>
      ⟨admits position operation admitted, convert remaining,
        calc target.charge position operation + convert remaining
            ≤ convert (walk.charge position operation) + convert remaining :=
              add_le_add_left (dominates position operation) _
          _ = convert (walk.charge position operation + remaining) := (map_add convert _ _).symm
          _ ≤ convert budget := monotone charged,
        fun reply later step =>
          Bound.convert target convert monotone admits dominates follows (next reply)
            (after reply later (follows position operation reply later step))⟩

end Walk

section Interface
variable {I : PIR.Signature} {E P : Type} {Raw : E → Type} {Cost : Type}

/-- The walk of a transcript interface: positions are absorbed histories, a
receive continues with the replies its absorbed events recover, a send with its
fixed reply, a query with every reply, and a refusal stops. Every operation is
admitted. -/
def Interface.walk (absorb : Interface I E P Raw) (charge : List E → I.Op → Cost) :
    Walk I (List E) Cost where
  admits _ _ := True
  charge := charge
  next history operation reply after :=
    match absorb operation with
    | .receive event recover =>
        ∃ message, recover (event message) = some reply ∧ after = history ++ [event message]
    | .send event value => reply = value ∧ after = history ++ [event]
    | .query event _ => after = history ++ [event]
    | .refuse => False

@[simp] theorem Interface.walk_admits (absorb : Interface I E P Raw) (charge : List E → I.Op → Cost)
    (history : List E) (operation : I.Op) : (absorb.walk charge).admits history operation = True :=
  rfl

@[simp] theorem Interface.walk_charge (absorb : Interface I E P Raw) (charge : List E → I.Op → Cost)
    (history : List E) (operation : I.Op) :
    (absorb.walk charge).charge history operation = charge history operation :=
  rfl

theorem Interface.walk_next (absorb : Interface I E P Raw) (charge : List E → I.Op → Cost)
    (history : List E) (operation : I.Op) (reply : I.Reply operation) (after : List E) :
    (absorb.walk charge).next history operation reply after =
      match absorb operation with
      | .receive event recover =>
          ∃ message, recover (event message) = some reply ∧ after = history ++ [event message]
      | .send event value => reply = value ∧ after = history ++ [event]
      | .query event _ => after = history ++ [event]
      | .refuse => False :=
  rfl

/-- The walk of a transcript interface without positions: a receive and a query
continue with every reply, a send with its fixed reply, and a refusal stops. -/
def Interface.replyWalk (absorb : Interface I E P Raw) (charge : I.Op → Cost) : Walk I Unit Cost where
  admits _ _ := True
  charge _ := charge
  next _ operation reply _ :=
    match absorb operation with
    | .receive _ _ => True
    | .send _ value => reply = value
    | .query _ _ => True
    | .refuse => False

@[simp] theorem Interface.replyWalk_admits (absorb : Interface I E P Raw) (charge : I.Op → Cost)
    (position : Unit) (operation : I.Op) : (absorb.replyWalk charge).admits position operation = True :=
  rfl

@[simp] theorem Interface.replyWalk_charge (absorb : Interface I E P Raw) (charge : I.Op → Cost)
    (position : Unit) (operation : I.Op) :
    (absorb.replyWalk charge).charge position operation = charge operation :=
  rfl

theorem Interface.replyWalk_next (absorb : Interface I E P Raw) (charge : I.Op → Cost)
    (position : Unit) (operation : I.Op) (reply : I.Reply operation) (after : Unit) :
    (absorb.replyWalk charge).next position operation reply after =
      match absorb operation with
      | .receive _ _ => True
      | .send _ value => reply = value
      | .query _ _ => True
      | .refuse => False :=
  rfl

/-- The transcript-query metric: one per query. -/
def Interface.queryCharge (absorb : Interface I E P Raw) (operation : I.Op) : ℕ :=
  match absorb operation with
  | .query _ _ => 1
  | _ => 0

/-- The weighted-loss metric of a per-key charge: a query is charged its key,
the history before it and its occurrence. -/
def Interface.lossCharge [Zero Cost] (absorb : Interface I E P Raw) (charge : List E → E → Cost)
    (history : List E) (operation : I.Op) : Cost :=
  match absorb operation with
  | .query event _ => charge history event
  | _ => 0

/-- The weighted-loss metric of an error per occurrence. -/
def Interface.errorCharge [Zero Cost] (absorb : Interface I E P Raw) (error : E → Cost)
    (operation : I.Op) : Cost :=
  match absorb operation with
  | .query event _ => error event
  | _ => 0

/-- Counts of queries and of received and sent messages, as a vector budget. -/
def Interface.messageQueryCharge (absorb : Interface I E P Raw) (operation : I.Op) : ℕ × ℕ :=
  match absorb operation with
  | .query _ _ => (1, 0)
  | .receive _ _ => (0, 1)
  | .send _ _ => (0, 1)
  | .refuse => (0, 0)

end Interface

end Zkc.Transcript
