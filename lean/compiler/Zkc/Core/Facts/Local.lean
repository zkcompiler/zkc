module

public import Zkc.Core.Facts.State
public import Zkc.Core.Program.LocalRules

@[expose] public section

/-!
What the analysis knows of the written operations of a function, and what the local dialect
tells it.

Per written operation: what it requires (the table of requirements), the ranges of its natural
results from those of its operands (the table of ranges of arithmetic), and how its result
reads. One value for `LocalRaw V`: a role program's computations are local operations and read
it too. Every operation of a function is a value, by its written form, except a call of a
function that can stop with a reason, which is kept in order; and the operations that the core
owns whose meaning is symmetric in two operands of one type commute (`OwnedName.commutes`), a
row of the vocabulary and a call do not (`localFactRules`). Following decides types and
performers by equality and two operations by their written forms (`localSkelRules`).
-/

namespace Zkc.Core

namespace Range

/-- The ranges of a sum. -/
def add : Option Range → Option Range → Option Range
  | some a, some b => some ⟨a.lo + b.lo, match a.hi, b.hi with
      | some x, some y => some (x + y)
      | _, _ => none⟩
  | _, _ => none

/-- The ranges of a difference, not below zero. -/
def sub : Option Range → Option Range → Option Range
  | some a, some b => some ⟨match b.hi with | some y => a.lo - y | none => 0, a.hi.map (· - b.lo)⟩
  | _, _ => none

/-- The ranges of a product. -/
def mul : Option Range → Option Range → Option Range
  | some a, some b => some ⟨a.lo * b.lo, match a.hi, b.hi with
      | some x, some y => some (x * y)
      | _, _ => none⟩
  | _, _ => none

/-- The ranges of a quotient rounded down, where the divisor is at least one. -/
def div : Option Range → Option Range → Option Range
  | some a, some b => some ⟨match b.hi with | some y => a.lo / y | none => 0,
      a.hi.map (· / max b.lo 1)⟩
  | _, _ => none

/-- The ranges of a remainder, where the divisor is at least one. -/
def rem : Option Range → Option Range → Option Range
  | some a, some b => some ⟨0, match a.hi, b.hi with
      | some x, some y => some (min x (y - 1))
      | some x, none => some x
      | none, some y => some (y - 1)
      | none, none => none⟩
  | _, _ => none

/-- The number of binary digits of a natural, within a number of steps: none for zero. -/
def digitsWithin : Nat → Nat → Nat
  | 0, _ => 0
  | steps + 1, n => if n = 0 then 0 else digitsWithin steps (n / 2) + 1

/-- The number of binary digits of a natural, zero being written with one. -/
def binaryDigits (n : Nat) : Nat := if n = 0 then 1 else digitsWithin n n

/-- Whether an end of the range of a power is computed: when its exponent times the number of
binary digits of its base is at most 65536 (TY8). -/
def powComputed (base exponent : Nat) : Bool := decide (exponent * binaryDigits base ≤ 65536)

/-- The ranges of a power: a number to the power zero is one. An end whose power would be too
large to compute is not computed: the lower end is then one when the base is at least one, and
the upper end is absent. -/
def pow : Option Range → Option Range → Option Range
  | some a, some b =>
      some ⟨if 1 ≤ a.lo then (if powComputed a.lo b.lo then a.lo ^ b.lo else 1)
          else if b.hi = some 0 then 1 else 0,
        match a.hi, b.hi with
        | some x, some y =>
            if powComputed x y then some (max (x ^ y) (if b.lo = 0 then 1 else 0)) else none
        | _, _ => none⟩
  | _, _ => none

end Range

namespace Range

theorem add_has {a b : Option Range} {x y : Nat} (ha : ∀ r, a = some r → r.Has x)
    (hb : ∀ r, b = some r → r.Has y) : ∀ r, Range.add a b = some r → r.Has (x + y) := by
  intro r e
  cases a with
  | none => simp [Range.add] at e
  | some a =>
      cases b with
      | none => simp [Range.add] at e
      | some b =>
          simp only [Range.add, Option.some.injEq] at e
          subst e
          obtain ⟨la, ua⟩ := ha a rfl
          obtain ⟨lb, ub⟩ := hb b rfl
          refine ⟨by simp only; omega, fun h e => ?_⟩
          rcases a with ⟨alo, _ | ahi⟩ <;> rcases b with ⟨blo, _ | bhi⟩ <;> simp at e
          have := ua ahi rfl
          have := ub bhi rfl
          omega

theorem sub_has {a b : Option Range} {x y : Nat} (ha : ∀ r, a = some r → r.Has x)
    (hb : ∀ r, b = some r → r.Has y) : ∀ r, Range.sub a b = some r → r.Has (x - y) := by
  intro r e
  cases a with
  | none => simp [Range.sub] at e
  | some a =>
      cases b with
      | none => simp [Range.sub] at e
      | some b =>
          simp only [Range.sub, Option.some.injEq] at e
          subst e
          obtain ⟨la, ua⟩ := ha a rfl
          obtain ⟨lb, ub⟩ := hb b rfl
          rcases a with ⟨alo, ahi⟩
          rcases b with ⟨blo, _ | bhi⟩
          · have la : alo ≤ x := la
            have lb : blo ≤ y := lb
            refine ⟨Nat.zero_le _, fun h e => ?_⟩
            cases ahi with
            | none => cases e
            | some ahi =>
                simp only [Option.map_some, Option.some.injEq] at e
                subst e
                have := ua ahi rfl
                omega
          · have la : alo ≤ x := la
            have lb : blo ≤ y := lb
            have hy := ub bhi rfl
            refine ⟨by show alo - bhi ≤ x - y; omega, fun h e => ?_⟩
            cases ahi with
            | none => cases e
            | some ahi =>
                simp only [Option.map_some, Option.some.injEq] at e
                subst e
                have := ua ahi rfl
                omega

theorem mul_has {a b : Option Range} {x y : Nat} (ha : ∀ r, a = some r → r.Has x)
    (hb : ∀ r, b = some r → r.Has y) : ∀ r, Range.mul a b = some r → r.Has (x * y) := by
  intro r e
  cases a with
  | none => simp [Range.mul] at e
  | some a =>
      cases b with
      | none => simp [Range.mul] at e
      | some b =>
          simp only [Range.mul, Option.some.injEq] at e
          subst e
          obtain ⟨la, ua⟩ := ha a rfl
          obtain ⟨lb, ub⟩ := hb b rfl
          refine ⟨Nat.mul_le_mul la lb, fun h e => ?_⟩
          rcases a with ⟨alo, _ | ahi⟩ <;> rcases b with ⟨blo, _ | bhi⟩ <;> simp at e
          subst e
          exact Nat.mul_le_mul (ua ahi rfl) (ub bhi rfl)

theorem div_has {a b : Option Range} {x y : Nat} (ha : ∀ r, a = some r → r.Has x)
    (hb : ∀ r, b = some r → r.Has y) (pos : 1 ≤ y) :
    ∀ r, Range.div a b = some r → r.Has (x / y) := by
  intro r e
  cases a with
  | none => simp [Range.div] at e
  | some a =>
      cases b with
      | none => simp [Range.div] at e
      | some b =>
          simp only [Range.div, Option.some.injEq] at e
          subst e
          obtain ⟨la, ua⟩ := ha a rfl
          obtain ⟨lb, ub⟩ := hb b rfl
          refine ⟨?_, fun h e => ?_⟩
          · cases hbh : b.hi with
            | none => simp
            | some yh =>
                simp only
                have := ub yh hbh
                exact Nat.le_trans (Nat.div_le_div_right la) (Nat.div_le_div_left this pos)
          · cases hah : a.hi with
            | none => rw [hah] at e; cases e
            | some xh =>
                rw [hah] at e
                simp only [Option.map_some, Option.some.injEq] at e
                subst e
                exact Nat.le_trans (Nat.div_le_div_right (ua xh hah))
                  (Nat.div_le_div_left (Nat.max_le.mpr ⟨lb, pos⟩) (by omega))

theorem rem_has {a b : Option Range} {x y : Nat} (ha : ∀ r, a = some r → r.Has x)
    (hb : ∀ r, b = some r → r.Has y) (pos : 1 ≤ y) :
    ∀ r, Range.rem a b = some r → r.Has (x % y) := by
  intro r e
  cases a with
  | none => simp [Range.rem] at e
  | some a =>
      cases b with
      | none => simp [Range.rem] at e
      | some b =>
          simp only [Range.rem, Option.some.injEq] at e
          subst e
          obtain ⟨_, ua⟩ := ha a rfl
          obtain ⟨_, ub⟩ := hb b rfl
          have lt := Nat.mod_lt x (by omega : y > 0)
          have le := Nat.mod_le x y
          refine ⟨Nat.zero_le _, fun h e => ?_⟩
          rcases a with ⟨alo, _ | ahi⟩ <;> rcases b with ⟨blo, _ | bhi⟩ <;>
            simp only [Option.some.injEq, reduceCtorEq] at e
          · subst e
            have := ub bhi rfl
            omega
          · subst e
            have := ua ahi rfl
            omega
          · subst e
            have := ua ahi rfl
            have := ub bhi rfl
            exact Nat.le_min.mpr ⟨by omega, by omega⟩

theorem pow_has {a b : Option Range} {x y : Nat} (ha : ∀ r, a = some r → r.Has x)
    (hb : ∀ r, b = some r → r.Has y) : ∀ r, Range.pow a b = some r → r.Has (x ^ y) := by
  intro r e
  cases a with
  | none => simp [Range.pow] at e
  | some a =>
      cases b with
      | none => simp [Range.pow] at e
      | some b =>
          simp only [Range.pow, Option.some.injEq] at e
          subst e
          obtain ⟨la, ua⟩ := ha a rfl
          obtain ⟨lb, ub⟩ := hb b rfl
          refine ⟨?_, fun h e => ?_⟩
          · simp only
            split
            · next one =>
                split
                · exact Nat.le_trans (Nat.pow_le_pow_left la _)
                    (Nat.pow_le_pow_right (by omega) lb)
                · exact Nat.pow_pos (by omega)
            · split
              · next zero =>
                  have := ub 0 zero
                  have : y = 0 := by omega
                  subst this
                  simp
              · exact Nat.zero_le _
          · rcases a with ⟨alo, _ | ahi⟩ <;> rcases b with ⟨blo, _ | bhi⟩ <;>
              simp only [reduceCtorEq] at e
            split at e
            · simp only [Option.some.injEq] at e
              subst e
              have hx := ua ahi rfl
              have hy := ub bhi rfl
              simp only at lb
              cases x with
              | zero =>
                  cases y with
                  | zero =>
                      have : blo = 0 := by omega
                      subst this
                      exact Nat.le_max_right _ _
                  | succ y => simp
              | succ x =>
                  exact Nat.le_trans (Nat.le_trans (Nat.pow_le_pow_left hx _)
                    (Nat.pow_le_pow_right (by omega) hy)) (Nat.le_max_left _ _)
            · cases e

end Range

section
variable {V : Vocabulary}

/-- The written length of a sequence of the type. -/
def lengthOfType (τ : V.Ty) : LocalRaw V := .owned .seqLength [τ] []

/-- What an operation that the core owns requires of an application, by its operands'
positions. -/
def ownedRequires : OwnedName → List V.Ty → List (Requirement (LocalRaw V))
  | .natSub, _ => [.le (.arg 1) (.arg 0)]
  | .natDiv, _ => [.atLeast (.arg 1) 1]
  | .natRem, _ => [.atLeast (.arg 1) 1]
  | .seqAt, [.seq _ (some size)] => [.below (.arg 1) size]
  | .seqAt, [.seq item none] => [.lt (.arg 1) (.apply (lengthOfType (.seq item none)) [0])]
  | .seqSlice, [.seq item size, .seq _ result] =>
      [.le (.arg 1) (.arg 2), .le (.arg 2) (.apply (lengthOfType (.seq item size)) [0])] ++
        (match result with
          | some count => [.difference (.arg 2) (.arg 1) count]
          | none => [])
  | .seqSized, [.seq item (some size)] =>
      [.exactly (.apply (lengthOfType (.seq item none)) [0]) size]
  | .natBelow, [.fin bound] => [.below (.arg 0) bound]
  | _, _ => []

/-- What a row requires: a restricted one, its domain row at the same operands known true. -/
def rowRequires (key : V.RowKey) : List (Requirement (LocalRaw V)) :=
  match V.row key with
  | some signature =>
      match signature.kind with
      | .pure => []
      | .restricted domain => [.holds (.apply (.row domain) (List.range signature.ins.length))]
  | none => []

/-- The range of the result of an operation on two naturals, from those of its operands. -/
def Range.onTwo (f : Option Range → Option Range → Option Range) :
    List (Option Range) → List (Option Range)
  | [a, b] => [f a b]
  | _ => []

/-- The range of the result of an operation that returns its one operand. -/
def Range.onOne : List (Option Range) → List (Option Range)
  | [a] => [a]
  | _ => []

theorem onTwo_has {f : Option Range → Option Range → Option Range} {known : List (Option Range)}
    {x y z : Nat}
    (sound : ∀ ka kb, (∀ r, ka = some r → r.Has x) → (∀ r, kb = some r → r.Has y) →
      ∀ r, f ka kb = some r → r.Has z)
    (hx : ∀ r, known[0]? = some (some r) → r.Has x)
    (hy : ∀ r, known[1]? = some (some r) → r.Has y) :
    ∀ (i : Nat) (r : Range), (Range.onTwo f known)[i]? = some (some r) → i = 0 ∧ r.Has z := by
  intro i r e
  match known, hx, hy with
  | [ka, kb], hx, hy =>
      simp only [Range.onTwo] at e
      cases i with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at e
          exact ⟨rfl, sound ka kb (fun r h => hx r (by simp [h])) (fun r h => hy r (by simp [h]))
            r e⟩
      | succ i => simp at e
  | [], _, _ => simp [Range.onTwo] at e
  | [_], _, _ => simp [Range.onTwo] at e
  | _ :: _ :: _ :: _, _, _ => simp [Range.onTwo] at e

theorem onOne_has {known : List (Option Range)} {x : Nat}
    (hx : ∀ r, known[0]? = some (some r) → r.Has x) :
    ∀ (i : Nat) (r : Range), (Range.onOne known)[i]? = some (some r) → i = 0 ∧ r.Has x := by
  intro i r e
  match known, hx with
  | [ka], hx =>
      simp only [Range.onOne] at e
      cases i with
      | zero => exact ⟨rfl, hx r (by simpa using e)⟩
      | succ i => simp at e
  | [], _ => simp [Range.onOne] at e
  | _ :: _ :: _, _ => simp [Range.onOne] at e

/-- The ranges of the natural results of an operation that the core owns, from those of its
operands. -/
def ownedRanges : OwnedName → List V.Ty → List (Option Range) → List (Option Range)
  | .natAdd, _ => Range.onTwo Range.add
  | .natSub, _ => Range.onTwo Range.sub
  | .natMul, _ => Range.onTwo Range.mul
  | .natDiv, _ => Range.onTwo Range.div
  | .natRem, _ => Range.onTwo Range.rem
  | .natPow, _ => Range.onTwo Range.pow
  | .seqLength, [.seq _ (some size)] => fun _ => [some (Range.point size)]
  | .seqLength, [.seq _ none] => fun _ => [some ⟨0, none⟩]
  | .natBelow, _ => Range.onOne
  | .finToNat, _ => Range.onOne
  | .finWiden, _ => Range.onOne
  | _, _ => fun _ => []

/-- What the data of a literal says of its natural. -/
def literalRanges : V.Ty → List Nat → List (Option Range)
  | .nat, [n] => [some (Range.point n)]
  | .fin _, [n] => [some (Range.point n)]
  | _, _ => []

/-- How the first result of a written operation reads. -/
def localForm : LocalRaw V → Option ResultForm
  | .owned .natAdd _ _ => some .sum
  | .owned .natSub _ _ => some .difference
  | .owned .natLess _ _ => some .less
  | .owned .natEqual _ _ => some .equal
  | .owned .boolNot _ _ => some .negation
  | .owned .boolAnd _ _ => some .conjunction
  | .owned .boolOr _ _ => some .disjunction
  | .literal .bool [0] => some (.truth false)
  | .literal .bool [1] => some (.truth true)
  | _ => none

variable (V) in
/-- What the check of facts knows of the written operations of a function. -/
def localOpFacts : OpFacts (LocalRaw V) where
  requires
    | .owned name types _ => ownedRequires name types
    | .row key => rowRequires key
    | _ => []
  ranges
    | .owned name types _, operands => ownedRanges name types operands
    | .literal τ data, _ => literalRanges τ data
    | _, _ => []
  form := localForm

/-- What the type of a natural says of it. -/
def localRange : V.Ty → Option Range
  | .nat => some ⟨0, none⟩
  | .fin bound => some (if bound = 0 then Range.nothing else ⟨0, some (bound - 1)⟩)
  | _ => none

/-- The number by which the table places the applications of a written operation of a function:
it tells apart the literals by their data, the operations that the core owns by their name and
numbers, and the calls by their callee; the rows share one. -/
def localPlace : LocalRaw V → Nat
  | .row _ => 0
  | .owned name _ numbers => FactCheck.mixNumbers (4 * name.ctorIdx + 1) numbers
  | .literal _ data => FactCheck.mixNumbers 2 data
  | .call callee => 4 * callee.number + 3

/-- Whether an operation that the core owns gives, on two operands of one type, a result that
does not depend on their order, for all values (`Meaning/Local.lean`): the sum and the product
of naturals, the conjunction and the disjunction of truth values, and the equality of naturals
and of truth values. Not the difference, the quotient, the remainder, the power or the order of
naturals; not a concatenation, nor a sequence, a tuple or a record made of two values of one
type, whose order is in the result. -/
def OwnedName.commutes : OwnedName → Bool
  | .natAdd | .natMul | .natEqual | .boolAnd | .boolOr | .boolEqual => true
  | .natSub | .natDiv | .natRem | .natPow | .natLess | .boolNot => false
  | .seqLength | .seqAt | .seqSlice | .seqConcat | .seqFill | .seqSized | .natBelow => false
  | .seqUnsized | .finToNat | .finWiden | .make | .get | .take | .variant => false

/-- Whether a written operation of a function commutes: an operation that the core owns, as it
is written (with no types and no numbers), when `OwnedName.commutes` says so. A row of the
vocabulary does not commute here, whatever a model does: that a row commutes would be a law that
every model must satisfy, which needs the model and is a later piece. A call does not commute:
nothing says that the callee's result does not depend on the order of its inputs. -/
def LocalRaw.commutes : LocalRaw V → Bool
  | .owned name [] [] => name.commutes
  | .owned _ (_ :: _) _ => false
  | .owned _ [] (_ :: _) => false
  | .row _ => false
  | .literal _ _ => false
  | .call _ => false

variable (V) in
/-- What the local dialect tells the analysis: every operation of a function is a value, by its
written form, except a call of a function that can stop with a reason, which is kept in order;
an operation that the core owns whose meaning is symmetric in its two operands commutes
(`LocalRaw.commutes`). -/
def localFactRules (fns : List (FnHeader V)) : FactRules (localDialect V fns) (LocalRaw V) where
  written := fun o => bif LocalOp.canStop o then none else some (LocalOp.print o)
  commutes := LocalRaw.commutes
  range := localRange
  noValue := Ty.noValue
  ops := localOpFacts V
  place := localPlace

variable (V) in
/-- What following decides for a function: types and performers by equality, and two operations
by their written forms. -/
def localSkelRules (fns : List (FnHeader V)) : SkelRules (localDialect V fns) where
  sameTy := inferInstanceAs (DecidableEq V.Ty)
  sameWho := inferInstanceAs (DecidableEq Unit)
  sameOp := fun o o' => decide (LocalOp.print o = LocalOp.print o')

end

end Zkc.Core
