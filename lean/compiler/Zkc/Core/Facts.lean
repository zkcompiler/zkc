module

public import Zkc.Core.WellFormed

public section

/-! The check of facts: every application of an operation with a domain is justified.

An operation the core owns may have a domain (`nat.sub`, `nat.div`, `nat.rem`, `seq.at`,
`seq.slice`, `seq.sized`, `nat.below`), and so has a restricted row of the operation
table. Outside its domain the application stops `undefined`. The check computes, for a
region of the local dialect, what is known of its values at every instruction, from the
instructions themselves, and decides at each such application whether what is known puts
the operands in the domain. Nothing is recorded in the program for it.

A value is named by its *level*: its number in its region, the inputs first, then the
results of each instruction in the order they are bound. A level does not change when
later values are bound.

What is tracked:

- for a natural, intervals `lo..hi`, `hi` possibly absent: the interval of the operation
  that made it, and narrower ones from conditions;
- for a value, its *shape*: the operation that made it, on the levels of its operands,
  for the operations that the rules read (`a + b`, `a - b`, the length of a sequence, the
  natural of a `fin`, `a < b`, `a == b` on naturals, `not`, `and`, `or`, a pure row with
  one `bool` output applied to operands);
- orders `a < b` and `a <= b` between naturals;
- the conditions known to be true.

A `guard` gives the facts of its condition to what follows; an `if` gives them to its
first region and the facts of the negation to its second; a `loop` gives its region the
interval of the iteration number and, when the count is a value that the region
captures, the order of the iteration number below it. Facts enter a nested region
through its captures: a fact is kept when every value it mentions is captured.

Three forms have a rule of their own. An `if` on `a` whose second region returns the
literal `false`, or whose first region returns the literal `true`, is `a and b` or
`a or b` with `b` computed under `a`: a condition on its result gives the facts of `a`.
A loop whose region returns a carried natural plus a term has, for that carried result,
the interval of the sum over the iterations. The region of a loop over the count 0 of
the operation never runs, and nothing in it needs a justification.

A region in which a value of a type without a value is in scope never runs either: no
environment gives that value. Whether a type has a value is `Ty.populated`, and it is
decided where values are bound: at the inputs of a function, at the inputs of a nested
region, at the results of an instruction and at the results of a block. What follows in
the region, and every region nested in it, needs no justification.

The check is a separate predicate from residual well-formedness. A program whose
restricted rows name no domain row is well formed, and does not pass.
-/

set_option autoImplicit false

namespace Zkc.Core

open Zkc.Source

/-! ## What is tracked -/

/-- The shape of a value: the operation that made it, on the levels of its operands. -/
inductive Shape where
  | other
  /-- `left + right` on naturals. -/
  | add (left right : Nat)
  /-- `left - right` on naturals. -/
  | sub (left right : Nat)
  /-- The number of elements of a sequence. -/
  | length (sequence : Nat)
  /-- A natural below a bound, as a natural. -/
  | toNat (value : Nat)
  /-- `left < right` on naturals. -/
  | less (left right : Nat)
  /-- `left == right` on naturals. -/
  | equal (left right : Nat)
  | not (condition : Nat)
  | and (left right : Nat)
  | or (left right : Nat)
  /-- The pure row with the number `row` and one `bool` output, applied to operands. -/
  | domain (row : Nat) (operands : List Nat)
  /-- The result of an `if` on `condition` whose second region returns the literal `false`:
  it is true only when the condition is. -/
  | conjunct (condition : Nat)
  /-- The result of an `if` on `condition` whose first region returns the literal `true`:
  it is false only when the condition is. -/
  | disjunct (condition : Nat)
  deriving Repr, Inhabited, DecidableEq

/-- An interval of naturals; without `hi` it has no upper end. -/
structure Interval where
  lo : Nat
  hi : Option Nat
  deriving Repr, Inhabited, DecidableEq

/-- The natural at a level is in an interval. -/
structure Bound where
  level : Nat
  lo : Nat
  hi : Option Nat
  deriving Repr, Inhabited, DecidableEq

/-- The natural at `left` is below the natural at `right`: strictly, or possibly equal. -/
structure Order where
  strict : Bool
  left : Nat
  right : Nat
  deriving Repr, Inhabited, DecidableEq

/-- What is known of the values of a region at one instruction: the shape of each value,
by level, and the bounds, the orders and the conditions known to be true. `dead` marks a
region that never runs, the region of a loop of no iteration or one with a value of a type
without a value in scope: every application in it is justified. -/
structure Facts where
  shapes : List Shape
  bounds : List Bound
  orders : List Order
  known : List Nat
  dead : Bool
  deriving Repr, Inhabited

/-- What is known of one value that a region returns: its interval and, when it is a sum,
each addend with the interval of the other one. A region of a loop that returns its
carried input plus a term is found by the second. -/
structure Returned where
  interval : Interval
  steps : List (Nat × Interval)
  deriving Repr, Inhabited, DecidableEq

/-- What a region returns: what is known of each output, or nothing when the region ends
in a stop on every path the check follows. -/
abbrev Outcome := Option (List Returned)

/-- The smaller of two upper ends. -/
@[expose] def atMost : Option Nat → Option Nat → Option Nat
  | some first, some second => some (min first second)
  | some first, none => some first
  | none, second => second

/-- The largest lower end that the bounds give a level. -/
@[expose] def lowest : List Bound → Nat → Nat
  | [], _ => 0
  | bound :: rest, level =>
      if bound.level = level then max bound.lo (lowest rest level) else lowest rest level

/-- The smallest upper end that the bounds give a level. -/
@[expose] def highest : List Bound → Nat → Option Nat
  | [], _ => none
  | bound :: rest, level =>
      if bound.level = level then atMost bound.hi (highest rest level) else highest rest level

/-- An upper end is at most a limit. -/
@[expose] def within : Option Nat → Nat → Bool
  | some hi, limit => decide (hi ≤ limit)
  | none, _ => false

/-- An upper end is below a limit. -/
@[expose] def below : Option Nat → Nat → Bool
  | some hi, limit => decide (hi < limit)
  | none, _ => false

/-- The levels, from `level` on, of the values whose shape is the length of a sequence. -/
@[expose] def lengthsFrom (sequence : Nat) : List Shape → Nat → List Nat
  | [], _ => []
  | shape :: rest, level =>
      match shape with
      | .length other =>
          if other = sequence then level :: lengthsFrom sequence rest (level + 1)
          else lengthsFrom sequence rest (level + 1)
      | _ => lengthsFrom sequence rest (level + 1)

namespace Facts

/-- Nothing known of `count` values. -/
@[expose] def start (count : Nat) : Facts := ⟨List.replicate count .other, [], [], [], false⟩

/-- The number of values. -/
@[expose] def depth (facts : Facts) : Nat := facts.shapes.length

@[expose] def shape (facts : Facts) (level : Nat) : Shape := facts.shapes.getD level .other

@[expose] def lo (facts : Facts) (level : Nat) : Nat := lowest facts.bounds level

@[expose] def hi (facts : Facts) (level : Nat) : Option Nat := highest facts.bounds level

@[expose] def interval (facts : Facts) (level : Nat) : Interval := ⟨facts.lo level, facts.hi level⟩

/-- The levels of the values whose shape is the length of the sequence at a level. -/
@[expose] def lengths (facts : Facts) (sequence : Nat) : List Nat :=
  lengthsFrom sequence facts.shapes 0

/-- What is known of the value at a level when a region returns it. -/
@[expose] def returned (facts : Facts) (level : Nat) : Returned :=
  ⟨facts.interval level,
    match facts.shape level with
    | .add left right => [(left, facts.interval right), (right, facts.interval left)]
    | _ => []⟩

/-- The facts of a region that never runs. -/
@[expose] def kill (facts : Facts) : Facts := { facts with dead := true }

/-- The facts of a region in which values of the given types are in scope: when one of
the types has no value, the region never runs. -/
@[expose] def inScope (facts : Facts) (types : List Ty) : Facts :=
  cond (Ty.allPopulated types) facts facts.kill

/-- The value at a level has a shape that the instruction itself does not give it. -/
@[expose] def reshape (facts : Facts) (level : Nat) : Option Shape → Facts
  | some shape => { facts with shapes := facts.shapes.set level shape }
  | none => facts

/-- One more bound. -/
@[expose] def bound (facts : Facts) (level lo : Nat) (hi : Option Nat) : Facts :=
  { facts with bounds := ⟨level, lo, hi⟩ :: facts.bounds }

/-- One more order. -/
@[expose] def order (facts : Facts) (strict : Bool) (left right : Nat) : Facts :=
  { facts with orders := ⟨strict, left, right⟩ :: facts.orders }

/-- The value at level 0 is below a captured value, when there is one. -/
@[expose] def orderWhen (facts : Facts) : Option Nat → Facts
  | some captured => facts.order true 0 captured
  | none => facts

/-- A condition known to be true. -/
@[expose] def mark (facts : Facts) (condition : Nat) : Facts :=
  { facts with known := condition :: facts.known }

/-- New values, with their shapes and bounds. -/
@[expose] def after (facts : Facts) (shapes : List Shape) (bounds : List Bound) : Facts :=
  { facts with shapes := facts.shapes ++ shapes, bounds := bounds ++ facts.bounds }

/-! ## What is known -/

/-- `left <= right` is known: the intervals decide it; they are one value; an order says
it; `right` is `left + u` or `u + left`; or `left` is `right - u`. Nothing else is tried. -/
@[expose] def knownLe (facts : Facts) (left right : Nat) : Bool :=
  within (facts.hi left) (facts.lo right) ||
  decide (left = right) ||
  facts.orders.any (fun order => decide (order.left = left) && decide (order.right = right)) ||
  (match facts.shape right with
    | .add first second => decide (first = left) || decide (second = left)
    | _ => false) ||
  (match facts.shape left with
    | .sub first _ => decide (first = right)
    | _ => false)

/-- `left < right` is known: the intervals decide it; an order says it; `right` is
`left + u` or `u + left` with `u` at least 1; `left` is `right - u` with `u` at least 1; or
`left` is `x + t` or `t + x`, and an order says `t < d` for a `d` that is `right - x`: the
index of a range that does not start at 0. Nothing else is tried. -/
@[expose] def knownLt (facts : Facts) (left right : Nat) : Bool :=
  below (facts.hi left) (facts.lo right) ||
  facts.orders.any (fun order =>
    order.strict && decide (order.left = left) && decide (order.right = right)) ||
  (match facts.shape right with
    | .add first second =>
        (decide (first = left) && decide (1 ≤ facts.lo second)) ||
          (decide (second = left) && decide (1 ≤ facts.lo first))
    | _ => false) ||
  (match facts.shape left with
    | .sub first second => decide (first = right) && decide (1 ≤ facts.lo second)
    | .add first second =>
        facts.orders.any fun order =>
          order.strict &&
            (match facts.shape order.right with
              | .sub whole start =>
                  decide (whole = right) &&
                    ((decide (order.left = second) && decide (start = first)) ||
                      (decide (order.left = first) && decide (start = second)))
              | _ => false)
    | _ => false)

/-- The interval of a level is the one point `value`. -/
@[expose] def point (facts : Facts) (level value : Nat) : Bool :=
  decide (value ≤ facts.lo level) && within (facts.hi level) value

/-! ## What a condition gives -/

/-- The upper end below another one. -/
@[expose] def before : Option Nat → Option Nat
  | some hi => some (hi - 1)
  | none => none

/-- The facts of a condition taken true or false. The condition is the value at a level;
its shape says what it compares or combines. `fuel` bounds the conditions followed
through `not`, `and` and `or`. -/
@[expose] def assume : (fuel : Nat) → Facts → (condition : Nat) → (truth : Bool) → Facts
  | 0, facts, condition, truth => cond truth (facts.mark condition) facts
  | fuel + 1, facts, condition, truth =>
      let marked := cond truth (facts.mark condition) facts
      match facts.shape condition, truth with
      | .less left right, true =>
          ((marked.order true left right).bound left 0 (before (facts.hi right))).bound right
            (facts.lo left + 1) none
      | .less left right, false =>
          ((marked.order false right left).bound right 0 (facts.hi left)).bound left
            (facts.lo right) none
      | .equal left right, true =>
          (((marked.order false left right).order false right left).bound left
            (facts.lo right) (facts.hi right)).bound right (facts.lo left) (facts.hi left)
      | .equal left right, false =>
          let first := cond (within (facts.hi right) 0) (marked.bound left 1 none) marked
          cond (within (facts.hi left) 0) (first.bound right 1 none) first
      | .not inner, truth => assume fuel marked inner (!truth)
      | .and left right, true => assume fuel (assume fuel marked left true) right true
      | .or left right, false => assume fuel (assume fuel marked left false) right false
      | .conjunct inner, true => assume fuel marked inner true
      | .disjunct inner, false => assume fuel marked inner false
      | _, _ => marked

/-! ## Entering a nested region -/

/-- The first level, from `inner` on, of a region's input that is the captured value at
`level`. A region's inputs are listed with the level each one captures, or nothing for an
input that is not a capture. -/
@[expose] def sourceOf (level : Nat) : List (Option Nat) → Nat → Option Nat
  | [], _ => none
  | source :: rest, inner =>
      if source = some level then some inner else sourceOf level rest (inner + 1)

/-- The levels in the region of captured values; nothing when one is not captured. -/
@[expose] def renameAll (rename : Nat → Option Nat) : List Nat → Option (List Nat)
  | [] => some []
  | level :: rest =>
      match rename level, renameAll rename rest with
      | some inner, some others => some (inner :: others)
      | _, _ => none

end Facts

/-- A shape in a nested region: kept when every value it mentions is captured. -/
@[expose] def Shape.rename (rename : Nat → Option Nat) : Shape → Shape
  | .other => .other
  | .add left right =>
      match rename left, rename right with
      | some left, some right => .add left right
      | _, _ => .other
  | .sub left right =>
      match rename left, rename right with
      | some left, some right => .sub left right
      | _, _ => .other
  | .length sequence =>
      match rename sequence with
      | some sequence => .length sequence
      | none => .other
  | .toNat value =>
      match rename value with
      | some value => .toNat value
      | none => .other
  | .less left right =>
      match rename left, rename right with
      | some left, some right => .less left right
      | _, _ => .other
  | .equal left right =>
      match rename left, rename right with
      | some left, some right => .equal left right
      | _, _ => .other
  | .not condition =>
      match rename condition with
      | some condition => .not condition
      | none => .other
  | .and left right =>
      match rename left, rename right with
      | some left, some right => .and left right
      | _, _ => .other
  | .or left right =>
      match rename left, rename right with
      | some left, some right => .or left right
      | _, _ => .other
  | .domain row operands =>
      match Facts.renameAll rename operands with
      | some operands => .domain row operands
      | none => .other
  | .conjunct condition =>
      match rename condition with
      | some condition => .conjunct condition
      | none => .other
  | .disjunct condition =>
      match rename condition with
      | some condition => .disjunct condition
      | none => .other

namespace Facts

/-- The bounds of captured values. -/
@[expose] def renameBounds (rename : Nat → Option Nat) : List Bound → List Bound
  | [] => []
  | bound :: rest =>
      match rename bound.level with
      | some level => ⟨level, bound.lo, bound.hi⟩ :: renameBounds rename rest
      | none => renameBounds rename rest

/-- The orders between captured values. -/
@[expose] def renameOrders (rename : Nat → Option Nat) : List Order → List Order
  | [] => []
  | order :: rest =>
      match rename order.left, rename order.right with
      | some left, some right => ⟨order.strict, left, right⟩ :: renameOrders rename rest
      | _, _ => renameOrders rename rest

/-- The captured conditions known to be true. -/
@[expose] def renameKnown (rename : Nat → Option Nat) : List Nat → List Nat
  | [] => []
  | condition :: rest =>
      match rename condition with
      | some condition => condition :: renameKnown rename rest
      | none => renameKnown rename rest

/-- The facts of a nested region at its start: an input that captures a value has the
shape of that value, and a bound, an order or a known condition is kept when every value
it mentions is captured. -/
@[expose] def enter (facts : Facts) (sources : List (Option Nat)) : Facts :=
  let rename := fun level => sourceOf level sources 0
  { shapes := sources.map fun
      | some level => (facts.shape level).rename rename
      | none => .other
    bounds := renameBounds rename facts.bounds
    orders := renameOrders rename facts.orders
    known := renameKnown rename facts.known
    dead := facts.dead }

/-! ### A region that captures every value in scope

In the normal form a nested region captures every value in scope, the most recent first, after
inputs of its own. For such a region the level of a captured value in the region is a shift of
its level outside, and the shapes of its inputs are the shapes outside. Compiled code uses the
shift in place of the search through the inputs, and one pass over the shapes in place of a
lookup per input (`enter_eq_enterFast`). The check and its theorems are stated with `enter`. -/

/-- The number of leading inputs that capture nothing. -/
def leading : List (Option Nat) → Nat
  | none :: rest => leading rest + 1
  | _ => 0

/-- Whether inputs capture the levels below a count, the highest first. -/
def descending : List (Option Nat) → Nat → Bool
  | [], 0 => true
  | some level :: rest, count + 1 => Nat.beq level count && descending rest count
  | _, _ => false

theorem sourceOf_leading (level : Nat) : ∀ (sources : List (Option Nat)) (inner : Nat),
    sourceOf level sources inner =
      sourceOf level (sources.drop (leading sources)) (inner + leading sources)
  | [], _ => rfl
  | some _ :: _, _ => rfl
  | none :: rest, inner => by
      show (if (none : Option Nat) = some level then some inner else sourceOf level rest (inner + 1)) =
        sourceOf level (rest.drop (leading rest)) (inner + (leading rest + 1))
      have differs : (none : Option Nat) ≠ some level := nofun
      simp only [differs, ↓reduceIte]
      rw [sourceOf_leading level rest (inner + 1), Nat.add_assoc, Nat.add_comm 1]

theorem sourceOf_descending (level : Nat) : ∀ (sources : List (Option Nat)) (count inner : Nat),
    descending sources count = true →
      sourceOf level sources inner =
        if level < count then some (inner + (count - 1 - level)) else none
  | [], 0, _, _ => rfl
  | [], _ + 1, _, shaped => nomatch shaped
  | none :: _, 0, _, shaped => nomatch shaped
  | none :: _, _ + 1, _, shaped => nomatch shaped
  | some _ :: _, 0, _, shaped => nomatch shaped
  | some first :: rest, count + 1, inner, shaped => by
      have both := Bool.and_eq_true_iff.mp shaped
      have first_ : first = count := Nat.eq_of_beq_eq_true both.1
      have later := sourceOf_descending level rest count (inner + 1) both.2
      show (if some first = some level then some inner else sourceOf level rest (inner + 1)) = _
      rw [later, first_]
      by_cases same : count = level
      · subst same
        simp
      · have differs : (some count : Option Nat) ≠ some level :=
          fun equal => same (Option.some.inj equal)
        simp only [differs, ↓reduceIte]
        by_cases below : level < count
        · have wider : level < count + 1 := Nat.lt_succ_of_lt below
          simp only [below, wider, ↓reduceIte]
          congr 1
          omega
        · have narrower : ¬ level < count + 1 := by omega
          simp only [below, narrower, ↓reduceIte]

/-- The shapes at the levels below a count, the highest first. -/
def shapesFrom (shapes : List Shape) : Nat → List Shape
  | 0 => []
  | count + 1 => shapes.getD count .other :: shapesFrom shapes count

/-- The same, in one pass over the shapes. -/
def shapesBelow : List Shape → Nat → List Shape → List Shape
  | _, 0, found => found
  | shape :: rest, count + 1, found => shapesBelow rest count (shape :: found)
  | [], count + 1, found => shapesBelow [] count (.other :: found)

theorem shapesFrom_nil_other (found : List Shape) : ∀ (count : Nat),
    shapesFrom [] count ++ Shape.other :: found = Shape.other :: (shapesFrom [] count ++ found)
  | 0 => rfl
  | count + 1 => by
      show Shape.other :: (shapesFrom [] count ++ Shape.other :: found) = _
      rw [shapesFrom_nil_other found count]
      rfl

theorem shapesFrom_nil : ∀ (count : Nat) (found : List Shape),
    shapesBelow [] count found = shapesFrom [] count ++ found
  | 0, _ => rfl
  | count + 1, found => by
      show shapesBelow [] count (.other :: found) = _
      rw [shapesFrom_nil count (.other :: found)]
      exact shapesFrom_nil_other found count

theorem shapesFrom_cons (shape : Shape) (rest : List Shape) : ∀ (count : Nat),
    shapesFrom (shape :: rest) (count + 1) = shapesFrom rest count ++ [shape]
  | 0 => rfl
  | count + 1 => by
      show (shape :: rest).getD (count + 1) .other :: shapesFrom (shape :: rest) (count + 1) = _
      rw [shapesFrom_cons shape rest count]
      rfl

theorem shapesBelow_eq : ∀ (shapes : List Shape) (count : Nat) (found : List Shape),
    shapesBelow shapes count found = shapesFrom shapes count ++ found
  | _, 0, _ => by
      cases ‹List Shape› <;> rfl
  | [], count + 1, found => shapesFrom_nil (count + 1) found
  | shape :: rest, count + 1, found => by
      show shapesBelow rest count (shape :: found) = _
      rw [shapesBelow_eq rest count (shape :: found), shapesFrom_cons shape rest count,
        List.append_assoc]
      rfl

/-- The shapes of the inputs that capture nothing. -/
theorem map_leading (shapeOf : Option Nat → Shape) (nothing : shapeOf none = .other) :
    ∀ (sources : List (Option Nat)),
      sources.map shapeOf =
        List.replicate (leading sources) .other ++ (sources.drop (leading sources)).map shapeOf
  | [] => rfl
  | some _ :: _ => rfl
  | none :: rest => by
      show shapeOf none :: rest.map shapeOf = _
      rw [nothing, map_leading shapeOf nothing rest]
      rfl

/-- The shapes of inputs that capture the levels below a count, the highest first. -/
theorem map_descending (shapes : List Shape) (change : Shape → Shape) :
    ∀ (sources : List (Option Nat)) (count : Nat), descending sources count = true →
      sources.map (fun
        | some level => change (shapes.getD level .other)
        | none => .other) = (shapesFrom shapes count).map change
  | [], 0, _ => rfl
  | [], _ + 1, shaped => nomatch shaped
  | none :: _, 0, shaped => nomatch shaped
  | none :: _, _ + 1, shaped => nomatch shaped
  | some _ :: _, 0, shaped => nomatch shaped
  | some first :: rest, count + 1, shaped => by
      have both := Bool.and_eq_true_iff.mp shaped
      have first_ : first = count := Nat.eq_of_beq_eq_true both.1
      show change (shapes.getD first .other) :: rest.map _ = _
      rw [map_descending shapes change rest count both.2, first_]
      rfl

/-- The facts of a nested region at its start, with a shift for a region that captures every
value in scope: the level in the region of the value at a level outside is a shift, and the
shapes of the inputs are the shapes outside, in one pass. -/
def enterFast (facts : Facts) (sources : List (Option Nat)) : Facts :=
  let own := leading sources
  let count := sources.length - own
  if descending (sources.drop own) count then
    let rename := fun level => if level < count then some (own + (count - 1 - level)) else none
    { shapes := List.replicate own .other ++
        (shapesBelow facts.shapes count []).map (Shape.rename rename)
      bounds := renameBounds rename facts.bounds
      orders := renameOrders rename facts.orders
      known := renameKnown rename facts.known
      dead := facts.dead }
  else enter facts sources

@[csimp] theorem enter_eq_enterFast : @enter = @enterFast := by
  funext facts sources
  unfold enterFast
  dsimp only
  split
  · rename_i shaped
    have renames : (fun level => sourceOf level sources 0) = fun level =>
        if level < sources.length - leading sources then
          some (leading sources + (sources.length - leading sources - 1 - level))
        else none := by
      funext level
      rw [sourceOf_leading level sources 0, sourceOf_descending level _ _ _ shaped, Nat.zero_add]
    unfold enter
    dsimp only
    have shapeAt : ∀ level, facts.shape level = facts.shapes.getD level .other := fun _ => rfl
    simp only [shapeAt]
    rw [renames, shapesBelow_eq, List.append_nil,
      map_leading (fun
        | some level => (facts.shapes.getD level .other).rename _
        | none => .other) rfl sources,
      map_descending facts.shapes (Shape.rename _) _ _ shaped]
  · rfl

end Facts

/-! ## Intervals of results -/

/-- The sum of two upper ends. -/
@[expose] def plus : Option Nat → Option Nat → Option Nat
  | some first, some second => some (first + second)
  | _, _ => none

/-- The product of two upper ends. -/
@[expose] def times : Option Nat → Option Nat → Option Nat
  | some first, some second => some (first * second)
  | _, _ => none

namespace Builtin

/-- The shape of the result of an operation the core owns, on the levels of its operands. -/
@[expose] def shape : Builtin → List Nat → Shape
  | .natAdd, [left, right] => .add left right
  | .natSub, [left, right] => .sub left right
  | .natLess, [left, right] => .less left right
  | .natEqual, [left, right] => .equal left right
  | .boolNot, [condition] => .not condition
  | .boolAnd, [left, right] => .and left right
  | .boolOr, [left, right] => .or left right
  | .seqLength _ _, [sequence] => .length sequence
  | .finToNat _, [value] => .toNat value
  | _, _ => .other

/-- The interval of the natural result of an operation the core owns.

A power is not monotone in its exponent at the base 0: `0 ^ 0` is 1. Its lower end is
`lo(a) ^ lo(b)` when `lo(a)` is at least 1, and otherwise 1 when the exponent is 0 and 0
when it may be more; its upper end is `hi(a) ^ hi(b)`, and at least 1 when the exponent
may be 0. -/
@[expose] def interval (facts : Facts) : Builtin → List Nat → Option Interval
  | .natAdd, [left, right] =>
      some ⟨facts.lo left + facts.lo right, plus (facts.hi left) (facts.hi right)⟩
  | .natMul, [left, right] =>
      some ⟨facts.lo left * facts.lo right, times (facts.hi left) (facts.hi right)⟩
  | .natPow, [base, exponent] =>
      some ⟨cond (decide (1 ≤ facts.lo base)) (facts.lo base ^ facts.lo exponent)
          (cond (within (facts.hi exponent) 0) 1 0),
        match facts.hi base, facts.hi exponent with
        | some top, some power =>
            some (cond (decide (facts.lo exponent = 0)) (max (top ^ power) 1) (top ^ power))
        | _, _ => none⟩
  | .natSub, [left, right] =>
      some ⟨match facts.hi right with
          | some hi => facts.lo left - hi
          | none => 0,
        match facts.hi left with
        | some hi => some (hi - facts.lo right)
        | none => none⟩
  | .natDiv, [left, right] =>
      some ⟨match facts.hi right with
          | some hi => facts.lo left / hi
          | none => 0,
        match facts.hi left with
        | some hi => cond (decide (1 ≤ facts.lo right)) (some (hi / facts.lo right)) none
        | none => none⟩
  | .natRem, [left, right] => some ⟨0, atMost (facts.hi left) (Facts.before (facts.hi right))⟩
  | .seqLength _ (some size), [_] => some ⟨size, some size⟩
  | .seqLength _ none, [_] => some ⟨0, none⟩
  | .finToNat bound, [_] => some ⟨0, some (bound - 1)⟩
  | _, _ => none

/-- An application of an operation the core owns is justified by what is known.

- `nat.sub a b`: `b <= a` is known.
- `nat.div a b`, `nat.rem a b`: the interval of `b` starts at 1 or above.
- `seq.at xs i`: on a sequence of `n` elements, the interval of `i` ends below `n`; on an
  unsized one, `i < l` is known for an `l` that is the length of `xs`.
- `seq.slice xs a b`: `a <= b` is known; the interval of `b` ends at `n` or below, or
  `b <= l` is known for an `l` that is the length of `xs`; and when the result has `k`
  elements, `a` and `b` are points whose difference is `k`, or `b` is `a + c` or `c + a`
  with `c` the point `k`.
- `seq.sized xs` to `n`: an `l` that is the length of `xs` is the point `n`.
- `nat.below a` to a bound: the interval of `a` ends below the bound.

An operation without a domain needs nothing. -/
@[expose] def justified (facts : Facts) : Builtin → List Nat → Bool
  | .natSub, [left, right] => facts.knownLe right left
  | .natDiv, [_, right] | .natRem, [_, right] => decide (1 ≤ facts.lo right)
  | .seqAt _ (some size), [_, position] => below (facts.hi position) size
  | .seqAt _ none, [sequence, position] =>
      (facts.lengths sequence).any fun length => facts.knownLt position length
  | .seqSlice _ size result, [sequence, first, last] =>
      facts.knownLe first last &&
        (match size with
          | some size => within (facts.hi last) size
          | none => (facts.lengths sequence).any fun length => facts.knownLe last length) &&
        (match result with
          | none => true
          | some count =>
              (match facts.hi first, facts.hi last with
                | some start, some stop =>
                    facts.point first start && facts.point last stop &&
                      decide (stop - start = count)
                | _, _ => false) ||
              (match facts.shape last with
                | .add left right =>
                    (decide (left = first) && facts.point right count) ||
                      (decide (right = first) && facts.point left count)
                | _ => false))
  | .seqSized _ size, [sequence] =>
      (facts.lengths sequence).any fun length => facts.point length size
  | .natBelow bound, [value] => below (facts.hi value) bound
  | operation, _ => !operation.restricted

end Builtin

/-- The requirement that an application does not meet. -/
inductive Requirement where
  /-- A `stop` names the reserved reason `undefined`. -/
  | reservedStop
  /-- `nat.sub a b` without `b <= a` known. -/
  | ordered
  /-- `nat.div` or `nat.rem` by a value not known to be at least 1. -/
  | positive
  /-- `seq.at` at a position not known to be below the length. -/
  | position
  /-- `seq.slice` with bounds not known to be ordered and within the length, or into a
  size that the bounds are not known to have. -/
  | slice
  /-- `seq.sized` of a sequence whose length is not known to be the size. -/
  | size
  /-- `nat.below` of a value not known to be below the bound. -/
  | bound
  /-- A restricted row whose domain row is not known to be true on the same operands. -/
  | domain
  /-- A restricted row that names no domain row. -/
  | noDomain
  /-- A loop over a value whose count is not known to be within its maximum. -/
  | maximum
  deriving Repr, Inhabited, DecidableEq

/-- The requirement of an operation the core owns that has a domain. -/
@[expose] def Builtin.requirement : Builtin → Requirement
  | .natSub => .ordered
  | .natDiv | .natRem => .positive
  | .seqAt .. => .position
  | .seqSlice .. => .slice
  | .seqSized .. => .size
  | _ => .bound

/-- An application that is not justified: the requirement, and where. The path is the
number of the instruction in the body, then, for an instruction inside a nested region,
the number of that region among the regions of its instruction and the number of the
instruction in it, and so on. The body of a block is numbered like a region without a
region number. -/
structure Unjustified where
  path : List Nat
  requirement : Requirement
  deriving Repr, Inhabited, DecidableEq

/-! ## Results -/

/-- The wider of two intervals. -/
@[expose] def Interval.join (first second : Interval) : Interval :=
  ⟨min first.lo second.lo,
    match first.hi, second.hi with
    | some first, some second => some (max first second)
    | _, _ => none⟩

/-- The intervals of the results of one of two regions. -/
@[expose] def joinIntervals : List Interval → List Interval → List Interval
  | first :: firsts, second :: seconds => first.join second :: joinIntervals firsts seconds
  | _, _ => []

/-- What one of two regions returns: a region that does not return adds nothing. Of a
value that either region may return the interval is known, and no sum. -/
@[expose] def Outcome.join : Outcome → Outcome → Outcome
  | none, second => second
  | first, none => first
  | some first, some second =>
      some ((joinIntervals (first.map (·.interval)) (second.map (·.interval))).map
        fun interval => ⟨interval, []⟩)

/-- What one of several regions returns. -/
@[expose] def Outcome.joinAll : List Outcome → Outcome
  | [] => none
  | outcome :: rest => outcome.join (joinAll rest)

/-- The bounds of new values of the given types from the level `level` on: a natural
has its interval. -/
@[expose] def boundsOf : (level : Nat) → List Ty → List Interval → List Bound
  | _, [], _ => []
  | _, _ :: _, [] => []
  | level, type :: types, interval :: rest =>
      match type with
      | .nat => ⟨level, interval.lo, interval.hi⟩ :: boundsOf (level + 1) types rest
      | _ => boundsOf (level + 1) types rest

/-- The bound of a new value at a level, when it has an interval. -/
@[expose] def boundOf (level : Nat) : Option Interval → List Bound
  | some interval => [⟨level, interval.lo, interval.hi⟩]
  | none => []

/-- The intervals that a region returns, none when it does not return. -/
@[expose] def Outcome.intervals : Outcome → List Interval
  | some returned => returned.map (·.interval)
  | none => []

/-- What is known of the values that a region returns, nothing when it does not return. -/
@[expose] def Outcome.returned : Outcome → List Returned
  | some returned => returned
  | none => []

/-- The interval of the other addend of a returned sum one of whose addends is the value
at `source`. -/
@[expose] def findStep (source : Nat) : List (Nat × Interval) → Option Interval
  | [] => none
  | step :: rest => if step.1 = source then some step.2 else findStep source rest

/-- `first + count * step` on upper ends. -/
@[expose] def plusTimes : Option Nat → Option Nat → Option Nat → Option Nat
  | some first, some count, some step => some (first + count * step)
  | _, _, _ => none

/-- The bounds of the carried results of a loop that are sums. A carried `nat` whose
region returns its carried input plus a term in `l..h`, in either order, is after
`count` iterations in `lo(init) + lo(count) * l .. hi(init) + hi(count) * h`: `init` is
the operand carried in, and nothing is known of the carried input inside the region, so
the term has its interval in every iteration. `level` is the level of the result,
`position` its position among the carried values, and the list of what the region returns
starts at its first carried value. -/
@[expose] def sumBounds (facts : Facts) (count : Interval) :
    (level position : Nat) → List Ty → List Nat → List Returned → List Bound
  | _, _, [], _, _ => []
  | _, _, _ :: _, [], _ => []
  | _, _, _ :: _, _ :: _, [] => []
  | level, position, type :: types, init :: inits, returned :: rest =>
      match type, findStep (position + 1) returned.steps with
      | .nat, some step =>
          ⟨level, facts.lo init + count.lo * step.lo,
            plusTimes (facts.hi init) count.hi step.hi⟩ ::
              sumBounds facts count (level + 1) (position + 1) types inits rest
      | _, _ => sumBounds facts count (level + 1) (position + 1) types inits rest

section Local

variable {operations : List OperationSignature} {functions : List FunctionHeader}
  {deployed : Bool}

/-- The `bool` literal that an instruction and the rest of its region return, when the
instruction is the literal and the rest returns its value and nothing else. -/
@[expose] def literalReturn {Γ : List Ty} :
    (op : LocalOp operations functions deployed) → {out : List Ty} →
      Region (LocalDialect operations functions deployed) (bindAll Γ op.results) out → Option Bool
  | .literal (.bool value), _, .ret (.cons reference .nil) =>
      cond (decide (reference.index = 0)) (some value) none
  | _, _, _ => none

/-- The `bool` literal that a region returns, when the region is one `literal`
instruction of a `bool` and the return of that one value. -/
@[expose] def literalBool {Γ out : List Ty} :
    Region (LocalDialect operations functions deployed) Γ out → Option Bool
  | .letOp op _ _ next => literalReturn op next
  | _ => none

end Local

/-- The shape of the result of an `if` on the value at `condition`, from the `bool` literal
that each of its two regions returns, when it returns one. An `if` on `a` whose second
region returns the literal `false` is `a and b`, with `b` computed under `a`: its result is
true only when `a` is. An `if` on `a` whose first region returns the literal `true` is
`a or b`: its result is false only when `a` is. -/
@[expose] def branchShapeOf (condition : Nat) (onTrue onFalse : Option Bool) : Option Shape :=
  if onFalse = some false then some (.conjunct condition)
  else if onTrue = some true then some (.disjunct condition)
  else none

section Local

variable {operations : List OperationSignature} {functions : List FunctionHeader}
  {deployed : Bool}

namespace LocalOp

/-- The shape of the result of an `if` that is a conjunction or a disjunction: the shape
that the literals of its two regions give it (`branchShapeOf`). -/
@[expose] def branchShape :
    (op : LocalOp operations functions deployed) → List Nat →
      Regions (LocalDialect operations functions deployed) op.regions → Option Shape
  | .conditional .., condition :: _, .cons onTrue (.cons onFalse .nil) =>
      branchShapeOf condition (literalBool onTrue) (literalBool onFalse)
  | _, _, _ => none

/-- The requirement that an application does not meet, on the levels of its operands; none
when it is justified. A restricted row is justified by a condition known to be true whose
shape is the row's domain row applied to the same operands. A loop over a value with a
maximum is justified when the count is known to be within the maximum. -/
@[expose] def unjustified (facts : Facts) :
    LocalOp operations functions deployed → List Nat → Option Requirement
  | .op (kind := kind) _ _, levels =>
      match kind with
      | .restricted none => some .noDomain
      | .restricted (some domain) =>
          cond (facts.known.any fun condition =>
              decide (facts.shape condition = .domain domain levels))
            none (some .domain)
      | _ => none
  | .builtin operation, levels =>
      cond (operation.justified facts levels) none (some operation.requirement)
  | .loop (.runtime (some maximum)) _ _ _, count :: _ =>
      cond (within (facts.hi count) maximum) none (some .maximum)
  | _, _ => none

/-- The shapes of the results. -/
@[expose] def resultShapes : LocalOp operations functions deployed → List Nat → List Shape
  | .op (outputs := outputs) (kind := kind) row _, levels =>
      match kind with
      | .pure =>
          cond (decide (outputs = [.bool])) [.domain row.index levels]
            (outputs.map fun _ => .other)
      | _ => outputs.map fun _ => .other
  | .builtin operation, levels => [operation.shape levels]
  | instruction, _ => instruction.results.map fun _ => Shape.other

/-- The bounds of the results: of a literal, of an operation the core owns, of an `if`
or a `match`, whose results have the smaller `lo` and the larger `hi` of the regions that
return, and of the carried results of a loop that are sums. -/
@[expose] def resultBounds (facts : Facts) :
    LocalOp operations functions deployed → List Nat → List Outcome → List Bound
  | .literal (.nat value), _, _ => [⟨facts.depth, value, some value⟩]
  | .builtin operation, levels, _ => boundOf facts.depth (operation.interval facts levels)
  | .conditional _ outputs, _, outcomes =>
      boundsOf facts.depth outputs (Outcome.joinAll outcomes).intervals
  | .match _ _ _ outputs, _, outcomes =>
      boundsOf facts.depth outputs (Outcome.joinAll outcomes).intervals
  | .loop (.static count) carried collected _, levels, outcomes =>
      sumBounds facts ⟨count, some count⟩ (facts.depth + collected.length) 0 carried levels
        ((Outcome.joinAll outcomes).returned.drop collected.length)
  | .loop (.runtime _) carried collected _, count :: rest, outcomes =>
      sumBounds facts (facts.interval count) (facts.depth + collected.length) 0 carried rest
        ((Outcome.joinAll outcomes).returned.drop collected.length)
  | _, _, _ => []

/-- What an operation gives the nested region with the number `number`, from the facts at
the operation.

- `if`: the facts of the condition, taken true in the first region and false in the
  second, then the captures.
- `match`: the captures; nothing is known of the payload.
- `loop`: the captures; the iteration number is below the count, and nothing is known of
  the carried values. A count of the operation gives the interval `0 .. n - 1`; a count
  that is a value gives `0 .. hi(count) - 1` and, when the region captures the count, the
  order of the iteration number below it. The region of a loop over the count 0 of the
  operation never runs. -/
@[expose] def regionEntry (facts : Facts) :
    LocalOp operations functions deployed → List Nat → Nat → Facts
  | .conditional .., condition :: captures, number =>
      (facts.assume facts.depth condition (decide (number = 0))).enter (captures.map some)
  | .match .., _ :: captures, _ => facts.enter (none :: captures.map some)
  | .loop (.static count) carried _ _, levels, _ =>
      cond (decide (count = 0))
        ((facts.enter (List.replicate (carried.length + 1) none ++
          (levels.drop carried.length).map some)).bound 0 0 (some (count - 1))).kill
        ((facts.enter (List.replicate (carried.length + 1) none ++
          (levels.drop carried.length).map some)).bound 0 0 (some (count - 1)))
  | .loop (.runtime _) carried _ _, count :: rest, _ =>
      let sources := List.replicate (carried.length + 1) none ++
        (rest.drop carried.length).map some
      ((facts.enter sources).bound 0 0 (Facts.before (facts.hi count))).orderWhen
        (Facts.sourceOf count sources 0)
  | _, _, _ => facts

/-- The types of the inputs of the nested region with the number `number`; none when the
operation has no such region. -/
@[expose] def regionInputs (op : LocalOp operations functions deployed) (number : Nat) : List Ty :=
  match op.regions[number]? with
  | some signature => signature.1
  | none => []

/-- The facts at the start of the nested region with the number `number`: what the
operation gives the region (`regionEntry`), with the inputs of the region in scope. A
region one of whose inputs has a type without a value, the region of a `match` on an
alternative without a value for one, never runs. -/
@[expose] def regionFacts (facts : Facts) (op : LocalOp operations functions deployed)
    (levels : List Nat) (number : Nat) : Facts :=
  (op.regionEntry facts levels number).inScope (op.regionInputs number)

/-- What an instruction gives of its results: a `guard` gives the facts of its condition;
every other instruction binds its results. -/
@[expose] def resultFacts (facts : Facts) (instruction : LocalOp operations functions deployed)
    (levels : List Nat) (outcomes : List Outcome) : Facts :=
  match instruction, levels with
  | .guard _, [condition] => facts.assume facts.depth condition true
  | instruction, levels =>
      facts.after (instruction.resultShapes levels)
        (instruction.resultBounds facts levels outcomes)

/-- The facts after an instruction: what the instruction gives of its results
(`resultFacts`), with the results in scope. After an instruction one of whose results has a
type without a value, the region never runs. -/
@[expose] def factsAfter (facts : Facts) (instruction : LocalOp operations functions deployed)
    (levels : List Nat) (outcomes : List Outcome) : Facts :=
  (instruction.resultFacts facts levels outcomes).inScope instruction.results

end LocalOp

mutual
  /-- The check of a region from the facts at its start: the first application that is not
  justified, or what the region returns. `path` and `index` say where the region's next
  instruction is. -/
  @[expose] def justifyRegion (path : List Nat) (index : Nat) (facts : Facts) {Γ out : List Ty} :
      Region (LocalDialect operations functions deployed) Γ out → Except Unjustified Outcome
    | .ret values => .ok (some ((Scope.numbers facts.depth values).map facts.returned))
    | .stop reason =>
        if reason = .undefined then .error ⟨path ++ [index], .reservedStop⟩ else .ok none
    | .letOp op arguments bodies next =>
        match cond facts.dead none
            (LocalOp.unjustified facts op (Scope.numbers facts.depth arguments)) with
        | some requirement => .error ⟨path ++ [index], requirement⟩
        | none =>
            match justifyRegions (path ++ [index])
                (LocalOp.regionFacts facts op (Scope.numbers facts.depth arguments)) 0 bodies with
            | .error unjustified => .error unjustified
            | .ok outcomes =>
                justifyRegion path (index + 1)
                  ((LocalOp.factsAfter facts op (Scope.numbers facts.depth arguments)
                    outcomes).reshape facts.depth
                      (LocalOp.branchShape op (Scope.numbers facts.depth arguments) bodies)) next
    | .bind (mid := mid) body next =>
        match justifyRegion (path ++ [index]) 0 facts body with
        | .error unjustified => .error unjustified
        | .ok outcome =>
            justifyRegion path (index + 1)
              ((facts.after (mid.map fun _ => Shape.other)
                (boundsOf facts.depth mid outcome.intervals)).inScope mid) next

  /-- The check of the nested regions of an instruction, each from its own facts. -/
  @[expose] def justifyRegions (path : List Nat) (factsOf : Nat → Facts) (number : Nat)
      {signatures : List (List Ty × List Ty)} :
      Regions (LocalDialect operations functions deployed) signatures →
        Except Unjustified (List Outcome)
    | .nil => .ok []
    | .cons body tail =>
        match justifyRegion (path ++ [number]) 0 (factsOf number) body with
        | .error unjustified => .error unjustified
        | .ok outcome =>
            match justifyRegions path factsOf (number + 1) tail with
            | .error unjustified => .error unjustified
            | .ok outcomes => .ok (outcome :: outcomes)
end

end Local

/-! ## Definitions and programs -/

/-- The first application of a function's body that is not justified; none when the
function passes the check of facts. Nothing is known of the inputs but that they are in
scope. -/
@[expose] def FunctionDefinition.unjustified {operations : List OperationSignature}
    {functions : List FunctionHeader} {header : FunctionHeader}
    (definition : FunctionDefinition operations functions header) : Option Unjustified :=
  match justifyRegion [] 0 ((Facts.start header.inputs.length).inScope header.inputs)
      definition.body with
  | .error unjustified => some unjustified
  | .ok _ => none

/-- A function passes the check of facts. -/
@[expose] def FunctionDefinition.justified {operations : List OperationSignature}
    {functions : List FunctionHeader} {header : FunctionHeader}
    (definition : FunctionDefinition operations functions header) : Bool :=
  definition.unjustified.isNone

/-- Every function passes the check of facts. A function known by its header only has no
body to check: its meaning is the model's, which stops with an authored reason. -/
@[expose] def Functions.justified {typeTable : TypeTable} {operations : List OperationSignature} :
    {functions : List FunctionHeader} → Functions typeTable operations functions → Bool
  | _, .nil => true
  | _, .snoc earlier definition _ => earlier.justified && definition.justified
  | _, .opaque earlier _ _ => earlier.justified

/-- The functions that do not pass, by their numbers in program order, each with its first
application that is not justified. -/
@[expose] def Functions.unjustified {typeTable : TypeTable} {operations : List OperationSignature} :
    {functions : List FunctionHeader} → Functions typeTable operations functions →
      List (Nat × Unjustified)
  | _, .nil => []
  | _, .snoc (functions := functions) earlier definition _ =>
      earlier.unjustified ++
        match definition.unjustified with
        | some unjustified => [(functions.length, unjustified)]
        | none => []
  | _, .opaque earlier _ _ => earlier.unjustified

end Zkc.Core
