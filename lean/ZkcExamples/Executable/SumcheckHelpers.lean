module

public import ZkcExamples.Executable.SumcheckProofProgramData
public import ZkcExamples.Construction.SumcheckArtifact
public import ZkcExamples.Structured.SumcheckSourceContracts
public import Zkc.Protocols.Sumcheck.Source.PendingLaws
public import Zkc.Executable.HelperSoundness
public import Zkc.Executable.Installed

@[expose] public section

/-! Preparation of the current executable Sumcheck helpers.

The native validator calls the Pending constructor, openClaim, append, atPrefix,
and the terminal multilinear check. The finite helper rule prepares the first
four against their complete admitted source bodies. The terminal check iterates
outside that rule's recipe table; its separate proof evaluates the actual native
fold, including its map binding, and preserves resource stops. Its exact charge
on a shaped table is `62 + 20 * point.length`.
-/

set_option autoImplicit false

namespace ZkcExamples.Executable.SumcheckHelpers
open Zkc.Construction Zkc.Executable Zkc.Source
open Zkc.Source.Structured
open ZkcExamples.Structured ZkcExamples.Structured.SumcheckHelperBodies
open Zkc.Polynomial.Multilinear
open SumcheckPendingBodies

abbrev validator : Validator := SumcheckProofProgramData.validator
abbrev program := ZkcExamples.Construction.SumcheckProof.program

/-- The current Pending constructor and its consuming wrappers. -/
abbrev pendingFunction : Zkc.Executable.Function := SumcheckProofProgramData.function0
abbrev openClaimFunction : Zkc.Executable.Function := SumcheckProofProgramData.function1
abbrev appendFunction : Zkc.Executable.Function := SumcheckProofProgramData.function2
abbrev atPrefixFunction : Zkc.Executable.Function := SumcheckProofProgramData.function3
abbrev checkFunction : Zkc.Executable.Function := SumcheckProofProgramData.function4

theorem pendingFunction_eq : validator.function? pendingHelper.name = some pendingFunction := rfl
theorem openClaimFunction_eq : validator.function? openClaimHelper.name = some openClaimFunction := rfl
theorem appendFunction_eq : validator.function? appendHelper.name = some appendFunction := rfl
theorem atPrefixFunction_eq : validator.function? atPrefixHelper.name = some atPrefixFunction := rfl
theorem checkFunction_eq : validator.function? checkHelper.name = some checkFunction := rfl


variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- The closed table of the admitted program's helpers is the source unit's. -/
theorem table_eq : helperTable program F G = SumcheckSourceContracts.helperMeanings (F := F) (G := G) := rfl

theorem present {helper : Helper} {body : Region dialect helper.inputs helper.outputs}
    (association : BodyIn SumcheckSourceViews.unit.definitions helper body) :
    helper ∈ program.payload.definitions.map CheckedDefinition.helper := by
  obtain ⟨definition, member, signature, -⟩ := association
  exact List.mem_map.mpr ⟨definition, member, signature⟩

/-- A call by name of one of the source's helpers invokes it in the source
unit's closed table. -/
theorem call_eq {helper : Helper} {body : Region dialect helper.inputs helper.outputs}
    (association : BodyIn SumcheckSourceViews.unit.definitions helper body)
    (arguments : List (Value F G)) (values : Values (assignment F G) helper.inputs)
    (decoded : decodeValues helper.inputs arguments = some values) :
    callHelper (helperTable program F G) helper.name arguments =
      match Zkc.Construction.closedOutcome
          (invoke (SumcheckSourceContracts.helperMeanings (F := F) (G := G)) helper values) with
      | .returned results => .returned (encodeValues results)
      | .stopped reason => .stopped reason := by
  obtain ⟨⟨foundHelper, implementation⟩, found, same⟩ :=
    Evaluation.linked_lookup (F := F) (G := G) (interface := closedInterface)
      .closed program.payload.linked helper (present association)
  change (helperTable program F G).find? (fun entry => entry.helper.name == helper.name) =
    some ⟨foundHelper, implementation⟩ at found
  simp only at same
  subst same
  rw [← table_eq]
  have invoked : invoke (helperTable program F G) foundHelper values = implementation values := by
    simp [invoke, found]
  rw [invoked]
  simp only [callHelper, found, decoded]
  generalize Zkc.Construction.closedOutcome (implementation values) = outcome
  cases outcome <;> rfl

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- An encoded value has the sort of its type. -/
theorem hasSort_encode (ty : Structured.Ty) (value : Structured.assignment F G ty) :
    HasSort (Value.encode ty value) (.data ty) := by
  simp only [HasSort]
  exact ⟨value, rfl⟩

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- One returned value at its sort. -/
theorem sorted_single {value : Value F G} {sort : ValueSort} (sorted : HasSort value sort) :
    ∀ (index : Nat) (found : Value F G) (expected : ValueSort), [value][index]? = some found →
      [sort][index]? = some expected → HasSort found expected
  | 0, found, expected, isFound, isExpected => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at isFound isExpected
      subst isFound isExpected
      exact sorted
  | _ + 1, _, _, isFound, _ => by simp at isFound

/-- The helper rule accepts Pending, both consuming wrappers, and point extension. -/
theorem rule_accepted :
    checkHelpers installed validator program [pendingHelper.name, openClaimHelper.name, appendHelper.name, atPrefixHelper.name] = .ok () := by
  decide +kernel

/-- The terminal check is outside the rule's recipe table: its body iterates. -/
theorem check_outside :
    checkHelper installed validator program.payload.definitions checkHelper.name = .error (.recipe "loop") := by
  decide +kernel

/-- The Pending constructor consumes the scalar and creates an empty prefix. -/
theorem pending_prepared : Prepared installed validator (helperTable program F G) pendingHelper.name :=
  checkHelpers_sound installed validator program rule_accepted _ (by simp)

/-- The point extension helper's body appends the challenge to the point. -/
theorem append_prepared : Prepared installed validator (helperTable program F G) appendHelper.name :=
  checkHelpers_sound installed validator program rule_accepted _ (by simp)

theorem openClaim_prepared : Prepared installed validator (helperTable program F G) openClaimHelper.name :=
  checkHelpers_sound installed validator program rule_accepted _ (by simp)

theorem atPrefix_prepared : Prepared installed validator (helperTable program F G) atPrefixHelper.name :=
  checkHelpers_sound installed validator program rule_accepted _ (by simp)

/-! ## Operations the check applies -/

section Operations

theorem indexLimit_pow {k : Nat} (small : k < 64) : 2 ^ k < indexLimit :=
  Nat.pow_lt_pow_right (by decide) small

theorem length_returns {xs : List F} (bound : xs.length < indexLimit) :
    (Resolved.compute (.primitive (.vectorLength "bls12-381.fr"))).evaluate
      [(.vector "bls12-381.fr" xs : Value F G)] = .returned [.index xs.length] := by
  simp [Resolved.evaluate, Computation.apply, decodeValues, Value.decode, Primitive.arguments,
    Primitive.evaluate, bound]
  rfl

theorem length_stops {xs : List F} (bound : ¬ xs.length < indexLimit) :
    (Resolved.compute (.primitive (.vectorLength "bls12-381.fr"))).evaluate
      [(.vector "bls12-381.fr" xs : Value F G)] = .stopped .exhausted := by
  simp [Resolved.evaluate, Computation.apply, decodeValues, Value.decode, Primitive.arguments,
    Primitive.evaluate, bound]

theorem constant_returns (value : Nat) :
    (Resolved.calculate (.indexConstant value)).evaluate ([] : List (Value F G)) =
      .returned [.index value] := rfl

theorem less_true {a b : Nat} (first : a < indexLimit) (second : b < indexLimit) (less : a < b) :
    (Resolved.compute (.primitive .indexLess)).evaluate [(.index a : Value F G), .index b] =
      .returned [.data (.boolean true)] := by
  simp [Resolved.evaluate, Computation.apply, decodeValues, Value.decode, Primitive.arguments,
    Primitive.evaluate, checkedIndices, first, second, less]
  rfl

theorem less_false {a b : Nat} (first : a < indexLimit) (second : b < indexLimit) (notLess : ¬ a < b) :
    (Resolved.compute (.primitive .indexLess)).evaluate [(.index a : Value F G), .index b] =
      .returned [.data (.boolean false)] := by
  simp [Resolved.evaluate, Computation.apply, decodeValues, Value.decode, Primitive.arguments,
    Primitive.evaluate, checkedIndices, first, second, notLess]
  rfl

theorem mod_returns {a b : Nat} (first : a < indexLimit) (second : b < indexLimit) (positive : b ≠ 0) :
    (Resolved.compute (.primitive .indexMod)).evaluate [(.index a : Value F G), .index b] =
      .returned [.index (a % b)] := by
  simp [Resolved.evaluate, Computation.apply, decodeValues, Value.decode, Primitive.arguments,
    Primitive.evaluate, checkedIndices, first, second, positive]
  rfl

theorem div_returns {a b : Nat} (first : a < indexLimit) (second : b < indexLimit) (positive : b ≠ 0) :
    (Resolved.compute (.primitive .indexDiv)).evaluate [(.index a : Value F G), .index b] =
      .returned [.index (a / b)] := by
  simp [Resolved.evaluate, Computation.apply, decodeValues, Value.decode, Primitive.arguments,
    Primitive.evaluate, checkedIndices, first, second, positive]
  rfl

theorem mul_returns {a b : Nat} (first : a < indexLimit) (second : b < indexLimit)
    (product : a * b < indexLimit) :
    (Resolved.compute (.primitive .indexMul)).evaluate [(.index a : Value F G), .index b] =
      .returned [.index (a * b)] := by
  simp [Resolved.evaluate, Computation.apply, decodeValues, Value.decode, Primitive.arguments,
    Primitive.evaluate, checkedIndices, first, second, product]
  rfl

theorem sub_returns {a b : Nat} (first : a < indexLimit) (second : b < indexLimit) (le : b ≤ a) :
    (Resolved.compute (.primitive .indexSub)).evaluate [(.index a : Value F G), .index b] =
      .returned [.index (a - b)] := by
  simp [Resolved.evaluate, Computation.apply, decodeValues, Value.decode, Primitive.arguments,
    Primitive.evaluate, checkedIndices, first, second, le]
  rfl

theorem equal_true {a b : Nat} (same : a = b) :
    (Resolved.calculate .indexEqual).evaluate [(.index a : Value F G), .index b] =
      .returned [.data (.boolean true)] := by
  subst same
  simp [Resolved.evaluate, Zkc.Construction.calculate, decodeValues, Value.decode, Calculation.op,
    Op.arguments, Calculation.evaluate_indexEqual]
  rfl

theorem equal_false {a b : Nat} (different : a ≠ b) :
    (Resolved.calculate .indexEqual).evaluate [(.index a : Value F G), .index b] =
      .returned [.data (.boolean false)] := by
  simp [Resolved.evaluate, Zkc.Construction.calculate, decodeValues, Value.decode, Calculation.op,
    Op.arguments, Calculation.evaluate_indexEqual, different]
  rfl

theorem get_returns {xs : List F} {index : Nat} (bound : index < xs.length) :
    (Resolved.calculate (.boundedAt "bls12-381.fr")).evaluate
      [(.vector "bls12-381.fr" xs : Value F G), .index index] =
      .returned [.data (.field "bls12-381.fr" xs[index])] := by
  simp [Resolved.evaluate, Zkc.Construction.calculate, decodeValues, Value.decode, Calculation.op,
    Op.arguments, Calculation.evaluate_boundedAt, bound]
  rfl

theorem split_returns {xs : List F} (positive : 0 < xs.length) (even : xs.length % 2 = 0) :
    (Resolved.compute (.primitive (.vectorSplit "bls12-381.fr"))).evaluate
      [(.vector "bls12-381.fr" xs : Value F G)] =
      .returned [.vector "bls12-381.fr" (xs.take (xs.length / 2)),
        .vector "bls12-381.fr" (xs.drop (xs.length / 2))] := by
  simp [Resolved.evaluate, Computation.apply, decodeValues, Value.decode, Primitive.arguments,
    Primitive.evaluate, positive, even]
  rfl

theorem require_returns :
    (Resolved.compute .require).evaluate [(.data (.boolean true) : Value F G)] = .returned [] := rfl

theorem subtract_returns {xs ys : List F} (same : xs.length = ys.length) :
    (Resolved.compute (.vectorSubtract "bls12-381.fr")).evaluate
      [(.vector "bls12-381.fr" xs : Value F G), .vector "bls12-381.fr" ys] =
      .returned [.vector "bls12-381.fr" (List.zipWith (· - ·) xs ys)] := by
  simp [Resolved.evaluate, Computation.apply, same]

theorem scale_returns {xs : List F} {scalar : F} :
    (Resolved.compute (.vectorScale "bls12-381.fr")).evaluate
      [(.vector "bls12-381.fr" xs : Value F G), .data (.field "bls12-381.fr" scalar)] =
      .returned [.vector "bls12-381.fr" (xs.map (· * scalar))] := by
  simp [Resolved.evaluate, Computation.apply]

theorem add_returns {xs ys : List F} (same : xs.length = ys.length) :
    (Resolved.compute (.vectorAdd "bls12-381.fr")).evaluate
      [(.vector "bls12-381.fr" xs : Value F G), .vector "bls12-381.fr" ys] =
      .returned [.vector "bls12-381.fr" (List.zipWith (· + ·) xs ys)] := by
  simp [Resolved.evaluate, Computation.apply, same]

/-- The expression the fold's numerical call carries over its low half, high
half and challenge: `in0 + (in1 + (-in0)) * in2`. -/
def interpolation : Zkc.Algebra.RingExpression.Expr Nat Nat :=
  .add (.input 0) (.mul (.add (.input 1) (.neg (.input 0))) (.input 2))

/-- The numerical map over two vectors and a broadcast scalar computes the
interpolation of `interpolate_eq` at every row. -/
theorem map_returns {low high : List F} {r : F} (same : low.length = high.length) :
    (Resolved.compute (.numerical .map "bls12-381.fr" [true, true, false] interpolation)).evaluate
      [(.index low.length : Value F G), .vector "bls12-381.fr" low, .vector "bls12-381.fr" high,
        .data (.field "bls12-381.fr" r)] =
      .returned [.vector "bls12-381.fr" (List.zipWith (fun low high => low + (high - low) * r) low high)] := by
  have slots : Numerical.slots (F := F) (G := G) "bls12-381.fr" low.length [true, true, false]
      [.vector "bls12-381.fr" low, .vector "bls12-381.fr" high, .data (.field "bls12-381.fr" r)] =
      some [.column low, .column high, .scalar r] := by
    simp [Numerical.slots, same]
  simp only [Resolved.evaluate, Computation.apply, slots, PIR.Outcome.returned.injEq, List.cons.injEq,
    Value.vector.injEq, true_and, and_true]
  apply List.ext_getElem
  · simp [same]
  · intro index inRange _
    have inLow : index < low.length := by simpa using inRange
    have inHigh : index < high.length := same ▸ inLow
    simp [Numerical.row, Zkc.Algebra.RingExpression.Expr.map, Zkc.Algebra.RingExpression.Expr.eval,
      Numerical.Slot.read, interpolation, inLow, inHigh, sub_eq_add_neg]

theorem sum_returns {xs : List F} :
    (Resolved.compute (.primitive (.vectorSum "bls12-381.fr"))).evaluate
      [(.vector "bls12-381.fr" xs : Value F G)] =
      .returned [.data (.field "bls12-381.fr" (xs.foldl (· + ·) 0))] := by
  simp [Resolved.evaluate, Computation.apply, decodeValues, Value.decode, Primitive.arguments,
    Primitive.evaluate]
  rfl

theorem fieldEqual_returns {a b : F} :
    (Resolved.calculate (.fieldEqual "bls12-381.fr")).evaluate
      [(.data (.field "bls12-381.fr" a) : Value F G), .data (.field "bls12-381.fr" b)] =
      .returned [.data (.boolean (decide (a = b)))] := by
  simp [Resolved.evaluate, Zkc.Construction.calculate, decodeValues, Value.decode, Calculation.op,
    Op.arguments, Calculation.evaluate_fieldEqual]
  rfl

end Operations

/-! ## The terminal check

The check's body is evaluated one step at a time: each installed operation by
its row's meaning, each region by its taken branch and each loop by induction
on its iterations. -/

section Check

/-- One installed operation of a concrete body that returns: its binding
resolves and its operands are found by evaluation. -/
local macro "returns_operation " evaluates:term : tactic =>
  `(tactic| refine Evaluated.Returns.operation installed validator (by rfl) (by rfl) $evaluates (by rfl) ?_)

/-- One installed operation that returns, on a path that stops later. -/
local macro "continues_operation " evaluates:term : tactic =>
  `(tactic| refine Evaluated.Stops.operation installed validator (by rfl) (by rfl) $evaluates (by rfl) ?_)

/-- One installed operation that stops. -/
local macro "stops_operation " evaluates:term : tactic =>
  `(tactic| exact Evaluated.Stops.operation_stops installed validator (by rfl) (by rfl) $evaluates)

/-- A region whose condition is true and whose branch returns `results`: what
remains is the branch and the rest. -/
local macro "returns_true " results:term : tactic =>
  `(tactic| refine Evaluated.Returns.cond_true installed validator (results := $results) (by rfl) (by rfl) ?_
    (by rfl) ?_)

/-- A region whose condition is false and whose branch returns `results`. -/
local macro "returns_false " results:term : tactic =>
  `(tactic| refine Evaluated.Returns.cond_false installed validator (results := $results) (by rfl) (by rfl) ?_
    (by rfl) ?_)

/-- A region whose condition is true and whose branch returns `results`, on a
path that stops later. -/
local macro "continues_true " results:term : tactic =>
  `(tactic| refine Evaluated.Stops.cond_true installed validator (results := $results) (by rfl) (by rfl) ?_
    (by rfl) ?_)

/-- A region whose condition is true and whose branch stops. -/
local macro "stops_true" : tactic =>
  `(tactic| refine Evaluated.Stops.cond_stops installed validator (by rfl) (by rfl) ?_)

/-- A Boolean constant. -/
local macro "returns_constant" : tactic =>
  `(tactic| refine Evaluated.Returns.constant installed validator ?_)

/-- A yield of found values. -/
local macro "returns_yield" : tactic =>
  `(tactic| exact Evaluated.Returns.yield installed validator (by rfl))

/-- A return of found values. -/
local macro "returns_ret" : tactic =>
  `(tactic| exact Evaluated.Returns.ret installed validator (by rfl))

/-- A loop over found bounds whose iterations return `results`: what remains is
the bounds' limits, the iterations and the rest. -/
local macro "returns_iterate " results:term : tactic =>
  `(tactic| refine Evaluated.Returns.iterate installed validator (results := $results) (by rfl) (by rfl)
    (by rfl) (by rfl) ?_ ?_ (by rfl) ?_)

/-- The actual fold instruction, including its compiler-selected bindings. -/
def restrictionLoop : Zkc.Executable.Step :=
  match checkFunction.body with
  | [_, _, _, _, _, _, _, .cond _ _ _ checked _ _, _] =>
      match checked with
      | [_, _, _, _, _, _, _, _, _, _, loop@(.iterate ..), _, _, _] => loop
      | _ => .yield []
  | _ => .yield []

/-- The body and bindings come from the same actual instruction. -/
def restrictionBody : List Zkc.Executable.Step :=
  match restrictionLoop with
  | .iterate _ _ _ _ _ _ body _ => body
  | _ => []

def restrictionInduction : String :=
  match restrictionLoop with
  | .iterate _ induction _ _ _ _ _ _ => induction
  | _ => ""

def restrictionStateNames : List String :=
  match restrictionLoop with
  | .iterate _ _ _ _ carried _ _ _ => carried.map Prod.fst
  | _ => []

def restrictionCaptureNames : List String :=
  match restrictionLoop with
  | .iterate _ _ _ _ _ captures _ _ => captures
  | _ => []

/-- The parameters of the fold loop's numerical call: its expression. -/
def interpolationParameters : List Parameter :=
  match restrictionBody with
  | [_, _, _, _, _, _, _, _, _, .operation _ _ parameters _ _, _, _, _] => parameters
  | _ => []

/-- The fold's numerical call resolves to the installed map over a low vector,
a high vector and a scalar, with the decoded interpolation. -/
theorem interpolation_resolves :
    validator.binding? "_finite_binding_10" >>= (installed.resolve · interpolationParameters) =
      some (.compute (.numerical .map "bls12-381.fr" [true, true, false] interpolation)) := by
  decide +kernel

omit [DecidableEq F] in
/-- Interpolating halves as the fold loop computes it. -/
theorem interpolate_eq (low high : List F) (r : F) :
    List.zipWith (· + ·) low ((List.zipWith (· - ·) high low).map (· * r)) =
      List.zipWith (fun low high => low + (high - low) * r) low high := by
  induction low generalizing high with
  | nil => simp
  | cons first low ih =>
      cases high with
      | nil => simp
      | cons second high => simp only [List.zipWith_cons_cons, List.map_cons, ih]

/-- The arguments of the check as the body names them. -/
abbrev checkEnv (xs point : List F) (claim : F) : Env F G :=
  (checkFunction.inputs.map (·.1)).zip
    [.vector "bls12-381.fr" xs, .vector "bls12-381.fr" point,
      .data (.field "bls12-381.fr" claim)]

/-- One installed operation that returns, with its exact charge. -/
local macro "charged_operation " evaluates:term : tactic =>
  `(tactic| apply Evaluated.ReturnsAfter.operation installed validator (by rfl) (by rfl) $evaluates (by rfl))

/-- A region whose condition is decided and whose branch returns `results`. -/
local macro "charged_cond " results:term : tactic =>
  `(tactic| apply Evaluated.ReturnsAfter.cond installed validator (results := $results) (by rfl) (by rfl)
    (length := by rfl))

/-- A Boolean constant. -/
local macro "charged_constant" : tactic =>
  `(tactic| apply Evaluated.ReturnsAfter.constant installed validator)

/-- A yield of found values. -/
local macro "charged_yield" : tactic =>
  `(tactic| exact Evaluated.ReturnsAfter.yield installed validator (by rfl))

/-- A loop over found bounds whose iterations return `results`. -/
local macro "charged_iterate " results:term : tactic =>
  `(tactic| apply Evaluated.ReturnsAfter.iterate installed validator (results := $results) (by rfl) (by rfl)
    (by rfl) (by rfl) (length := by rfl))

/-- The doubling loop of the authored shape check charges three instructions an
iteration. -/
theorem doubling_cost {first second two doubled carried induction : String}
    (carriedTwo : (carried == two) = false) (carriedInduction : (carried == induction) = false) :
    ∀ (count k start : Nat), k + count < 64 →
      (evalFor (fun env => evalSteps installed validator
          [.operation first "zkl_binding_0" [.text "2"] [] [two],
            .operation second "zkl_binding_6" [] [carried, two] [doubled], .yield [doubled]] env)
        induction [carried] [] (List.range' start count) [(.index (2 ^ k) : Value F G)]).ReturnsAfter
        [.index (2 ^ (k + count))] (3 * count)
  | 0, _, _, _ => Evaluated.ReturnsAfter.for_nil
  | count + 1, k, start, small => by
      have product : 2 ^ k * 2 < indexLimit := by
        rw [← pow_succ]
        exact indexLimit_pow (by omega)
      apply Evaluated.ReturnsAfter.of_eq
      · apply Evaluated.ReturnsAfter.for_cons (yielded := [.index (2 ^ k * 2)]) (length := rfl)
        · charged_operation (constant_returns 2)
          apply Evaluated.ReturnsAfter.operation installed validator (by rfl)
            (by simp [lookupAll, List.lookup, carriedTwo, carriedInduction])
            (mul_returns (indexLimit_pow (by omega)) (by decide) product) (by rfl)
          exact Evaluated.ReturnsAfter.yield installed validator (by simp [lookupAll, List.lookup])
        · rw [← pow_succ, show k + (count + 1) = k + 1 + count by omega]
          exact doubling_cost carriedTwo carriedInduction count (k + 1) (start + 1) (by omega)
      · omega

/-- The fold loop of the check charges fourteen instructions an iteration. -/
theorem restriction_cost (point : List F) (small : point.length < 64) :
    ∀ (count start : Nat) (current : List F), start + count = point.length →
      current.length = 2 ^ count →
      (evalFor (fun env => evalSteps installed validator restrictionBody env) restrictionInduction
          restrictionStateNames
          (restrictionCaptureNames.zip [.vector "bls12-381.fr" point, .index point.length])
          (List.range' start count)
          [(.vector "bls12-381.fr" current : Value F G), .index count, .index 1]).ReturnsAfter
        [.vector "bls12-381.fr" (restrictPrefixValues current (point.drop start)), .index 0, .index 1]
        (14 * count)
  | 0, start, current, ends, _ => by
      have dropped : point.drop start = [] := List.drop_eq_nil_of_le (by omega)
      rw [dropped]
      exact Evaluated.ReturnsAfter.for_nil
  | count + 1, start, current, ends, shape => by
      have inside : start < point.length := by omega
      have bounded : 2 ^ count < indexLimit := indexLimit_pow (by omega)
      have doubled : current.length = 2 * 2 ^ count := by rw [shape, pow_succ, Nat.mul_comm]
      have sixtyFour : (64 : Nat) < indexLimit := by decide
      have countBound : count + 1 < indexLimit := by omega
      have positive : 0 < 2 ^ count := Nat.two_pow_pos count
      apply Evaluated.ReturnsAfter.of_eq
      · apply Evaluated.ReturnsAfter.for_cons (yielded := [.vector "bls12-381.fr"
          (restrictValues current point[start]), .index (count + 1 - 1), .index 1]) (length := rfl)
        · charged_operation (get_returns inside)
          charged_operation (constant_returns 0)
          charged_operation (less_true (a := 0) (by decide) countBound (by omega))
          charged_cond []
          · charged_yield
          charged_operation (split_returns (by omega) (by omega))
          charged_operation (length_returns (by simp only [List.length_take]; omega))
          charged_operation (length_returns (by simp only [List.length_drop]; omega))
          charged_operation (equal_true (by simp only [List.length_take, List.length_drop]; omega))
          charged_operation require_returns
          apply Evaluated.ReturnsAfter.operation installed validator interpolation_resolves (by rfl)
            (map_returns (by simp only [List.length_take, List.length_drop]; omega)) (by rfl)
          charged_operation (constant_returns 1)
          charged_operation (sub_returns (b := 1) countBound (by decide) (by omega))
          charged_yield
        · rw [List.drop_eq_getElem_cons inside, restrictPrefixValues_cons]
          exact restriction_cost point small count (start + 1) (restrictValues current point[start]) (by omega)
            (restrictValues_length current point[start] doubled)
      · omega

/-- With a well-shaped table, the check charges `62 + 20 * n` instructions for a
point of `n` coordinates. -/
theorem check_shaped_cost {xs point : List F} {claim : F} (pointBound : point.length < indexLimit)
    (small : point.length < 64) (vectorBound : xs.length < indexLimit)
    (shaped : xs.length = 2 ^ point.length) :
    (evalSteps installed validator checkFunction.body (checkEnv (G := G) xs point claim)).ReturnsAfter
      [.data (.boolean (decide ((restrictPrefixValues xs point).foldl (· + ·) 0 = claim)))]
      (62 + 20 * point.length) := by
  apply Evaluated.ReturnsAfter.of_eq
  · charged_operation (length_returns pointBound)
    charged_operation (constant_returns 1)
    charged_operation (constant_returns 0)
    charged_operation (less_true (a := 0) (b := 1) (by decide) (by decide) (by decide))
    charged_cond [.data (.boolean true)]
    · charged_operation (constant_returns 64)
      charged_operation (less_true pointBound (by decide) small)
      charged_yield
    charged_cond [.data (.boolean true)]
    · charged_operation (length_returns vectorBound)
      charged_operation (mod_returns (b := 1) vectorBound (by decide) (by decide))
      charged_operation (constant_returns 0)
      charged_operation (equal_true (Nat.mod_one _))
      charged_yield
    charged_cond [.data (.boolean true)]
    · charged_operation (length_returns vectorBound)
      charged_operation (div_returns (b := 1) vectorBound (by decide) (by decide))
      charged_operation (constant_returns 64)
      charged_operation (less_true pointBound (by decide) small)
      charged_cond []
      · charged_yield
      charged_operation (constant_returns 1)
      charged_operation (constant_returns 0)
      charged_iterate [.index (2 ^ (0 + point.length))]
      · refine ⟨?_, ?_, ?_⟩ <;> omega
      · exact doubling_cost (count := point.length) (k := 0) (start := 0) (by decide) (by decide) (by omega)
      charged_operation (equal_true (by simpa using shaped))
      charged_yield
    charged_cond [.data (.boolean (decide ((restrictPrefixValues xs point).foldl (· + ·) 0 = claim)))]
    · charged_operation (length_returns pointBound)
      charged_operation (constant_returns 1)
      charged_operation (constant_returns 0)
      charged_operation (less_true (a := 0) (b := 1) (by decide) (by decide) (by decide))
      charged_cond [.data (.boolean true)]
      · charged_operation (constant_returns 64)
        charged_operation (less_true pointBound (by decide) small)
        charged_yield
      charged_cond [.data (.boolean true)]
      · charged_operation (length_returns vectorBound)
        charged_operation (mod_returns (b := 1) vectorBound (by decide) (by decide))
        charged_operation (constant_returns 0)
        charged_operation (equal_true (Nat.mod_one _))
        charged_yield
      charged_cond [.data (.boolean true)]
      · charged_operation (length_returns vectorBound)
        charged_operation (div_returns (b := 1) vectorBound (by decide) (by decide))
        charged_operation (constant_returns 64)
        charged_operation (less_true pointBound (by decide) small)
        charged_cond []
        · charged_yield
        charged_operation (constant_returns 1)
        charged_operation (constant_returns 0)
        charged_iterate [.index (2 ^ (0 + point.length))]
        · refine ⟨?_, ?_, ?_⟩ <;> omega
        · exact doubling_cost (count := point.length) (k := 0) (start := 0) (by decide) (by decide) (by omega)
        charged_operation (equal_true (by simpa using shaped))
        charged_yield
      charged_cond []
      · charged_yield
      charged_operation (length_returns pointBound)
      charged_operation (constant_returns 0)
      charged_iterate [.vector "bls12-381.fr" (restrictPrefixValues xs (point.drop 0)), .index 0, .index 1]
      · refine ⟨?_, ?_, ?_⟩ <;> omega
      · exact restriction_cost point small point.length 0 xs (by simp) shaped
      charged_operation sum_returns
      charged_operation fieldEqual_returns
      charged_yield
    exact Evaluated.ReturnsAfter.ret installed validator (by rfl)
  · omega

/-- A point too long for an index stops the check at its length. -/
theorem check_point_stops {xs point : List F} {claim : F} (overflow : ¬ point.length < indexLimit) :
    (evalSteps installed validator checkFunction.body (checkEnv (G := G) xs point claim)).Stops
      (.kernel .exhausted) := by
  stops_operation (length_stops overflow)

/-- A table too long for an index stops the check at its length. -/
theorem check_vector_stops {xs point : List F} {claim : F} (pointBound : point.length < indexLimit)
    (small : point.length < 64) (overflow : ¬ xs.length < indexLimit) :
    (evalSteps installed validator checkFunction.body (checkEnv (G := G) xs point claim)).Stops
      (.kernel .exhausted) := by
  continues_operation (length_returns pointBound)
  continues_operation (constant_returns 1)
  continues_operation (constant_returns 0)
  continues_operation (less_true (a := 0) (b := 1) (by decide) (by decide) (by decide))
  continues_true [.data (.boolean true)]
  · returns_operation (constant_returns 64)
    returns_operation (less_true pointBound (by decide) small)
    returns_yield
  stops_true
  stops_operation (length_stops overflow)

/-- A point of at least 64 coordinates fails the authored shape check. -/
theorem check_large {xs point : List F} {claim : F} (pointBound : point.length < indexLimit)
    (large : ¬ point.length < 64) :
    (evalSteps installed validator checkFunction.body (checkEnv (G := G) xs point claim)).Returns
      [.data (.boolean false)] := by
  returns_operation (length_returns pointBound)
  returns_operation (constant_returns 1)
  returns_operation (constant_returns 0)
  returns_operation (less_true (a := 0) (b := 1) (by decide) (by decide) (by decide))
  returns_true [.data (.boolean false)]
  · returns_operation (constant_returns 64)
    returns_operation (less_false pointBound (by decide) large)
    returns_yield
  returns_false [.data (.boolean false)]
  · returns_constant
    returns_yield
  returns_false [.data (.boolean false)]
  · returns_constant
    returns_yield
  returns_false [.data (.boolean false)]
  · returns_constant
    returns_yield
  returns_ret

/-- With a table whose length is not `2 ^ point.length`, the authored shape
check fails. -/
theorem check_unshaped {xs point : List F} {claim : F} (pointBound : point.length < indexLimit)
    (small : point.length < 64) (vectorBound : xs.length < indexLimit)
    (unshaped : xs.length ≠ 2 ^ point.length) :
    (evalSteps installed validator checkFunction.body (checkEnv (G := G) xs point claim)).Returns
      [.data (.boolean false)] := by
  returns_operation (length_returns pointBound)
  returns_operation (constant_returns 1)
  returns_operation (constant_returns 0)
  returns_operation (less_true (a := 0) (b := 1) (by decide) (by decide) (by decide))
  returns_true [.data (.boolean true)]
  · returns_operation (constant_returns 64)
    returns_operation (less_true pointBound (by decide) small)
    returns_yield
  returns_true [.data (.boolean true)]
  · returns_operation (length_returns vectorBound)
    returns_operation (mod_returns (b := 1) vectorBound (by decide) (by decide))
    returns_operation (constant_returns 0)
    returns_operation (equal_true (Nat.mod_one _))
    returns_yield
  returns_true [.data (.boolean false)]
  · returns_operation (length_returns vectorBound)
    returns_operation (div_returns (b := 1) vectorBound (by decide) (by decide))
    returns_operation (constant_returns 64)
    returns_operation (less_true pointBound (by decide) small)
    returns_true []
    · returns_yield
    returns_operation (constant_returns 1)
    returns_operation (constant_returns 0)
    returns_iterate [.index (2 ^ (0 + point.length))]
    · refine ⟨?_, ?_, ?_⟩ <;> omega
    · exact (doubling_cost (count := point.length) (k := 0) (start := 0) (by decide) (by decide)
        (by omega)).returns
    returns_operation (equal_false (by simpa using unshaped))
    returns_yield
  returns_false [.data (.boolean false)]
  · returns_constant
    returns_yield
  returns_ret

/-- The check hands back the authored shape predicate and the comparison of
the folded table's sum with the claim. -/
theorem check_returns {xs point : List F} {claim : F} (pointBound : point.length < indexLimit)
    (small : point.length < 64) (vectorBound : xs.length < indexLimit) :
    (evalSteps installed validator checkFunction.body (checkEnv (G := G) xs point claim)).Returns
      [.data (.boolean (decide (PrimitiveLibrary.HasShape xs point.length 1 ∧
        (restrictPrefixValues xs point).sum = claim)))] := by
  by_cases shaped : xs.length = 2 ^ point.length
  · have value : decide (PrimitiveLibrary.HasShape xs point.length 1 ∧
          (restrictPrefixValues xs point).sum = claim) =
        decide ((restrictPrefixValues xs point).foldl (· + ·) 0 = claim) := by
      rw [List.sum_eq_foldl]
      simp [PrimitiveLibrary.HasShape, shaped, small, Nat.mod_one]
    rw [value]
    exact (check_shaped_cost pointBound small vectorBound shaped).returns
  · have value : decide (PrimitiveLibrary.HasShape xs point.length 1 ∧
          (restrictPrefixValues xs point).sum = claim) = false := by
      simp [PrimitiveLibrary.HasShape, shaped]
    rw [value]
    exact check_unshaped pointBound small vectorBound shaped

/-- The terminal check's body implements the source's check helper. -/
theorem check_prepared : Prepared installed validator (helperTable program F G) checkHelper.name := by
  intro callee found arguments length sorted
  rw [checkFunction_eq, Option.some.injEq] at found
  subst found
  have inputs : checkFunction.inputs.length = 3 := rfl
  rw [inputs] at length
  rcases arguments with _ | ⟨first, _ | ⟨second, _ | ⟨third, _ | ⟨_, _⟩⟩⟩⟩
  · simp at length
  · simp at length
  · simp at length
  rotate_left
  · simp at length
  · obtain ⟨xs, xsEq⟩ := sorted 0 first (.data (.vector "bls12-381.fr")) rfl rfl
    obtain ⟨point, pointEq⟩ := sorted 1 second (.data (.vector "bls12-381.fr")) rfl rfl
    obtain ⟨claim, claimEq⟩ := sorted 2 third (.data (.field "bls12-381.fr")) rfl rfl
    subst xsEq pointEq claimEq
    rw [call_eq SumcheckSourceAssociations.check_association _ (SumcheckHelperLaws.checkInputs xs point claim)
      rfl]
    have envEq : (checkFunction.inputs.map (·.1)).zip
        [Value.encode (F := F) (G := G) (.vector "bls12-381.fr") xs, Value.encode (.vector "bls12-381.fr") point,
          Value.encode (.field "bls12-381.fr") claim] = checkEnv xs point claim := rfl
    rw [envEq]
    by_cases pointBound : point.length < indexLimit
    · by_cases small : point.length < 64
      · by_cases vectorBound : xs.length < indexLimit
        · rw [SumcheckSourceContracts.check_equation xs point claim vectorBound pointBound]
          obtain ⟨cost, evaluated⟩ := check_returns (G := G) (claim := claim) pointBound small vectorBound
          rw [evaluated]
          exact ⟨rfl, rfl, sorted_single (hasSort_encode .boolean _)⟩
        · rw [SumcheckSourceContracts.check_vector_exhausted xs point claim small vectorBound]
          obtain ⟨cost, evaluated⟩ := check_vector_stops (G := G) (claim := claim) pointBound small vectorBound
          rw [evaluated]
          rfl
      · rw [SumcheckSourceContracts.check_large_dimension xs point claim pointBound small]
        obtain ⟨cost, evaluated⟩ := check_large (G := G) (xs := xs) (claim := claim) pointBound small
        rw [evaluated]
        exact ⟨rfl, rfl, sorted_single (hasSort_encode .boolean _)⟩
    · rw [SumcheckSourceContracts.check_point_exhausted xs point claim pointBound]
      obtain ⟨cost, evaluated⟩ := check_point_stops (G := G) (xs := xs) (claim := claim) pointBound
      rw [evaluated]
      rfl

/-- Every helper the constructed Sumcheck validator calls by name is prepared. -/
theorem prepared : ∀ name ∈ [pendingHelper.name, openClaimHelper.name, appendHelper.name, atPrefixHelper.name, checkHelper.name],
    Prepared installed validator (helperTable program F G) name := by
  intro name member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact pending_prepared
  · exact openClaim_prepared
  · exact append_prepared
  · exact atPrefix_prepared
  · exact check_prepared

end Check

/-! ## Calls of the source's helpers -/

section Calls

/-- The point extension helper appends the challenge to the point. -/
theorem append_call (point : List F) (challenge : F) :
    callHelper (helperTable program F G) appendHelper.name
      [.vector "bls12-381.fr" point, .data (.field "bls12-381.fr" challenge)] =
      .returned [.vector "bls12-381.fr" (point ++ [challenge])] := by
  rw [call_eq SumcheckSourceContracts.bodies.append _ (.cons point (.cons challenge .nil)) rfl,
    SumcheckUnitContracts.append_equation SumcheckSourceViews.unit.linked SumcheckSourceContracts.bodies]
  rfl

/-- The terminal check helper compares the table's authored shape and the sum
of the table restricted at the point with the claim. -/
theorem check_call {xs point : List F} {claim : F} (vectorBound : xs.length < indexLimit)
    (pointBound : point.length < indexLimit) :
    callHelper (helperTable program F G) checkHelper.name
        [.vector "bls12-381.fr" xs, .vector "bls12-381.fr" point, .data (.field "bls12-381.fr" claim)] =
      .returned [.data (.boolean (decide (PrimitiveLibrary.HasShape xs point.length 1 ∧
        (restrictPrefixValues xs point).sum = claim)))] := by
  rw [call_eq SumcheckSourceAssociations.check_association _ (SumcheckHelperLaws.checkInputs xs point claim) rfl,
    SumcheckSourceContracts.check_equation xs point claim vectorBound pointBound]
  rfl

/-- The terminal check's charge on a well-shaped table: what the helper call
charges for its body. -/
theorem check_cost {xs point : List F} {claim : F} (small : point.length < 64)
    (shaped : xs.length = 2 ^ point.length) :
    helperCost installed validator checkHelper.name
      [(.vector "bls12-381.fr" xs : Value F G), .vector "bls12-381.fr" point,
        .data (.field "bls12-381.fr" claim)] = 62 + 20 * point.length := by
  have pointBound : point.length < indexLimit := lt_trans small (by decide)
  have vectorBound : xs.length < indexLimit := by
    rw [shaped]
    exact indexLimit_pow small
  have evaluated := check_shaped_cost (G := G) (claim := claim) pointBound small vectorBound shaped
  unfold helperCost Validator.evaluateCall
  rw [checkFunction_eq]
  simp only [show checkFunction.inputs.length = 3 from rfl, List.length_cons, List.length_nil]
  simp only [ite_true]
  have envEq : (checkFunction.inputs.map (·.1)).zip
      [(.vector "bls12-381.fr" xs : Value F G), .vector "bls12-381.fr" point,
        .data (.field "bls12-381.fr" claim)] = checkEnv xs point claim := rfl
  rw [envEq, evaluated]
  rfl

end Calls

end ZkcExamples.Executable.SumcheckHelpers
