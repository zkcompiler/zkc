import Zkc.Compiler.Checking
import Zkc.Source.InputBinding
import Zkc.Source.PublicDimensions
import Zkc.Polynomial.Multilinear
import Zkc.Polynomial.Coordinates
import Mathlib.Data.ZMod.Basic
import Lean

/-! C1 design client. This file instantiates the maintained source and direct plan;
it does not extend their syntax or implement a native allocator or wire codec. -/

set_option autoImplicit false

namespace C1
open Zkc.Source Zkc.Compiler
namespace TableModel

structure Table (F : Type) (n : Nat) where
  origin : Nat
  cells : List F
  shape : cells.length = 2 ^ n

def admit {F : Type} (n origin : Nat) (cells : List F) : Option (Table F n) :=
  if h : cells.length = 2 ^ n then some ⟨origin, cells, h⟩ else none

def vector {F : Type} {n : Nat} (t : Table F n) (i : Fin (2 ^ n)) : F :=
  t.cells[i.val]'(by rw [t.shape]; exact i.isLt)

def logical {F : Type} {n : Nat} (t : Table F n) :=
  Zkc.Polynomial.Multilinear.ofVector (vector t)

theorem original_cell {F : Type} {n : Nat} (t : Table F n) (i : Fin (2 ^ n)) :
    logical t (Zkc.Polynomial.Multilinear.vertex n i) = vector t i :=
  Zkc.Polynomial.Multilinear.ofVector_vertex (vector t) i

structure Residual (F : Type) (n : Nat) where
  root : Table F n
  coordinates : List F
  bound : coordinates.length ≤ n

def view {F : Type} {n : Nat} (t : Table F n) : Residual F n := ⟨t, [], by simp⟩

def extend {F : Type} {n : Nat} (v : Residual F n) (r : F)
    (room : v.coordinates.length < n) : Residual F n :=
  ⟨v.root, v.coordinates ++ [r], by simp; omega⟩

def restrict {F : Type} {n : Nat} (v : Residual F n) (r : F) : Option (Residual F n) :=
  if room : v.coordinates.length < n then some (extend v r room) else none

def atPoint {F : Type} [CommRing F] {n : Nat} (t : Table F n)
    (point : List F) (shape : point.length = n) : F :=
  Zkc.Polynomial.Multilinear.extension n (logical t)
    (fun i => point[i.val]'(by rw [shape]; exact i.isLt))

def evaluate {F : Type} [CommRing F] {n : Nat} (v : Residual F n)
    (tail : List F) : Option F :=
  if shape : (v.coordinates ++ tail).length = n then some (atPoint v.root _ shape) else none

theorem extend_root {F : Type} {n : Nat} (v : Residual F n) (r : F)
    (room : v.coordinates.length < n) : (extend v r room).root = v.root := rfl

theorem evaluate_original {F : Type} [CommRing F] {n : Nat} (v : Residual F n)
    (tail : List F) (shape : (v.coordinates ++ tail).length = n) :
    evaluate v tail = some (atPoint v.root (v.coordinates ++ tail) shape) := by
  simp [evaluate, shape]

/-- Restricting one coordinate and then evaluating retains the original order,
including invalid final arity. This is uniform in the field and original rank. -/
theorem restrict_evaluate {F : Type} [CommRing F] {n : Nat} (v : Residual F n)
    (r : F) (room : v.coordinates.length < n) (tail : List F) :
    evaluate (extend v r room) tail = evaluate v (r :: tail) := by
  simp [evaluate, extend, List.append_assoc]

theorem restriction_exhausted {F : Type} {n : Nat} (v : Residual F n) (r : F)
    (full : v.coordinates.length = n) : restrict v r = none := by
  simp [restrict, full]

theorem atPoint_coordinates {F : Type} [CommRing F] {n : Nat} (t : Table F n)
    (point : List F) (shape : point.length = n) :
    atPoint t point shape = Zkc.Polynomial.Multilinear.extension n (logical t)
      (Zkc.Polynomial.coordinates n point) := by
  unfold atPoint
  congr 1
  funext i
  have within : i.val < point.length := by rw [shape]; exact i.isLt
  simp [Zkc.Polynomial.coordinates, within]

/-- Exact bridge to the specification's maintained indexed prefix join. -/
theorem evaluate_indexed_join {F : Type} [CommRing F] {n m : Nat}
    (t : Table F (n + m)) (fixed tail : List F)
    (fixedSize : fixed.length = m) (tailSize : tail.length = n) :
    evaluate ⟨t, fixed, by omega⟩ tail =
      some (Zkc.Polynomial.Multilinear.extension (n + m) (logical t)
        (Zkc.Polynomial.Quadratic.point m (Zkc.Polynomial.coordinates m fixed)
          (Zkc.Polynomial.coordinates n tail))) := by
  rw [evaluate_original _ _ (by simp [fixedSize, tailSize, Nat.add_comm]),
    atPoint_coordinates, Zkc.Polynomial.point_coordinates m fixed tail fixedSize tailSize]

end TableModel
open TableModel

inductive Domain where | two | seven deriving DecidableEq, Repr
abbrev Field : Domain → Type | .two => ZMod 2 | .seven => ZMod 7
instance (d : Domain) : CommRing (Field d) := by cases d <;> infer_instance
instance (d : Domain) : DecidableEq (Field d) := by cases d <;> infer_instance

inductive Ty where
  | boolean | digest | summary
  | scalar (d : Domain)
  | table (d : Domain) (originalRank : Nat)
  | residual (d : Domain) (originalRank : Nat)
  | point (d : Domain)
  deriving DecidableEq, Repr

abbrev Value : Ty → Type
  | .boolean => Bool
  | .digest => Nat
  | .summary => Field .two × Field .seven × Nat
  | .scalar d => Field d
  | .table d n => Table (Field d) n
  | .residual d n => Residual (Field d) n
  | .point d => List (Field d)

inductive Op where
  | view (d : Domain) (n : Nat)
  | restrict (d : Domain) (n : Nat)
  | evaluate (d : Domain) (n : Nat)
  | add (d : Domain)
  | record (d : Domain)
  | abortWrite (d : Domain)
  | orderedPair | pack
  deriving DecidableEq, Repr

def arguments : Op → List Ty
  | .view d n => [.table d n]
  | .restrict d n => [.residual d n, .scalar d]
  | .evaluate d n => [.residual d n, .point d]
  | .add d => [.scalar d, .scalar d]
  | .record d | .abortWrite d => [.scalar d]
  | .orderedPair => [.digest, .digest]
  | .pack => [.scalar .two, .scalar .seven, .digest]

def result : Op → Ty
  | .view d n | .restrict d n => .residual d n
  | .evaluate d _ | .add d => .scalar d
  | .record _ | .abortWrite _ => .boolean
  | .orderedPair => .digest
  | .pack => .summary

abbrev language : Language := ⟨Ty, Op, arguments, result, .boolean⟩
structure Request where
  domain : Domain
  value : Field domain
  abort : Bool
abbrev interface : PIR.Signature := ⟨Request, fun _ => Bool⟩

def checked {A : Type} (value : Option A) : PIR.Proc interface A :=
  match value with | some x => .done x | none => .halt .refused

abbrev meaning : Interpretation language interface where
  Value := Value
  condition := id
  operation
    | .view _ _, .cons t .nil => .done (view t)
    | .restrict _ _, .cons v (.cons r .nil) => checked (restrict v r)
    | .evaluate d _, .cons v (.cons p .nil) => checked (evaluate (F := Field d) v p)
    | .add _, .cons a (.cons b .nil) => .done (a + b)
    | .record d, .cons x .nil => .call ⟨d, x, false⟩ .done
    | .abortWrite d, .cons x .nil => .call ⟨d, x, true⟩ .done
    | .orderedPair, .cons a (.cons b .nil) => .done (Nat.pair a b)
    | .pack, .cons a (.cons b (.cons c .nil)) => .done (a, b, c)

structure World where
  two : Field .two := 0
  seven : Field .seven := 0
  writes : Nat := 0

structure Event where
  domain : Domain
  value : Nat
  deriving DecidableEq, Repr

def write (request : Request) (world : World) : World :=
  match request with
  | ⟨.two, x, _⟩ => { world with two := x, writes := world.writes + 1 }
  | ⟨.seven, x, _⟩ => { world with seven := x, writes := world.writes + 1 }

def event (request : Request) : Event :=
  match request with
  | ⟨.two, x, _⟩ => ⟨.two, x.val⟩
  | ⟨.seven, x, _⟩ => ⟨.seven, x.val⟩

def handler : PIR.Handler interface World Event := fun request world =>
  ⟨if request.abort then .stopped .abort else .returned (decide (request.value ≠ 0)),
    write request world, [event request]⟩

theorem failed_write_retained (d : Domain) (x : Field d) (world : World) :
    handler ⟨d, x, true⟩ world =
      ⟨.stopped .abort, write ⟨d, x, true⟩ world, [event ⟨d, x, true⟩]⟩ := rfl

theorem false_reply_retained (d : Domain) (world : World) :
    handler ⟨d, 0, false⟩ world =
      ⟨.returned false, write ⟨d, 0, false⟩ world, [event ⟨d, 0, false⟩]⟩ := by
  simp [handler]

theorem direct_preserves {Γ : List Ty} {ty : Ty}
    (source : Program language Γ ty) (values : Values Value Γ) (world : World) :
    (lower source).run meaning handler values.get world =
      (source.denote meaning values.get).run handler world :=
  lower_correct meaning handler source values.get world

namespace Controls

open Zkc.Source.PublicDimensions

/-- A concrete public-rank template, not a general dependent frontend. -/
def specialize (rawRank : RawDim) (publicInputs : List Nat) :
    Option (Σ n, Program language [.table .seven n, .point .seven] (.scalar .seven)) := do
  let rank ← rawRank.scope 1
  let environment ← publicEnv publicInputs 1
  let n := rank.eval environment
  let body : RawProgram Ty Op :=
    .letOp (.view .seven n) [0] (.letOp (.evaluate .seven n) [0, 2] (.ret 0))
  let formed ← (body.elaborate [.table .seven n, .point .seven]
    (.scalar .seven) (language := language)).toOption
  pure ⟨n, formed⟩

theorem public_rank_selected : (specialize (.pub 0) [2]).map Sigma.fst = some 2 := by decide
theorem extra_public_refused : (specialize (.pub 0) [2, 3]).isSome = false := by decide
theorem hidden_annihilated_refused :
    (specialize (.mul (.lit 0) (.hidden 0)) [2]).isSome = false := by decide

def t2 : Table (ZMod 2) 1 := ⟨10, [0, 1], by decide⟩
def t7 : Table (ZMod 7) 2 := ⟨11, [0, 1, 2, 4], by decide⟩
def t0 : Table (ZMod 7) 0 := ⟨12, [6], by decide⟩

-- Source roles and all declared captures are bound before any body executes.
def declarations : List (InputDeclaration Ty) := [
  ⟨"binary", .table .two 1, .shared, .capture⟩,
  ⟨"seven", .table .seven 2, .shared, .capture⟩,
  ⟨"r2", .scalar .two, .shared, .argument⟩,
  ⟨"r7", .scalar .seven, .shared, .argument⟩,
  ⟨"tail2", .point .two, .shared, .argument⟩,
  ⟨"tail7", .point .seven, .shared, .argument⟩,
  ⟨"left", .digest, .shared, .capture⟩,
  ⟨"right", .digest, .shared, .capture⟩,
  ⟨"dormant", .scalar .seven, .privateTo "prover", .capture⟩]

abbrev context := declarations.map InputDeclaration.type
def supplied : List (SuppliedInput Value) := [
  ⟨"binary", .table .two 1, t2⟩, ⟨"seven", .table .seven 2, t7⟩,
  ⟨"r2", .scalar .two, 1⟩, ⟨"r7", .scalar .seven, 2⟩,
  ⟨"tail2", .point .two, []⟩, ⟨"tail7", .point .seven, [3]⟩,
  ⟨"left", .digest, 2⟩, ⟨"right", .digest, 5⟩,
  ⟨"dormant", .scalar .seven, 6⟩]

def bound : Values Value context :=
  (bindInputs "prover" declarations supplied).toOption.get (by decide)

def raw : RawProgram Ty Op :=
  .letOp (.view .two 1) [0]
  (.letOp (.restrict .two 1) [0, 3]
  (.letOp (.evaluate .two 1) [0, 6]
  (.letOp (.view .seven 2) [4]
  (.letOp (.restrict .seven 2) [0, 7]
  (.letOp (.evaluate .seven 2) [0, 10]
  (.letOp .orderedPair [12, 13]
  (.letOp .pack [4, 1, 0] (.ret 0))))))))

def source : Program language context .summary :=
  (raw.elaborate context .summary (language := language)).toOption.get (by decide)
def run := (lower source).run meaning handler bound.get {}

theorem separate_domains : run.outcome = .returned (1, 6, Nat.pair 2 5) := by decide
theorem separate_pure_effects : run.state.writes = 0 ∧ run.events = [] := by decide
theorem direct_accepted : (checkDirect source (lower source).erase).isSome = true := by decide

def swapped : RawProgram Ty Op :=
  .letOp (.view .two 1) [0]
  (.letOp (.restrict .two 1) [0, 3]
  (.letOp (.evaluate .two 1) [0, 6]
  (.letOp (.view .seven 2) [4]
  (.letOp (.restrict .seven 2) [0, 7]
  (.letOp (.evaluate .seven 2) [0, 10]
  (.letOp .orderedPair [13, 12]
  (.letOp .pack [4, 1, 0] (.ret 0))))))))

theorem swap_forms : (swapped.elaborate context .summary (language := language)).isOk = true := by decide
theorem swap_refused : (checkDirect source swapped).isSome = false := by decide
theorem pair_order_matters : Nat.pair 2 5 ≠ Nat.pair 5 2 := by decide
theorem loop_capacity_needs_growth :
    Nat.pair 2 2 = 8 ∧ Nat.pair 8 8 = 80 ∧ (2 * 2 + 1)^2 < 80 := by decide
theorem cross_field_refused :
    ((RawProgram.letOp (.add .two) [2, 3] (.ret 0)).elaborate
      context (.scalar .two) (language := language)).isOk = false := by decide
theorem cross_table_refused :
    ((RawProgram.letOp (.view .two 2) [1] (.ret 0)).elaborate
      context (.residual .two 2) (language := language)).isOk = false := by decide
theorem cross_point_refused :
    ((RawProgram.letOp (.view .two 1) [0]
      (.letOp (.evaluate .two 1) [0, 6] (.ret 0))).elaborate
      context (.scalar .two) (language := language)).isOk = false := by decide
theorem missing_dormant_refused :
    (bindInputs "prover" declarations (supplied.take 8)).isOk = false := by decide
theorem private_role_refused :
    (bindInputs "verifier" declarations supplied).isOk = false := by decide
theorem zero_body_checked :
    ((RawProgram.iterate 0 (.scalar .two) 2 (.ret 99) (.ret 0)).elaborate
      context (.scalar .two) (language := language)).isOk = false := by decide

theorem malformed_table_refused : (admit 2 0 ([0, 1] : List (ZMod 7))).isSome = false := by decide
theorem zero_dimension : evaluate (view t0) [] = some 6 := by decide
theorem zero_dimension_restrict_refused : (restrict (view t0) 1).isSome = false := by decide
theorem wrong_point_refused : evaluate (view t7) [2] = none := by decide
theorem prefix_order : evaluate (extend (view t7) 2 (by decide)) [3] = some 6 := by decide
theorem prefix_reversed_differs : evaluate (extend (view t7) 3 (by decide)) [2] = some 0 := by decide

abbrev loopContext : List Ty := [.scalar .two, .scalar .two]
def loopRaw : RawProgram Ty Op :=
  .iterate 3 (.scalar .two) 0
    (.letOp (.record .two) [0] (.letOp (.add .two) [1, 3] (.ret 0))) (.ret 0)
def loopSource : Program language loopContext (.scalar .two) :=
  (loopRaw.elaborate loopContext (.scalar .two) (language := language)).toOption.get (by decide)
def loopValues : Values Value loopContext := .cons 0 (.cons 1 .nil)
def loopRun := (lower loopSource).run meaning handler loopValues.get {}
theorem three_natural_iterations : loopRun.outcome = .returned 1 ∧
    loopRun.state.writes = 3 ∧ loopRun.events = [⟨.two, 0⟩, ⟨.two, 1⟩, ⟨.two, 0⟩] := by decide

abbrev residualContext : List Ty := [.residual .seven 2, .scalar .seven, .point .seven]
def restrictLoopRaw : RawProgram Ty Op :=
  .iterate 2 (.residual .seven 2) 0
    (.letOp (.restrict .seven 2) [0, 2] (.ret 0))
    (.letOp (.evaluate .seven 2) [0, 3] (.ret 0))
def restrictLoop : Program language residualContext (.scalar .seven) :=
  (restrictLoopRaw.elaborate residualContext (.scalar .seven) (language := language)).toOption.get (by decide)
def residualValues : Values Value residualContext := .cons (view t7) (.cons 2 (.cons [] .nil))
theorem shrinking_prefix_loop :
    ((lower restrictLoop).run meaning handler residualValues.get {}).outcome = .returned 3 := by decide

def failureRaw : RawProgram Ty Op :=
  .letOp (.abortWrite .two) [0] (.letOp (.record .two) [2] (.ret 0))
def failureSource : Program language loopContext .boolean :=
  (failureRaw.elaborate loopContext .boolean (language := language)).toOption.get (by decide)
def failureRun := (lower failureSource).run meaning handler loopValues.get { two := 1, writes := 4 }
theorem failed_call_prefix : failureRun.outcome = .stopped .abort ∧
    failureRun.state.two = 0 ∧ failureRun.state.writes = 5 ∧
    failureRun.events = [⟨.two, 0⟩] := by decide

def branchRaw : RawProgram Ty Op :=
  .letOp (.record .two) [0]
    (.branch 0 (.letOp (.record .two) [2] (.ret 0)) (.stop .reject))
def branchSource : Program language loopContext .boolean :=
  (branchRaw.elaborate loopContext .boolean (language := language)).toOption.get (by decide)
def branchRun := (lower branchSource).run meaning handler loopValues.get {}
theorem false_branch_stop : branchRun.outcome = .stopped .reject ∧
    branchRun.state.writes = 1 ∧ branchRun.events = [⟨.two, 0⟩] := by decide

def successfulValues : Values Value loopContext := .cons 1 (.cons 1 .nil)
def successfulRun := (lower branchSource).run meaning handler successfulValues.get {}
theorem successful_branch : successfulRun.outcome = .returned true ∧
    successfulRun.state.two = 1 ∧ successfulRun.state.writes = 2 ∧
    successfulRun.events = [⟨.two, 1⟩, ⟨.two, 1⟩] := by decide

def shapeFailureRaw : RawProgram Ty Op :=
  .letOp (.record .seven) [1]
    (.letOp (.evaluate .seven 2) [1, 3] (.ret 0))
def shapeFailure : Program language residualContext (.scalar .seven) :=
  (shapeFailureRaw.elaborate residualContext (.scalar .seven)
    (language := language)).toOption.get (by decide)
def shapeFailureRun := (lower shapeFailure).run meaning handler residualValues.get {}
theorem bad_shape_keeps_prior_write : shapeFailureRun.outcome = .stopped .refused ∧
    shapeFailureRun.state.seven = 2 ∧ shapeFailureRun.state.writes = 1 ∧
    shapeFailureRun.events = [⟨.seven, 2⟩] := by decide

def stoppedLoopRaw : RawProgram Ty Op :=
  .iterate 3 (.scalar .two) 0
    (.letOp (.record .two) [0] (.stop .reject))
    (.letOp (.record .two) [0] (.ret 1))
def stoppedLoop : Program language loopContext (.scalar .two) :=
  (stoppedLoopRaw.elaborate loopContext (.scalar .two)
    (language := language)).toOption.get (by decide)
def stoppedLoopRun := (lower stoppedLoop).run meaning handler loopValues.get {}
theorem stop_skips_iterations_and_suffix : stoppedLoopRun.outcome = .stopped .reject ∧
    stoppedLoopRun.state.writes = 1 ∧ stoppedLoopRun.events = [⟨.two, 0⟩] := by decide

end Controls

namespace Protocols

inductive Call where
  | base (request : Request)
  | send (atZero atOne : Field .seven)
  | draw
abbrev Reply : Call → Type
  | .base _ | .send _ _ => Bool
  | .draw => Field .seven
abbrev protocolInterface : PIR.Signature := ⟨Call, Reply⟩

def lift {A : Type} : PIR.Proc interface A → PIR.Proc protocolInterface A
  | .done x => .done x
  | .halt why => .halt why
  | .call request next => .call (.base request) (fun reply => lift (next reply))

inductive Operation where
  | base (op : Op)
  | send | draw | linear | point | equal
  | endpointPoint (atOne : Bool)
  | parent (siblingOnLeft : Bool)
  | digestEqual
  deriving DecidableEq, Repr

def arguments : Operation → List Ty
  | .base op => C1.arguments op
  | .send | .equal => [.scalar .seven, .scalar .seven]
  | .draw | .endpointPoint _ => []
  | .linear => [.scalar .seven, .scalar .seven, .scalar .seven]
  | .point => [.scalar .seven]
  | .parent _ | .digestEqual => [.digest, .digest]
def result : Operation → Ty
  | .base op => C1.result op
  | .send | .equal | .digestEqual => .boolean
  | .draw | .linear => .scalar .seven
  | .point | .endpointPoint _ => .point .seven
  | .parent _ => .digest
abbrev language : Language := ⟨Ty, Operation, arguments, result, .boolean⟩
abbrev meaning : Interpretation language protocolInterface where
  Value := Value
  condition := id
  operation
    | .base op, args => lift (C1.meaning.operation op args)
    | .send, .cons a (.cons b .nil) => .call (.send a b) .done
    | .draw, .nil => .call .draw .done
    | .linear, .cons a (.cons b (.cons r .nil)) => .done ((1-r)*a+r*b)
    | .point, .cons r .nil => .done [r]
    | .endpointPoint atOne, .nil => .done [if atOne then 1 else 0]
    | .equal, .cons a (.cons b .nil) => .done (decide (a=b))
    | .parent left, .cons value (.cons sibling .nil) =>
        .done (if left then Nat.pair sibling value else Nat.pair value sibling)
    | .digestEqual, .cons a (.cons b .nil) => .done (decide (a=b))

structure State where
  base : World := {}
  sent : List (Field .seven × Field .seven) := []
  tape : List (Field .seven) := []
inductive Trace where
  | base (event : Event)
  | sent (atZero atOne : Nat)
  | drawn (value : Nat)
  deriving DecidableEq, Repr

def handler : PIR.Handler protocolInterface State Trace
  | .base request, state =>
      let out := C1.handler request state.base
      ⟨out.outcome, { state with base := out.state }, out.events.map Trace.base⟩
  | .send a b, state =>
      ⟨.returned true, { state with sent := state.sent ++ [(a,b)] }, [.sent a.val b.val]⟩
  | .draw, state =>
      match state.tape with
      | [] => ⟨.stopped .exhausted, state, []⟩
      | r :: rest => ⟨.returned r, { state with tape := rest }, [.drawn r.val]⟩

/-- A closed one-variable, degree-one Sumcheck trace with an actual table terminal.
The handler supplies a deterministic challenge tape; this is not a fresh law. -/
abbrev sumContext : List Ty := [.table .seven 1, .scalar .seven]
def sumRaw : RawProgram Ty Operation :=
  .letOp (.endpointPoint false) []
  (.letOp (.endpointPoint true) []
  (.letOp (.base (.view .seven 1)) [2]
  (.letOp (.base (.evaluate .seven 1)) [0, 2]
  (.letOp (.base (.evaluate .seven 1)) [1, 2]
  (.letOp .send [1, 0]
  (.letOp (.base (.add .seven)) [2, 1]
  (.letOp .equal [0, 8]
  (.branch 0
    (.letOp .draw []
    (.letOp .linear [5, 4, 0]
    (.letOp .point [1]
    (.letOp (.base (.evaluate .seven 1)) [8, 0]
    (.letOp .equal [0, 2] (.ret 0))))))
    (.stop .reject)))))))))
def sumSource : Program language sumContext .boolean :=
  (sumRaw.elaborate sumContext .boolean (language := language)).toOption.get (by decide)
def sumTable : Table (ZMod 7) 1 := ⟨20, [2,5], by decide⟩
def sumDeclarations : List (InputDeclaration Ty) := [
  ⟨"table", .table .seven 1, .shared, .capture⟩,
  ⟨"claim", .scalar .seven, .shared, .argument⟩]
def sumSupplied (claim : ZMod 7) : List (SuppliedInput Value) := [
  ⟨"table", .table .seven 1, sumTable⟩, ⟨"claim", .scalar .seven, claim⟩]
def sumValues (claim : ZMod 7) : Values Value sumContext :=
  (bindInputs "trace" sumDeclarations (sumSupplied claim)).toOption.get (by rfl)
def sumRun (claim : ZMod 7) (tape : List (ZMod 7)) :=
  (lower sumSource).run meaning handler (sumValues claim).get { tape := tape }

theorem sumcheck_complete : (sumRun 0 [3]).outcome = .returned true ∧
    (sumRun 0 [3]).state.sent = [(2,5)] ∧ (sumRun 0 [3]).state.tape = [] ∧
    (sumRun 0 [3]).events = [.sent 2 5, .drawn 3] := by decide
theorem sumcheck_wrong_claim : (sumRun 1 [3]).outcome = .stopped .reject ∧
    (sumRun 1 [3]).state.tape = [3] ∧ (sumRun 1 [3]).events = [.sent 2 5] := by decide
theorem sumcheck_short_tape : (sumRun 0 []).outcome = .stopped .exhausted ∧
    (sumRun 0 []).state.sent = [(2,5)] ∧ (sumRun 0 []).events = [.sent 2 5] := by decide
theorem sumcheck_extra_tape : (sumRun 0 [3,6]).outcome = .returned true ∧
    (sumRun 0 [3,6]).state.tape = [6] := by decide
theorem sumcheck_direct_checked :
    (checkDirect sumSource (lower sumSource).erase).isSome = true := by decide

theorem affine_original {F : Type} [CommRing F] (t : Table F 1) (r : F) :
    atPoint t [r] (by simp) =
      (1-r)*atPoint t [0] (by simp) + r*atPoint t [1] (by simp) := by
  simp [atPoint, Zkc.Polynomial.Multilinear.extension]

abbrev merkleContext : List Ty := [.digest, .digest, .digest, .digest]
def merkleRaw (firstLeft : Bool) : RawProgram Ty Operation :=
  .letOp (.parent firstLeft) [0, 1]
    (.letOp (.parent false) [0, 3] (.letOp .digestEqual [0, 5] (.ret 0)))
def merkleSource (firstLeft : Bool) : Program language merkleContext .boolean :=
  ((merkleRaw firstLeft).elaborate merkleContext .boolean
    (language := language)).toOption.get (by cases firstLeft <;> decide)
def merkleDeclarations : List (InputDeclaration Ty) := [
  ⟨"leaf", .digest, .shared, .argument⟩,
  ⟨"sibling0", .digest, .shared, .capture⟩,
  ⟨"sibling1", .digest, .shared, .capture⟩,
  ⟨"root", .digest, .shared, .argument⟩]
def merkleSupplied : List (SuppliedInput Value) := [
  ⟨"leaf", .digest, 2⟩, ⟨"sibling0", .digest, 5⟩, ⟨"sibling1", .digest, 9⟩,
  ⟨"root", .digest, Nat.pair (Nat.pair 2 5) 9⟩]
def merkleValues : Values Value merkleContext :=
  (bindInputs "verifier" merkleDeclarations merkleSupplied).toOption.get (by decide)
def merkleRun (firstLeft : Bool) :=
  (lower (merkleSource firstLeft)).run meaning handler merkleValues.get {}
theorem merkle_ordered_path : (merkleRun false).outcome = .returned true ∧
    (merkleRun false).events = [] := by decide
theorem merkle_reversed_path : (merkleRun true).outcome = .returned false := by decide
theorem merkle_changed_path_refused :
    (checkDirect (merkleSource false) (merkleRaw true)).isSome = false := by decide
theorem merkle_direct_checked :
    (checkDirect (merkleSource false) (lower (merkleSource false)).erase).isSome = true := by decide

theorem protocol_direct_preserves {Γ : List Ty} {ty : Ty}
    (source : Program language Γ ty) (values : Values Value Γ) (state : State) :
    (lower source).run meaning handler values.get state =
      (source.denote meaning values.get).run handler state :=
  lower_correct meaning handler source values.get state

end Protocols
end C1

-- Audit locally elaborated declarations too: the maintained imported-module
-- auditor alone would miss this standalone file's current declarations.
run_cmd do
  let env ← Lean.getEnv
  let mut count : Nat := 0
  let mut theorems : Nat := 0
  for (name, info) in env.constants.toList do
    if (`C1).isPrefixOf name then
      count := count + 1
      if info.isTheorem then theorems := theorems + 1
      for axiomName in ← Lean.collectAxioms name do
        unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
          throwError "C1 unexpected axiom: {name}: {axiomName}"
  unless count > 0 ∧ theorems > 0 do throwError "C1 empty declaration audit"
  Lean.logInfo m!"C1-AUDIT-PASS declarations={count} theorems={theorems}"
