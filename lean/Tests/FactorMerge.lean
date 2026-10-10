import Zkc.Compiler.FactorOptimization.Size
import Tests.FactorOptimization

/-! Outcome merging: useful shared facts, precision loss, failed writes, refusal,
source control, exact candidate admission and unequal-transfer growth controls.
-/

set_option autoImplicit false

namespace Tests.FactorMerge

open Zkc.Source Zkc.Compiler Zkc.Source.FactorQueries
open Zkc.Modules.Factor Zkc.Modules.FactorState

abbrev retained := Tests.FactorOptimization.retained
abbrev query := Tests.FactorOptimization.query

def other : Fact := { retained with handle := 8 }

/-- Different summaries can still share a useful factor and ready coordinates. -/
def shared (_ : Nat) (success : Bool) : Summary :=
  ⟨none, if success then [retained, other] else [retained], [],
    if success then [0, 1, 2] else [0, 1]⟩

example : Zkc.Compiler.FactorMerge.facts (shared 0) [] = [retained] := by decide
example : Zkc.Compiler.FactorMerge.available (shared 0) [] = [0, 1] := by decide

def fixture : World Nat :=
  ⟨⟨fun _ values => values.sum, fun _ tail => 2 + tail.sum,
    fun i => if i = 0 then 2 else 3⟩, [0, 1, 2]⟩

def invariant (state : World Nat) : Prop :=
  Valid state.values [retained, other] ∧ Known state [0, 1, 2]

theorem fixture_valid : invariant fixture := by
  constructor
  · intro fact member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;>
      simp [Means, retained, other, Tests.FactorOptimization.retained, fixture]
  · decide

def implement (success : Bool) (_ : Nat) (state : World Nat) : Returned Nat Bool :=
  ⟨success, state, [success]⟩

theorem laws (success : Bool) :
    Zkc.Compiler.FactorOptimization.Laws invariant shared (implement success) where
  summary name state initial := by
    constructor
    · trivial
    · cases success with
      | true => exact initial.1
      | false =>
          intro fact member
          have same : fact = retained := by simpa [shared, implement] using member
          exact initial.1 fact (by simp [same])
    · simp [Known, keptKnown, shared]
    · cases success with
      | true => exact initial.2
      | false =>
          intro i member
          apply initial.2 i
          simpa [shared, implement] using List.mem_append_left [2] member
  preserves _ _ initial := initial

def source : Program language [.scalar] .scalar :=
  .letOp (.external 0) .nil
    (.branch .here (.letOp (.evaluate query) .nil (.ret .here)) (.ret (.there .here)))

/-- Construct the candidate independently, retaining the original Boolean branch. -/
def expected : RawProgram Ty PlannedOperation :=
  .letOp (.external 0) []
    (.branch 0 (.letOp (.evaluate query (.reuse retained [1])) [] (.ret 0)) (.ret 1))

def checkedRule (success : Bool) :=
  Zkc.Compiler.FactorOptimization.Conservative.rule invariant shared (implement success)
    (laws success) [.scalar] .scalar

example : (checkTransformation (checkedRule true) source () expected).isSome = true := by decide
example : (checkTransformation (checkedRule false) source () expected).isSome = true := by decide
example : (checkTransformation (checkedRule true) source () (.ret 0)).isSome = false := by decide
example : (checkTransformation (checkedRule true) (.stop .abort) () expected).isSome = false := by decide

def run (success : Bool) : PIR.Execution (World Nat) Bool Nat :=
  ((Zkc.Compiler.FactorOptimization.Conservative.rewrite shared [] [] source).denote
    plannedMeaning (Values.cons (99 : Nat) Values.nil).get).run
    (Zkc.Compiler.FactorOptimization.handler (implement success)) fixture

theorem execution (success : Bool) : run success =
    (source.denote meaning (Values.cons (99 : Nat) Values.nil).get).run
      (Zkc.Compiler.FactorOptimization.handler (implement success)) fixture :=
  Zkc.Compiler.FactorOptimization.Conservative.execution invariant shared (implement success)
    (laws success) source _ fixture [] [] (by simp [Valid]) (by simp [Known]) fixture_valid

example : (run true).outcome = .returned 5 := by decide
example : (run false).outcome = .returned 99 := by decide
example : (run false).events = [false] := by decide

/-- Retaining a fact from just one outcome is unsound in general. -/
def invalid : State Nat := ⟨fun _ _ => 0, fun _ _ => 1, fun _ => 0⟩

example : Valid invalid ([] : List Fact) := by simp [Valid]
example : ¬ Valid invalid [retained] := by
  intro valid
  have contradiction := valid retained (by simp) [0] rfl
  exact Nat.noConfusion contradiction

def asymmetric (_ : Nat) (success : Bool) : Summary :=
  ⟨none, if success then [retained] else [], [], []⟩

example : Zkc.Compiler.FactorMerge.facts (asymmetric 0) [] = [] := by decide
example : Zkc.Compiler.FactorMerge.available (fun _ => ⟨none, [], [], []⟩) [0] = [] := by decide

/-- The actual polynomial preparation contract exports only on success. The
conservative rule therefore declines its reuse, while preserving computation. -/
def polynomialExpected : RawProgram Ty PlannedOperation :=
  .letOp (.external 0) [] (.letOp (.external 1) [] (.letOp (.external 2) []
    (Tests.FactorOptimization.expectedLeaf .direct)))

example : (lower (Zkc.Compiler.FactorOptimization.Conservative.rewrite
    (Tests.FactorOptimization.summaries (2 : ZMod 7) 3) [] []
    Tests.FactorOptimization.source)).erase = polynomialExpected := by decide

def runPolynomial (program : Program language [.scalar] .boolean) :
    PIR.Execution (World (ZMod 7)) (Zkc.Modules.PolynomialPreparation.Event (ZMod 7)) Bool :=
  ((Zkc.Compiler.FactorOptimization.Conservative.rewrite
    (Tests.FactorOptimization.summaries (2 : ZMod 7) 3) [] [] program).denote plannedMeaning
    (Tests.FactorOptimization.inputs (3 : ZMod 7)).get).run
    (Zkc.Compiler.FactorOptimization.handler (Tests.FactorOptimization.implement (2 : ZMod 7) 3))
    Tests.FactorOptimization.initial

example : (runPolynomial Tests.FactorOptimization.source).outcome = .returned true := by decide
example : (runPolynomial Tests.FactorOptimization.changedSource).outcome = .returned true := by decide
example : (runPolynomial Tests.FactorOptimization.changedSource).state.values.view 7 [3] = 1 := by decide
example : (runPolynomial Tests.FactorOptimization.changedSource).events =
    [.assigned 0 2, .prepared 7, .assigned 1 3, .overwritten 7 false] := by decide
example : (runPolynomial Tests.FactorOptimization.premature).outcome = .stopped .refused := by decide
example : (runPolynomial Tests.FactorOptimization.premature).events = [.assigned 0 2, .prepared 7] := by decide
example : (runPolynomial Tests.FactorOptimization.premature).state.known = [0] := by decide

def loop : Program language [.scalar] .scalar :=
  .iterate 3 .here (.letOp (.evaluate query) .nil (.ret .here))
    (.letOp (.evaluate query) .nil (.ret .here))

example : (Zkc.Compiler.FactorOptimization.Conservative.rewrite shared [retained] [0, 1] loop).erase =
    .iterate 3 .scalar 0 (.letOp (.evaluate query .direct) [] (.ret 0))
      (.letOp (.evaluate query .direct) [] (.ret 0)) := by decide

def chain {Γ : List Ty} : Nat → Program language Γ .boolean
  | 0 => .stop .abort
  | n + 1 => .letOp (.external 0) .nil (chain n)

theorem chain_nodeCount {Γ : List Ty} (n : Nat) : (chain (Γ := Γ) n).erase.nodeCount = n + 1 := by
  induction n generalizing Γ with
  | zero => rfl
  | succ n ih =>
      simp only [chain, Program.erase, RawProgram.nodeCount]
      rw [ih]
      omega

theorem candidate_chain_nodeCount (n : Nat) :
    (lower (Zkc.Compiler.FactorOptimization.Conservative.rewrite asymmetric [] []
      (chain (Γ := []) n))).erase.nodeCount = n + 1 :=
  (Zkc.Compiler.FactorOptimization.Conservative.candidate_nodeCount _ _).trans (chain_nodeCount n)

example : [0, 1, 2, 8, 20, 64].map (fun n =>
    (lower (Zkc.Compiler.FactorOptimization.Conservative.rewrite asymmetric [] []
      (chain (Γ := []) n))).erase.nodeCount) = [1, 2, 3, 9, 21, 65] := by decide

example : [0, 1, 2, 8].map (fun n =>
    (lower (Zkc.Compiler.FactorOptimization.rewrite asymmetric [] []
      (chain (Γ := []) n))).erase.nodeCount) = [1, 4, 10, 766] := by decide

end Tests.FactorMerge
