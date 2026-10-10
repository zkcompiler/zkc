import Zkc.Compiler.PolynomialPreparation
import Mathlib.Data.ZMod.Basic

/-! Actual checked field computation, residual preparation and terminal use.
The expected candidate is constructed independently of the optimization pass.
-/

set_option autoImplicit false

namespace Tests.FactorOptimization

open Zkc.Source Zkc.Compiler Zkc.Polynomial
open Zkc.Source.FactorQueries Zkc.Modules.Factor
open Zkc.Modules.FactorState Zkc.Modules.PolynomialPreparation

def binding {F : Type} [CommSemiring F] : Binding F 2 where
  key := ⟨100, [11, 12]⟩
  size := rfl
  distinct := by decide
  polynomial := .node
    (.node (.constant 1) (.constant 3) (.constant 0))
    (.node (.constant 2) (.constant 4) (.constant 0))
    (.node (.constant 0) (.constant 0) (.constant 0))

theorem polynomial_meaning {F : Type} [CommSemiring F] (x y : F) :
    (binding (F := F)).polynomial.eval ![x, y] = 1 + 2 * x + 3 * y + 4 * x * y := by
  simp [binding, Quadratic.eval, Function.comp_def]
  ring

def request : Request 1 := ⟨7, [0], rfl⟩
def query : Query := ⟨⟨100, [11, 12]⟩, [0, 1]⟩
def retained : Fact := ⟨⟨100, [11, 12]⟩, 7, [0], 1⟩

def calls {F : Type} [CommSemiring F] (x y : F) : Nat → Call F 1
  | 0 => .assign 0 x
  | 1 => .prepare request
  | 2 => .assign 1 y
  | 3 => .overwrite 7 (fun _ => 99) false
  | _ => .assign 0 (x + 1)

def initial {F : Type} [CommSemiring F] : World F :=
  bind binding ⟨⟨fun _ _ => 0, fun _ _ => 99, fun _ => 0⟩, []⟩

def raw : RawProgram Ty Operation :=
  .letOp (.external 0) [] (.letOp (.external 1) [] (.letOp (.external 2) []
    (.letOp (.evaluate query) [] (.letOp .equal [0, 4]
      (.branch 0 (.ret 0) (.stop .reject))))))

def source : Program language [.scalar] .boolean :=
  (raw.elaborate (language := language) [.scalar] .boolean).toOption.get (by decide)

def expectedLeaf (plan : Zkc.Modules.Factor.Plan) : RawProgram Ty PlannedOperation :=
  .letOp (.evaluate query plan) [] (.letOp .equal [0, 4]
    (.branch 0 (.ret 0) (.stop .reject)))

def expected : RawProgram Ty PlannedOperation :=
  .letOp (.external 0) [] (.letOp (.external 1) [] (.branch 0
    (.letOp (.external 2) [] (expectedLeaf (.reuse retained [1])))
    (.letOp (.external 2) [] (expectedLeaf .direct))))

def summaries {F : Type} [CommSemiring F] (x y : F) :=
  fun name => summary (n := 1) binding (calls x y name)

def implement {F : Type} [CommSemiring F] (x y : F) :=
  fun name => execute (n := 1) binding (calls x y name)

def checkedRule {F : Type} [CommSemiring F] [DecidableEq F] (x y : F) :=
  FactorOptimization.rule (Bound binding) (summaries x y) (implement x y)
    (Zkc.Compiler.PolynomialPreparation.laws (n := 1) binding (calls x y)) [.scalar] .boolean

example : (checkTransformation (checkedRule (2 : ZMod 7) 3) source () expected).isSome = true := by
  decide

example : (checkTransformation (checkedRule (4 : ZMod 5) 1) source () expected).isSome = true := by
  decide

example : (lower (FactorOptimization.rewrite (summaries (2 : ZMod 7) 3) [] [] source)).erase =
    expected := by decide

def inputs {F : Type} (claim : F) : Values (Value F) [.scalar] := .cons claim .nil

def runSource {F : Type} [CommSemiring F] [DecidableEq F] (x y claim : F) : PIR.Execution (World F) (Event F) Bool :=
  (source.denote meaning (inputs claim).get).run (FactorOptimization.handler (implement x y)) initial

def runTarget {F : Type} [CommSemiring F] [DecidableEq F] (x y claim : F) : PIR.Execution (World F) (Event F) Bool :=
  ((FactorOptimization.rewrite (summaries x y) [] [] source).denote plannedMeaning
    (inputs claim).get).run (FactorOptimization.handler (implement x y)) initial

/-- All field bindings and claims, including rejection, share complete execution. -/
theorem actual_execution {F : Type} [CommSemiring F] [DecidableEq F] (x y claim : F) :
    runTarget x y claim = runSource x y claim :=
  FactorOptimization.execution (Bound binding) _ _ (Zkc.Compiler.PolynomialPreparation.laws (n := 1) binding (calls x y))
    source _ initial [] [] (by simp [Valid]) (by simp [Known]) (bind_bound binding _)

example : (runTarget (2 : ZMod 7) 3 3).outcome = .returned true := by decide
example : (runTarget (2 : ZMod 7) 3 4).outcome = .stopped .reject := by decide
example : (runTarget (2 : ZMod 7) 3 3).events =
    [.assigned 0 2, .prepared 7, .assigned 1 3] := by decide

/-- The stored residual answers a later point that was not used to prepare it. -/
example : (runTarget (2 : ZMod 7) 3 3).state.values.view 7 [5] = 4 := by decide

def changedRaw : RawProgram Ty Operation :=
  .letOp (.external 0) [] (.letOp (.external 1) [] (.letOp (.external 2) []
    (.letOp (.external 3) [] (.letOp (.evaluate query) []
      (.letOp .equal [0, 5] (.branch 0 (.ret 0) (.stop .reject)))))))

def changedSource : Program language [.scalar] .boolean :=
  (changedRaw.elaborate (language := language) [.scalar] .boolean).toOption.get (by decide)

def runChanged : PIR.Execution (World (ZMod 7)) (Event (ZMod 7)) Bool :=
  ((FactorOptimization.rewrite (summaries (2 : ZMod 7) 3) [] [] changedSource).denote plannedMeaning
    (inputs (3 : ZMod 7)).get).run (FactorOptimization.handler (implement (2 : ZMod 7) 3)) initial

/-- Failed overwrite invalidates the cached fact and retains the changed storage. -/
example : runChanged.outcome = .returned true := by decide
example : runChanged.state.values.view 7 [3] = 1 := by decide
example : runChanged.events =
    [.assigned 0 2, .prepared 7, .assigned 1 3, .overwritten 7 false] := by decide

example : nextFacts (summary (n := 1) (binding (F := ZMod 7)) (calls 2 3 3) false)
    [retained] = [] := by decide

/-- An old candidate cannot be applied to a source with an intervening mutation. -/
example : (checkTransformation (checkedRule (2 : ZMod 7) 3) changedSource () expected).isSome = false := by
  decide

example : check [retained] [0, 1] ⟨⟨100, [12, 11]⟩, [0, 1]⟩ (.reuse retained [1]) = false := by
  decide
example : check [retained] [0, 1] query (.reuse retained [0]) = false := by decide
example : check [retained] [0] query (.reuse retained [1]) = false := by decide

/-- Preparation before its fixed coordinate is available fails without export. -/
example : (execute (n := 1) binding (.prepare request) (initial (F := ZMod 7))).success = false := by
  decide

def prematureRaw : RawProgram Ty Operation :=
  .letOp (.external 0) [] (.letOp (.external 1) []
    (.letOp (.evaluate query) [] (.letOp (.external 2) [] (.stop .abort))))

def premature : Program language [.scalar] .boolean :=
  (prematureRaw.elaborate (language := language) [.scalar] .boolean).toOption.get (by decide)

def runPremature : PIR.Execution (World (ZMod 7)) (Event (ZMod 7)) Bool :=
  ((FactorOptimization.rewrite (summaries (2 : ZMod 7) 3) [] [] premature).denote plannedMeaning
    (inputs (3 : ZMod 7)).get).run (FactorOptimization.handler (implement (2 : ZMod 7) 3)) initial

example : runPremature.outcome = .stopped .refused := by decide
example : runPremature.events = [.assigned 0 2, .prepared 7] := by decide
example : runPremature.state.known = [0] := by decide

end Tests.FactorOptimization
