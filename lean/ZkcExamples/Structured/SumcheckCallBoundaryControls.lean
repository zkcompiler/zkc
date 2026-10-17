module

public import ZkcExamples.Structured.SumcheckCallBoundary
public import Mathlib.Data.ZMod.Basic

@[expose] public section

/-! Actual caller controls on arbitrary six-slot returns, including foreign
slots that no honest child execution is required to produce. -/
namespace ZkcExamples.Structured.SumcheckCallBoundaryControls
open Zkc.Source Zkc.Source.Structured
open Zkc.Polynomial Zkc.Polynomial.Multilinear
open SumcheckCallBoundary

abbrev F := ZMod 5

set_option backward.isDefEq.respectTransparency false
set_option smartUnfolding false
set_option maxRecDepth 20000

/-- Deliberately arbitrary foreign slots; only the last two are V's outputs. -/
def outputs (point : Option (List F)) (value : Option F) :
    Values (Component (assignment F F)) SumcheckVerifierBodies.reduceOutputs :=
  .cons (some [4, 3, 2]) (.cons (some [1, 4]) (.cons (some 7)
    (.cons (some 4) (.cons point (.cons value .nil)))))

def table : Table F 1 := ofVector (fun _ : Fin 2 => 0)

theorem decoded : ofList? 1 [0, 0] = some table := by
  exact ofList?_ofFn (n := 1) (fun _ : Fin 2 => (0 : F))

theorem missing_point : terminal [0, 0] (outputs none (some 0)) = .halt .incomplete := by
  exact SumcheckVerifierTerminal.terminal_optional _ _ _ _ _

theorem missing_value : terminal [0, 0] (outputs (some [0]) none) = .halt .incomplete := by
  exact SumcheckVerifierTerminal.terminal_optional _ _ _ _ _

theorem malformed_short : terminal [0, 0] (outputs (some []) (some 0)) =
    .done (.cons (some false) .nil) := by
  change SumcheckVerifierTerminal.actualOwnedCheck (G := F) SumcheckSourceViews.unit 1
    (some [0, 0]) (some []) (some 0) = _
  rw [SumcheckVerifierTerminal.terminal_malformed 1 [0, 0] [] 0
    (by decide) (by decide) (by decide)]

theorem malformed_long : terminal [0, 0] (outputs (some [0, 0]) (some 0)) =
    .done (.cons (some false) .nil) := by
  change SumcheckVerifierTerminal.actualOwnedCheck (G := F) SumcheckSourceViews.unit 1
    (some [0, 0]) (some [0, 0]) (some 0) = _
  rw [SumcheckVerifierTerminal.terminal_malformed 1 [0, 0] [0, 0] 0
    (by decide) (by decide) (by decide)]

theorem correct_terminal : terminal [0, 0] (outputs (some [0]) (some 0)) =
    .done (.cons (some true) .nil) := by
  change SumcheckVerifierTerminal.actualOwnedCheck (G := F) SumcheckSourceViews.unit 1
    (some [0, 0]) (some [0]) (some 0) = _
  rw [SumcheckVerifierTerminal.terminal_equation 1 [0, 0] [0] 0 (by decide) (by decide)]
  congr 3

theorem wrong_value : terminal [0, 0] (outputs (some [0]) (some 1)) =
    .done (.cons (some false) .nil) := by
  change SumcheckVerifierTerminal.actualOwnedCheck (G := F) SumcheckSourceViews.unit 1
    (some [0, 0]) (some [0]) (some 1) = _
  rw [SumcheckVerifierTerminal.terminal_equation 1 [0, 0] [0] 1 (by decide) (by decide)]
  congr 3

/-- Changing the fixed public table changes the actual terminal on this same
arbitrary return, despite every foreign slot remaining identical. -/
theorem changed_table : terminal [1, 0] (outputs (some [0]) (some 1)) =
    .done (.cons (some true) .nil) := by
  change SumcheckVerifierTerminal.actualOwnedCheck (G := F) SumcheckSourceViews.unit 1
    (some [1, 0]) (some [0]) (some 1) = _
  rw [SumcheckVerifierTerminal.terminal_equation 1 [1, 0] [0] 1 (by decide) (by decide)]
  congr 3

/-- This guard is quantified instead of allocating a list of indexLimit size. -/
theorem exhausted_point (point : List F) (large : ¬ point.length < indexLimit) :
    terminal [0, 0] (outputs (some point) (some 0)) = .halt .exhausted := by
  change SumcheckVerifierTerminal.actualOwnedCheck (G := F) SumcheckSourceViews.unit 1
    (some [0, 0]) (some point) (some 0) = _
  rw [SumcheckVerifierTerminal.terminal_decision, ite_eq_right large]

/-- A stopped replacement child never reaches the actual terminal. -/
theorem stopped_child (reason : PIR.Stop) :
    (PIR.Proc.halt reason).bind (terminal (F := F) (G := F) [0, 0]) = .halt reason := rfl

end ZkcExamples.Structured.SumcheckCallBoundaryControls
