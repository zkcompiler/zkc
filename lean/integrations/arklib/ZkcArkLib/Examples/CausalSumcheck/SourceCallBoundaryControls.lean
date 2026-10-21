module

public import ZkcArkLib.Examples.CausalSumcheck.SourceContracts
public import ZkcExamples.Structured.SumcheckCallBoundaryControls
public import Mathlib.Algebra.Field.ZMod

@[expose] public section

/-! A replacement child uses the same caller theorem solely through its typed
residual bound. Its deliberately malformed return cannot arise from the old
successful one-round normal form, so the test detects reliance on that form. -/
namespace ZkcSecurity.Examples.CausalSumcheck.SourceCallBoundaryControls
open Zkc.Source Zkc.Source.Structured ZkcExamples.Structured
open ZkcSecurity.VCVio.Execution
open SumcheckCallBoundaryControls
open scoped ENNReal

set_option smartUnfolding false

local instance primeFive : Fact (Nat.Prime 5) := ⟨by decide⟩

variable {S E : Type}

def replacement : PIR.Proc (participantInterface F F)
    (Values (Component (assignment F F)) SumcheckVerifierBodies.reduceOutputs) :=
  .done (outputs (some []) (some 0))

theorem replacement_request_false :
    ¬ SourceVerifier.childResidualRequest [0, 0] (1 : F) 1 0 (outputs (some []) (some 0)) := by
  intro holds
  have residual := (SumcheckCallBoundary.child_request_iff [0, 0] (1 : F) 1 0 table decoded
    (outputs (some []) (some 0))).mp holds
  change SumcheckContractBindings.Residual 0 1 table [] 0 at residual
  rcases residual with ⟨point, length, _⟩
  have impossible := congrArg List.length length
  simp at impossible

theorem replacement_interface
    (handler : PIR.MonadHandler ProbComp (participantInterface F F) S E) (state : S) :
    mass (acceptance handler replacement state
      (SourceVerifier.childResidualRequest [0, 0] (1 : F) 1 0)) ≤ 0 := by
  simp [replacement, acceptance, PIR.Proc.runM, returnedSatisfies, replacement_request_false]

/-- A correct V result discharges the typed request even with these arbitrary
foreign slots; the actual terminal theorem supplies the implication. -/
theorem positive_request
    (handler : PIR.MonadHandler ProbComp (participantInterface F F) S E) (state : S) :
    SourceVerifier.childResidualRequest [0, 0] (1 : F) 1 0 (outputs (some [0]) (some 0)) := by
  apply SourceVerifier.terminal_implies_request handler 1 [0, 0] table decoded (by decide) 1 0
    (outputs (some [0]) (some 0)) state
    ⟨.returned (.cons (some true) .nil), state, []⟩
  · rw [correct_terminal]
    simp [PIR.Proc.runM]
  · rfl

/-- The caller proof is unchanged and invokes no theorem about Reduce's body. -/
theorem replacement_caller_bound
    (handler : PIR.MonadHandler ProbComp (participantInterface F F) S E) (state : S) :
    mass (acceptance handler (replacement.bind (SumcheckCallBoundary.terminal [0, 0])) state
      (fun output => output.get .here = some true)) ≤ 0 :=
  SourceVerifier.caller_bound_of_child handler 1 [0, 0] table decoded (by decide) 1 0
    replacement state 0 (replacement_interface handler state)

end ZkcSecurity.Examples.CausalSumcheck.SourceCallBoundaryControls
