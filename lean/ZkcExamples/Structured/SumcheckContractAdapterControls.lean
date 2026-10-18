module

public import ZkcExamples.Structured.SumcheckContractBoundaryControls
public import ZkcExamples.Structured.SumcheckReductionRequests

@[expose] public section

/-! Counterexamples on the assembled residual wrapper adapter. The actual
zero-round source return is available, but its fixed-table terminal is false.
Changing the fixed table or omitting the terminal changes the property. -/
namespace ZkcExamples.Structured.SumcheckContractAdapterControls
open Zkc.Source Zkc.Source.Structured
open Zkc.Polynomial.Multilinear Zkc.Protocols.Sumcheck.Multilinear
open SumcheckContractBindings SumcheckContractRequests

abbrev F := ZMod 5

set_option smartUnfolding false

private theorem decode_singleton (value : F) :
    ofList? 0 [value] = some (fun _ => value) := by
  simp [ofList?]
  rfl

def input : ComponentInput reductionRoot F F := reductionRootInput none none 1 0 0

def outputs : Values (Component (assignment F F)) reductionRoot.protocol.outputs :=
  SumcheckReduceVerifier.reduceRootResults (some [], some 1)

/-- The boundary used in these controls is an actual returned source outcome. -/
theorem actual_zero_return : input.process.interpret forgetSites = .done outputs :=
  SumcheckReduceVerifier.verifier_zero _ _ _ _

theorem fixed_table_rejects :
    ¬ (wrapperTerminal [0] 0 0).Holds {} (input.boundary (.returned outputs))
      (wrapperAssignments (G := F)) := by
  intro holds
  have residual := (wrapper_terminal_iff [0] 0 0 (fun _ => (0 : F))
    (decode_singleton 0) none none 1 0 outputs).mp holds
  exact SumcheckContractStops.zero_residual_is_false residual

theorem changed_table_accepts :
    (wrapperTerminal [1] 0 0).Holds {} (input.boundary (.returned outputs))
      (wrapperAssignments (G := F)) := by
  apply (wrapper_terminal_iff [1] 0 0 (fun _ => (1 : F))
    (decode_singleton 1) none none 1 0 outputs).mpr
  change Residual 0 0 (fun _ => (1 : F)) [] 1
  refine ⟨Fin.elim0, rfl, ?_⟩
  rw [residualClaim_complete_iff]
  rfl

/-- Successful return without the typed terminal cannot discharge the actual
fixed-table wrapper request, even at the zero-round source outcome. -/
theorem omitted_terminal_cannot_close :
    ¬ (∀ outcome,
      input.returnedEvent (fun _ => True) outcome →
      input.returnedEvent (fun boundary =>
        (wrapperTerminal [0] 0 0).Holds {} boundary (wrapperAssignments (G := F))) outcome) := by
  intro close
  exact fixed_table_rejects (close (.returned outputs) trivial)

end ZkcExamples.Structured.SumcheckContractAdapterControls
