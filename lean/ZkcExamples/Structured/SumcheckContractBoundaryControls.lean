module

public import ZkcExamples.Structured.SumcheckContractRequests
public import ZkcExamples.Structured.SumcheckContractControls
public import ZkcExamples.Structured.SumcheckContractStops

@[expose] public section

/-! Negative controls at the actual request boundaries. They supplement the
finite wrong-table/residual-omission controls and actual count/stop equations. -/
namespace ZkcExamples.Structured.SumcheckContractBoundaryControls
open Zkc.Source Zkc.Source.Structured
open SumcheckRelationContract SumcheckContractBindings SumcheckContractRequests
open SumcheckContractInstantiation
open Zkc.Polynomial.Multilinear

set_option backward.isDefEq.respectTransparency false
set_option smartUnfolding false
set_option maxRecDepth 20000

variable {F G : Type}

def proverPublicTable : BoundarySelector publicOwner.protocol.signature vector :=
  ⟨.input .here, ⟨0, by decide⟩, by decide⟩

theorem prover_table_absent (raw : List F) (claim : F) (count handle : Nat) (outcome) :
    proverPublicTable.read {} ((publicInput (G := G) raw claim count handle).boundary outcome) = none := rfl

theorem wrong_table_read (raw other : List F) (different : raw ≠ other)
    (claim : F) (count handle : Nat) (outcome) :
    publicTable.read {} ((publicInput (G := G) raw claim count handle).boundary outcome) ≠ some other := by
  rw [public_table_read]
  exact fun equality => different (Option.some.inj equality)

theorem wrong_assignment_disagrees (raw other : List F) (different : raw ≠ other)
    (claim : F) (count handle : Nat) (outcome) :
    ¬ publicApplication.Agrees {} ((publicInput (G := G) raw claim count handle).boundary outcome)
      (fixedPublic (invocation := rootInvocation) other) := by
  intro agreement
  have equal := congrArg (fun values => values.get .here) agreement
  change some other = some raw at equal
  exact different (Option.some.inj equal).symm

variable [CommRing F]

/-- A stopped callee cannot discharge this request, even though its fixed table
and input claim remain available. There is no fabricated returned tuple. -/
theorem stopped_child_terminal (raw : List F) (claim : F) (count handle : Nat)
    (table : Table F (0 + count)) (decoded : ofList? (0 + count) raw = some table)
    (reason : PIR.Stop) :
    ¬ (childTerminal (G := G) 0 count).Holds SumcheckSourceVerifier.childContext
      (childBoundary raw claim count handle (.stopped reason))
      (childAssignments raw claim count handle) := by
  intro holds
  have selected := (residual_terminal_iff (.parameter childTable) 0 count childPoint childValue rfl rfl
    SumcheckSourceVerifier.childContext (childBoundary raw claim count handle (.stopped reason))
    (childAssignments raw claim count handle) raw rfl table decoded).mp holds
  rcases selected with ⟨point, value, pointRead, _, _⟩
  have absent := publicReductionCall.boundaryOfOutcome_stopped_output {} 1
    (publicCallEnvironment (G := G) raw claim count handle) reason childPoint
    (.there (.there (.there (.there .here)))) rfl
  have contradiction := absent.symm.trans pointRead
  cases contradiction

end ZkcExamples.Structured.SumcheckContractBoundaryControls
