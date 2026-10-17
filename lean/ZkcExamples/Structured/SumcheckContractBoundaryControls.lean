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

set_option smartUnfolding false

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

/-- The call-boundary bound's source-relation premise is satisfiable: a false
public claim refutes the retained relation at the actual child boundary. -/
theorem child_refutation_inhabited
    (environment : RelationEnvironment SumcheckSourceViews.imported SumcheckContractControls.F SumcheckContractControls.F) :
    (childRefutation (G := SumcheckContractControls.F) (sourceEnvironment := environment)
      ([0, 0, 0, 0] : List SumcheckContractControls.F) 1 2 0 (.stopped .incomplete)).Proof := by
  have translation := public_translation (G := SumcheckContractControls.F) (sourceEnvironment := environment)
    ([0, 0, 0, 0] : List SumcheckContractControls.F) 1 2 0 (.stopped .incomplete) (by decide)
  refine child_refutation _ _ _ _ _ ?_ translation
  intro holds
  have equal : (1 : SumcheckContractControls.F) = ([0, 0, 0, 0] : List SumcheckContractControls.F).sum :=
    ((publicUse (G := SumcheckContractControls.F) (sourceEnvironment := environment)
      ([0, 0, 0, 0] : List SumcheckContractControls.F) 1 2 0 (.stopped .incomplete)).equivalence
        translation).mp holds
  exact absurd equal (by decide)

/-- The reduction request's refutation premise is satisfiable at the actual
Reduce input clause, with the formula law and its capacity domain. -/
theorem reduction_refutation_inhabited
    (environment : RelationEnvironment SumcheckReduceViews.imported SumcheckContractControls.F SumcheckContractControls.F) :
    (reductionRefutation (G := SumcheckContractControls.F) (reductionEnvironment := environment)
      ([0, 0, 0, 0] : List SumcheckContractControls.F) 2 1 2 0).Meaning := by
  have translation : (reductionUse (G := SumcheckContractControls.F) (reductionEnvironment := environment)
      ([0, 0, 0, 0] : List SumcheckContractControls.F) 2 1 2 0 (.stopped .incomplete)).Translation :=
    ⟨reduction_formula_law,
      show ([0, 0, 0, 0] : List SumcheckContractControls.F).length < indexLimit by decide⟩
  intro holds
  have equal : (1 : SumcheckContractControls.F) = ([0, 0, 0, 0] : List SumcheckContractControls.F).sum :=
    ((reductionUse (G := SumcheckContractControls.F) (reductionEnvironment := environment)
      ([0, 0, 0, 0] : List SumcheckContractControls.F) 2 1 2 0 (.stopped .incomplete)).equivalence
        translation).mp holds
  exact absurd equal (by decide)

end ZkcExamples.Structured.SumcheckContractBoundaryControls
