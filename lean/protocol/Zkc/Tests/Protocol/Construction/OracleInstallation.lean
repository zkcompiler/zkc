module

public import Zkc.Tests.Protocol.Construction.StatefulOracle

/-! A non-injective private-state representation for the complete oracle source.
Only the audit counter is erased. Store contents, outcomes and the ordered observation
history are retained, including the histories of failed operations.
-/

@[expose] public section
noncomputable section
open PIR ProtocolProof MeasureTheory ProbabilityTheory
open ProtocolProofExamples.StatefulOracle

namespace ProtocolProofExamples.OracleInstallation

abbrev ConcreteStore := Store × Nat

def project (current : ConcreteStore × List Event) : Store × List Event :=
  (current.1.1, current.2)

def operations (op : Service.Op) : Kernel ConcreteStore (Execution ConcreteStore Event Nat) :=
  ⟨fun current => (StatefulOracle.operations op current.1).map
      (fun out => ⟨out.outcome, (out.state, current.2 + 1), out.events⟩),
    measurable_of_countable _⟩

def actual : System Configuration Service ConcreteStore Event where
  operations _ := operations
  initial _ := Measure.dirac ([], 0)
  operation_mass e op current := by
    change ((StatefulOracle.operations op current.1).map
      (fun out => (⟨out.outcome, (out.state, current.2 + 1), out.events⟩ :
        Execution ConcreteStore Event Nat))) Set.univ = 1
    rw [Measure.map_apply (measurable_of_countable _) MeasurableSet.univ]
    exact StatefulOracle.system.operation_mass e op current.1
  initial_probability _ := inferInstance

/-- Every operation satisfies the same total representation, not only the successful reads. -/
theorem operation_map (e : Configuration) (op : Service.Op)
    (current : ConcreteStore × List Event) :
    (actual.accumulatedOperations e op current).map (fun out => (out.1, project out.2)) =
      StatefulOracle.system.accumulatedOperations e op (project current) := by
  rw [actual.accumulatedOperations_apply, StatefulOracle.system.accumulatedOperations_apply]
  change (((StatefulOracle.operations op current.1.1).map _).map _).map _ = _
  rw [Measure.map_map (measurable_of_countable _) (measurable_of_countable _),
    Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  rfl

def installation (admissible : Configuration → Prop) :
    Installation actual StatefulOracle.system admissible (fun _ s t => project s = t) :=
  Installation.ofMap actual StatefulOracle.system admissible (fun _ => project)
    (fun _ => measurable_of_countable _) (fun e _ => operation_map e)
    (by intro e _; simp [System.initialWithEvents, actual, StatefulOracle.system, project])

def accepting : Set (Execution ConcreteStore Event Bool) :=
  {out | out.outcome = .returned true}

def upperRequest : UpperRequest Configuration (Execution ConcreteStore Event Bool) where
  experiment := actual.experiment game
  admissible _ := True
  event := accepting
  measurable_event := MeasurableSet.of_discrete
  bound := acceptance

def lowerRequest : LowerRequest Configuration (Execution ConcreteStore Event Bool) where
  experiment := actual.experiment game
  admissible _ := True
  event := accepting
  measurable_event := MeasurableSet.of_discrete
  bound := acceptance

def upperEvidence :
    UpperEvidence upperRequest actual StatefulOracle.system game (fun _ s t => project s = t) where
  subject := rfl
  installation := installation _
  spec _ := spec
  local_bound e _ op post state := (operation_expectation e op post state).le
  model_event _ := StatefulOracle.accepting
  measurable_event _ := MeasurableSet.of_discrete
  terminal _ _ _ _ _ _ h := h
  potential e _ := acceptance e
  mathematics e _ := complete_upper e
  budget _ _ := by simp [System.initialWithEvents, StatefulOracle.system, upperRequest]

def lowerEvidence :
    LowerEvidence lowerRequest actual StatefulOracle.system game (fun _ s t => project s = t) where
  subject := rfl
  installation := installation _
  spec _ := spec
  local_bound e _ op post state := (operation_expectation e op post state).ge
  model_event _ := StatefulOracle.accepting
  measurable_event _ := MeasurableSet.of_discrete
  terminal _ _ _ _ _ _ h := h
  potential e _ := acceptance e
  mathematics e _ := complete_lower e
  budget _ _ := by simp [System.initialWithEvents, StatefulOracle.system, lowerRequest]

theorem complete_acceptance (e : Configuration) :
    (actual.experiment game).run e accepting = acceptance e :=
  le_antisymm (upperEvidence.establish e trivial) (lowerEvidence.establish e trivial)

theorem representation_noninjective : ¬ Function.Injective project := by
  intro injective
  have impossible := injective (a₁ := (([], 0), [])) (a₂ := (([], 1), [])) rfl
  cases impossible

/-- Erasing observable history is not an interchangeable representation. -/
theorem history_is_not_optional :
    project (([], 0), [(2, 0, 0)]) ≠ project (([], 1), []) := by
  simp [project]

end ProtocolProofExamples.OracleInstallation
