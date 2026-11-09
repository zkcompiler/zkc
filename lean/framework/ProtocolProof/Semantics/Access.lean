module

public import ProtocolProof.Semantics.System
public import PolyFun.PFunctor.Free.WP.Charge

/-!
# Request-fixed access and weighted abstract-call bounds

The algorithm sees only its public input and the answers of its typed interface. The
environment, which may contain an adversary implementation, reaches it through the fixed
handler. The resource reading bounds the weights of abstract calls over all possible answers.
Pure computation is uncharged: this is not a time-complexity or polynomial-time certificate.
-/

public section

open PFunctor MeasureTheory
open scoped ENNReal

namespace ProtocolProof

universe uP uE uA uB uS uR

section Execution

variable (Public : Type uP) (Environment : Type uE) (Interface : PFunctor.{uA, uB})
  (State : Type uS) (Result : Type uR)
  [∀ op, MeasurableSpace (Interface.B op)] [MeasurableSpace State]

/-- An algorithm and its allowed services are fixed before any security evidence. -/
structure AccessExecution where
  system : System Environment Interface State
  publicInput : Environment → Public
  algorithm : Public → FreeM Interface Result

variable {Public Environment Interface State Result}

/-- Interpret the selected algorithm with exactly the request's services and initial law. -/
@[expose] noncomputable def AccessExecution.experiment
    [∀ op, Countable (Interface.B op)] [∀ op, MeasurableSingletonClass (Interface.B op)]
    [MeasurableSpace Result]
    (execution : AccessExecution Public Environment Interface State Result) :
    Experiment Environment (Result × State) :=
  execution.system.experiment (fun environment ↦
    execution.algorithm (execution.publicInput environment))

end Execution

variable {Interface : PFunctor.{uA, uB}} {Result : Type uR}

/-- A request-owned weight for each permitted abstract operation, not a host-runtime model. -/
structure OperationCost (Interface : PFunctor.{uA, uB}) where
  weight : Interface.A → ℝ≥0∞

namespace OperationCost

/-- Count every abstract call once. -/
@[expose] def calls (Interface : PFunctor.{uA, uB}) : OperationCost Interface := ⟨fun _ ↦ 1⟩

/-- A structural bound on the selected program's weighted abstract calls. -/
@[expose]
noncomputable def bound (cost : OperationCost Interface) (program : FreeM Interface Result) :
    ℝ≥0∞ := FreeM.wpFold (OpSpec.charge cost.weight) program (fun _ ↦ 0)

@[simp] theorem bound_pure (cost : OperationCost Interface) (value : Result) :
    cost.bound (pure value) = 0 := rfl

end OperationCost

end ProtocolProof
