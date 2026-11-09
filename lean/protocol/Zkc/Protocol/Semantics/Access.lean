module

public import Zkc.Protocol.Semantics.System

/-!
# Request-fixed access and weighted abstract-call bounds

The algorithm sees only its public input and the answers of its typed interface. The
environment, which may contain an adversary implementation, reaches it through the fixed
handler. The resource reading bounds the weights of abstract calls over all possible answers.
Pure computation is uncharged: this is not a time-complexity or polynomial-time certificate.
-/

public section

open PIR MeasureTheory
open scoped ENNReal

namespace ProtocolProof

section Execution

variable (Public Environment : Type) (Interface : Signature) (State Event Result : Type)
  [∀ op, MeasurableSpace (Interface.Reply op)]
  [MeasurableSpace State] [MeasurableSpace Event]

/-- An algorithm and its allowed services are fixed before any security evidence. -/
structure AccessExecution where
  system : System Environment Interface State Event
  publicInput : Environment → Public
  algorithm : Public → Process Interface Result

variable {Public Environment Interface State Event Result}

/-- Interpret the selected algorithm with exactly the request's services and initial law. -/
@[expose] noncomputable def AccessExecution.experiment
    [∀ op, Countable (Interface.Reply op)] [∀ op, MeasurableSingletonClass (Interface.Reply op)]
    [MeasurableSpace Result]
    (execution : AccessExecution Public Environment Interface State Event Result) :
    Experiment Environment (Execution State Event Result) :=
  execution.system.experiment (fun environment ↦
    execution.algorithm (execution.publicInput environment))

end Execution

variable {Interface : Signature} {Result : Type}

/-- A request-owned weight for each permitted abstract operation, not a host-runtime model. -/
structure OperationCost (Interface : Signature) where
  weight : Interface.Op → ℝ≥0∞

namespace OperationCost

/-- Count every abstract call once. -/
@[expose] def calls (Interface : Signature) : OperationCost Interface := ⟨fun _ ↦ 1⟩

/-- A structural bound on the selected program's weighted abstract calls. -/
@[expose]
noncomputable def bound (cost : OperationCost Interface) : Process Interface Result → ℝ≥0∞
  | .done _ => 0
  | .halt _ => 0
  | .call operation next => cost.weight operation + ⨆ reply, cost.bound (next reply)

@[simp] theorem bound_pure (cost : OperationCost Interface) (value : Result) :
    cost.bound (pure value) = 0 := rfl

@[simp] theorem bound_done (cost : OperationCost Interface) (value : Result) :
    cost.bound (.done value) = 0 := rfl

@[simp] theorem bound_halt (cost : OperationCost Interface) (reason : Stop) :
    cost.bound (Process.halt (A := Result) reason) = 0 := rfl

@[simp] theorem bound_call (cost : OperationCost Interface) (operation : Interface.Op)
    (next : Interface.Reply operation → Process Interface Result) :
    cost.bound (.call operation next) = cost.weight operation + ⨆ reply, cost.bound (next reply) :=
  rfl

/-- No continuation is charged after an explicit process stop. -/
@[simp] theorem bound_halt_bind {Next : Type} (cost : OperationCost Interface) (reason : Stop)
    (next : Result → Process Interface Next) :
    cost.bound ((Process.halt reason).bind next) = 0 := rfl

end OperationCost

/-- Observe the complete outcome, retaining every terminal stop and its original mass. -/
@[expose] def Observation.outcome {State Event Result : Type}
    [MeasurableSpace State] [MeasurableSpace Event] [MeasurableSpace Result] :
    Observation (Execution State Event Result) (Outcome Result) :=
  ⟨Execution.outcome, Execution.measurable_outcome⟩

end ProtocolProof
