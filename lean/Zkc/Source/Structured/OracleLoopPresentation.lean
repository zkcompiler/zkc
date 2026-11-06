module

public import Zkc.Source.Structured.OracleProtocol
public import Zkc.Source.Structured.ProtocolLoopPresentation

@[expose] public section

/-! The logical-oracle instance of the generic loop presentation. These observations
are the existing structural effects, not replacements for source transcript actions. -/

set_option autoImplicit false
namespace Zkc.Source.Structured.OracleProtocol

/-- Exactly the existing enter/leave operations. A stopped body never emits leave. -/
def iterationObservations (model : DomainModel) : IterationObservations (Interface model) :=
  .observed
    (fun site index ↦ .call (.iteration site index) (fun _ ↦ .done ()))
    (fun _ _ ↦ .call .leave (fun _ ↦ .done ()))

/-- Installs the logical-oracle algebra into `ProtocolLoopPresentation.present`.
This infrastructure law is independent of the source program and mathematical invariant. -/
theorem iteration_eq (model : DomainModel) (self : Nat)
    (ordinary : Evaluation.ComponentTablesOn model.toCarriers (Interface model))
    (helpers : ProtocolCalculation.Tables model.toCarriers (Interface model))
    (context : ProtocolContext) (site : String) {A : Type}
    (index : Nat) (process : PIR.Process (Interface model) A) :
    (algebra model self ordinary helpers).iteration context site index process =
      (iterationObservations model).within site index process := by
  change enter model (.iteration site index) process =
    (iterationObservations model).within site index process
  simp only [iterationObservations, IterationObservations.within, enter, PIR.Process.bind]

end Zkc.Source.Structured.OracleProtocol
