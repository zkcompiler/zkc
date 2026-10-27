module
public import Zkc.Construction.Uniform.DomainExecution
@[expose] public section
/-! A compositional loop seam for the authoritative evaluator. -/
set_option autoImplicit false
namespace Zkc.Construction.Uniform.DomainAdapter
open Zkc.Source
variable {carriers : Structured.Carriers}

def yieldValues (yielded : List Nat) (declared : List ValueSort)
    (final : Domain.Environment carriers) :
    PIR.Process (Domain.effects carriers) (Domain.Environment carriers) :=
  match Domain.read final yielded with
  | some values => if Domain.sortsMatch declared values then .done values else .halt .refused
  | none => .halt .refused

theorem iterate_bind (body : Domain.View.Block carriers)
    (outer : Domain.Environment carriers) (yielded : List Nat) (declared : List ValueSort)
    (index : Nat) (rest : List Nat) (carried : Domain.Environment carriers) :
    Domain.iterate body outer yielded declared (index :: rest) carried =
      ((body (outer ++ .data (.index index) :: carried)).bind (yieldValues yielded declared)).bind
        (Domain.iterate body outer yielded declared rest) := by
  simp only [Domain.iterate, PIR.Process.bind_assoc]
  congr 1
  funext final
  cases found : Domain.read final yielded with
  | none => simp only [yieldValues, found, PIR.Process.bind]
  | some values =>
      simp only [yieldValues, found]
      by_cases sorted : Domain.sortsMatch declared values = true <;>
        simp only [sorted, Bool.false_eq_true, ite_true, ite_false, PIR.Process.bind]

end Zkc.Construction.Uniform.DomainAdapter
