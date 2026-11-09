module

public import Zkc.Verification.ProgramLogic.Oracle.SourceExecution
public import Zkc.Tests.IR.OracleProcessData

@[expose] public section

set_option autoImplicit false
namespace TestsSecurity.OracleSourceExecution

open OracleComp OracleSpec
open Zkc.Source Zkc.Source.Structured
open ZkcSecurity.VCVio.Execution
open Tests.OracleProcessData

/-- An extra hidden uniform draw changes oracle cost, but not the complete returned record. -/
def sampled {I : PIR.Signature} {S E : Type} (handler : PIR.Handler I S E) :
    PIR.MonadHandler ProbComp I S E := fun operation current ↦ do
  let _ ← ($ᵗ Bool)
  pure (handler operation current)

theorem sampled_law {I : PIR.Signature} {S E : Type}
    (handler : PIR.Handler I S E) (operation : I.Op) (current : S) :
    SameDist (sampled handler operation current) (pure (handler operation current)) := by
  let : MeasurableSpace (PIR.Execution S E (I.Reply operation)) := ⊤
  exact OracleComp.evalDist_bind_const _ _

/-- Both providers share the actual nested-table fixture's state; all failures and logs
are preserved even when every external operation consumes hidden randomness. -/
theorem nested_actual (failure : Option (Nat × PIR.Stop)) (stopAfter : Bool) :
    SameDist
      (OracleProcess.runM model [checked] (sampled (ordinary false)) (sampled (base failure))
        (process stopAfter) state)
      (OracleProcess.runM model [checked]
        (fun operation current ↦ pure (ordinary false operation current))
        (fun request current ↦ pure (base failure request current)) (process stopAfter) state) :=
  ZkcSecurity.VCVio.OracleSource.protocol_sameDist _ _ _ _ _
    (sampled_law (ordinary false)) (sampled_law (base failure)) _ _

private theorem pure_same_iff {A : Type} (left right : A) :
    SameDist (pure left : ProbComp A) (pure right) ↔ left = right := by
  constructor
  · intro same
    have belongs : left ∈ support (pure left : ProbComp A) := by simp
    rw [same.support_eq] at belongs
    simpa using belongs
  · intro same
    subst right
    exact SameDist.refl _

/-- Identical returned values cannot hide a different residual provider state. -/
example : ¬ SameDist
    (pure (⟨.returned (), 0, ["read"]⟩ : PIR.Execution Nat String Unit) : ProbComp _)
    (pure ⟨.returned (), 1, ["read"]⟩) := by
  rw [pure_same_iff]
  intro same
  exact Nat.zero_ne_one (congrArg PIR.Execution.state same)

/-- Provider events remain ordered observations of the replacement law. -/
example : ¬ SameDist
    (pure (⟨.returned (), 0, ["first", "second"]⟩ : PIR.Execution Nat String Unit) : ProbComp _)
    (pure ⟨.returned (), 0, ["second", "first"]⟩) := by
  rw [pure_same_iff]
  intro same
  have different := congrArg PIR.Execution.events same
  simp at different

/-- A failure is not normalized to a successful reply with the same state and log. -/
example : ¬ SameDist
    (pure (⟨.stopped .abort, 0, ["read"]⟩ : PIR.Execution Nat String Unit) : ProbComp _)
    (pure ⟨.returned (), 0, ["read"]⟩) := by
  rw [pure_same_iff]
  intro same
  have different := congrArg PIR.Execution.outcome same
  cases different

#print axioms ZkcSecurity.VCVio.OracleSource.handler_sameDist
#print axioms ZkcSecurity.VCVio.OracleSource.execute_sameDist
#print axioms ZkcSecurity.VCVio.OracleSource.protocol_sameDist
#print axioms ZkcSecurity.VCVio.OracleSource.source_sameDist
#print axioms ZkcSecurity.VCVio.OracleSource.protocol_relTriple
#print axioms ZkcSecurity.VCVio.OracleSource.source_relTriple
#print axioms nested_actual

end TestsSecurity.OracleSourceExecution
