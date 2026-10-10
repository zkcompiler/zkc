import Zkc.Compiler.FactorGuards
import Zkc.Polynomial.Bilinear.Execution

set_option autoImplicit false

namespace Zkc.Polynomial.Bilinear.Compilation
open PIR Zkc.Compiler.FactorGuards Zkc.Modules.FactorExecution

variable {K E A : Type}

open Zkc.Polynomial.Bilinear.Execution Zkc.Modules.Factor in
/-- Both passes act on one caller: actual immutable preparation, actual stateful
    calls, and factor inference with Zkc.Modules.FactorState outcome-specific invalidation. -/
theorem compile_with_preparation (contracts : Nat → Zkc.Modules.FactorState.Spec Nat)
    (external : Nat → Zkc.Modules.FactorState.Implementation Nat E)
    (laws : ∀ id, Zkc.Modules.FactorState.Satisfies (contracts id) (external id)) (calls : Nat → Call)
    (src : Zkc.Compiler.FactorProgram.Source) (s : Zkc.Modules.FactorState.World Nat) (cache : Cache)
    (facts : List Fact) (available : List Nat)
    (cacheValid : Zkc.Modules.Preparation.Valid Zkc.Source.TablePreparation.provider cache)
    (valid : Valid s.values facts) (known : Zkc.Modules.FactorState.Known s available)
    (legal : Zkc.Compiler.FactorProgram.Legal (fun id => spec contracts (calls id))
      (fun id => reference external (calls id)) available src s) :
    Related SameWorld Preparation.view Preparation.view
      ((Zkc.Compiler.FactorExecution.embed (Zkc.Compiler.FactorProgram.compile (fun id => (spec contracts (calls id)).post)
        facts available src)).run (handler .memo external calls) (s,cache))
      ((Zkc.Compiler.FactorExecution.embed (Zkc.Compiler.FactorProgram.direct src)).run (handler .direct external calls) (s,cache)) := by
  have compiled := Zkc.Compiler.FactorExecution.compiled_execution (fun id => spec contracts (calls id))
    (fun id => reference external (calls id)) (fun id => reference_satisfies contracts external laws (calls id))
    src s facts available valid known legal
  have hm := run_reference .memo external calls
    (Zkc.Compiler.FactorExecution.embed (Zkc.Compiler.FactorProgram.compile (fun id => (spec contracts (calls id)).post) facts available src))
    (s,cache) cacheValid
  have hd := run_reference .direct external calls (Zkc.Compiler.FactorExecution.embed (Zkc.Compiler.FactorProgram.direct src)) (s,cache) cacheValid
  rw [compiled] at hm
  exact executions_from_reference _ _ _ hm hd

def mixedHandler (mode : Zkc.Modules.Preparation.Mode) (external : Nat → Zkc.Modules.FactorState.Implementation Nat E)
    (calls : Nat → Zkc.Polynomial.Bilinear.Execution.Call) := guard (fun s : Zkc.Polynomial.Bilinear.Execution.State => s.1.known) (Zkc.Polynomial.Bilinear.Execution.handler mode external calls)

theorem mixed_reference (mode : Zkc.Modules.Preparation.Mode) (external : Nat → Zkc.Modules.FactorState.Implementation Nat E)
    (calls : Nat → Zkc.Polynomial.Bilinear.Execution.Call) (prog : Proc (Zkc.Modules.FactorExecution.signature Nat) A)
    (s : Zkc.Polynomial.Bilinear.Execution.State) (valid : Zkc.Modules.Preparation.Valid Zkc.Source.TablePreparation.provider s.2) :
    Related Zkc.Polynomial.Bilinear.Execution.Rel Preparation.view (fun e => [e])
      (prog.run (mixedHandler mode external calls) s)
      (prog.run (guard Zkc.Modules.FactorState.World.known (Zkc.Modules.FactorExecution.handler (fun id => Zkc.Polynomial.Bilinear.Execution.reference external (calls id)))) s.1) := by
  apply run_related _ _ _ _ _ _ prog s s.1 ⟨rfl,valid⟩
  apply guarded_handlers_related
  · intro a b r; exact congrArg Zkc.Modules.FactorState.World.known r.1
  · exact Zkc.Polynomial.Bilinear.Execution.handlers_related mode external calls

/-- The composed compiler is correct with actual runtime refusal at unavailable
    demands, without assuming that the guard can be erased for arbitrary callers. -/
theorem compile_with_guards (contracts : Nat → Zkc.Modules.FactorState.Spec Nat)
    (external : Nat → Zkc.Modules.FactorState.Implementation Nat E)
    (laws : ∀ id, Zkc.Modules.FactorState.Satisfies (contracts id) (external id)) (calls : Nat → Zkc.Polynomial.Bilinear.Execution.Call)
    (src : Zkc.Compiler.FactorProgram.Source) (s : Zkc.Modules.FactorState.World Nat) (cache : Zkc.Polynomial.Bilinear.Execution.Cache)
    (facts : List Zkc.Modules.Factor.Fact) (available : List Nat)
    (cacheValid : Zkc.Modules.Preparation.Valid Zkc.Source.TablePreparation.provider cache)
    (valid : Zkc.Modules.Factor.Valid s.values facts) (known : Zkc.Modules.FactorState.Known s available)
    (legal : Zkc.Compiler.FactorProgram.Legal (fun id => Zkc.Polynomial.Bilinear.Execution.spec contracts (calls id))
      (fun id => Zkc.Polynomial.Bilinear.Execution.reference external (calls id)) available src s) :
    Related Zkc.Polynomial.Bilinear.Execution.SameWorld Preparation.view Preparation.view
      ((Zkc.Compiler.FactorExecution.embed (Zkc.Compiler.FactorProgram.compile (fun id => (Zkc.Polynomial.Bilinear.Execution.spec contracts (calls id)).post)
        facts available src)).run (mixedHandler .memo external calls) (s,cache))
      ((Zkc.Compiler.FactorExecution.embed (Zkc.Compiler.FactorProgram.direct src)).run (mixedHandler .direct external calls) (s,cache)) := by
  have compiled := guarded_analysis (fun id => Zkc.Polynomial.Bilinear.Execution.spec contracts (calls id))
    (fun id => Zkc.Polynomial.Bilinear.Execution.reference external (calls id))
    (fun id => Zkc.Polynomial.Bilinear.Execution.reference_satisfies contracts external laws (calls id)) src s facts available valid known legal
  have hm := mixed_reference .memo external calls
    (Zkc.Compiler.FactorExecution.embed (Zkc.Compiler.FactorProgram.compile (fun id => (Zkc.Polynomial.Bilinear.Execution.spec contracts (calls id)).post) facts available src))
    (s,cache) cacheValid
  have hd := mixed_reference .direct external calls (Zkc.Compiler.FactorExecution.embed (Zkc.Compiler.FactorProgram.direct src)) (s,cache) cacheValid
  rw [compiled] at hm
  exact Zkc.Polynomial.Bilinear.Execution.executions_from_reference _ _ _ hm hd


/-- Join refusal-preserving inference to the existing preparation simulation.
    The initial cache/fact invariants and actual module contracts remain required. -/
theorem compile_until_refusal (contracts : Nat → Zkc.Modules.FactorState.Spec Nat)
    (external : Nat → Zkc.Modules.FactorState.Implementation Nat E)
    (laws : ∀ id, Zkc.Modules.FactorState.Satisfies (contracts id) (external id)) (calls : Nat → Zkc.Polynomial.Bilinear.Execution.Call)
    (src : Zkc.Compiler.FactorProgram.Source) (s : Zkc.Modules.FactorState.World Nat) (cache : Zkc.Polynomial.Bilinear.Execution.Cache)
    (facts : List Zkc.Modules.Factor.Fact) (available : List Nat)
    (cacheValid : Zkc.Modules.Preparation.Valid Zkc.Source.TablePreparation.provider cache)
    (valid : Zkc.Modules.Factor.Valid s.values facts) (known : Zkc.Modules.FactorState.Known s available)
    (reached : CallsBeforeRefusal (fun id => Zkc.Polynomial.Bilinear.Execution.spec contracts (calls id))
      (fun id => Zkc.Polynomial.Bilinear.Execution.reference external (calls id)) src s) :
    Related Zkc.Polynomial.Bilinear.Execution.SameWorld Preparation.view Preparation.view
      ((Zkc.Compiler.FactorExecution.embed (Zkc.Compiler.FactorProgram.compile (fun id => (Zkc.Polynomial.Bilinear.Execution.spec contracts (calls id)).post)
        facts available src)).run (mixedHandler .memo external calls) (s,cache))
      ((Zkc.Compiler.FactorExecution.embed (Zkc.Compiler.FactorProgram.direct src)).run (mixedHandler .direct external calls) (s,cache)) := by
  have compiled := guarded_analysis_until_refusal (fun id => Zkc.Polynomial.Bilinear.Execution.spec contracts (calls id))
    (fun id => Zkc.Polynomial.Bilinear.Execution.reference external (calls id))
    (fun id => Zkc.Polynomial.Bilinear.Execution.reference_satisfies contracts external laws (calls id))
    src s facts available valid known reached
  have hm := mixed_reference .memo external calls
    (Zkc.Compiler.FactorExecution.embed (Zkc.Compiler.FactorProgram.compile (fun id => (Zkc.Polynomial.Bilinear.Execution.spec contracts (calls id)).post)
      facts available src)) (s,cache) cacheValid
  have hd := mixed_reference .direct external calls
    (Zkc.Compiler.FactorExecution.embed (Zkc.Compiler.FactorProgram.direct src)) (s,cache) cacheValid
  rw [compiled] at hm
  exact Zkc.Polynomial.Bilinear.Execution.executions_from_reference _ _ _ hm hd

open Zkc.Modules.Factor Zkc.Compiler.FactorReuse Zkc.Polynomial.Bilinear.Factor in
/-- This bounded producer join uses the existing demand inference. It does
    not identify a full evaluation request with a prefix materialization key. -/
theorem inference_after_preparation (o a b c d x : Nat)
    (available : List Nat) (q : Query) :
    let s := materialized o a b c d x
    let facts := [Zkc.Source.FactorInputs.fact (source o) 0]
    runPlan s q (infer facts available q) = runQuery s q := by
  apply inferred_value
  intro f hf
  have he : f = Zkc.Source.FactorInputs.fact (source o) 0 := by simpa using hf
  subst f
  exact prepared_means o a b c d x

end Zkc.Polynomial.Bilinear.Compilation
