import Zkc.Semantics.Execution
import Zkc.Modules.FactorContract

set_option autoImplicit false
namespace Zkc.Modules.FactorExecution
open PIR
open Zkc.Modules.Factor

inductive Op where
  | demand : Query → Plan → Op
  | external : Nat → Op

def signature (K : Type) : Signature :=
  ⟨Op, fun o => match o with | .demand _ _ => K | .external _ => Bool⟩

variable {K E : Type}

/-- Zkc.Modules.FactorState's false result is recoverable and therefore a returned Bool. -/
def returned (out : Zkc.Modules.FactorState.Returned K E) : Execution (Zkc.Modules.FactorState.World K) E Bool :=
  ⟨.returned out.success,out.world,out.events⟩

def contract (spec : Zkc.Modules.FactorState.Spec K) : Contract (Zkc.Modules.FactorState.World K) E Bool where
  pre := spec.pre
  post := fun s out => ∃ b, out.outcome = .returned b ∧
    Zkc.Modules.FactorState.Justifies (spec.post b) s out.state

theorem contract_interpretation (spec : Zkc.Modules.FactorState.Spec K) (impl : Zkc.Modules.FactorState.Implementation K E) :
    Satisfies (contract spec) (fun s => returned (impl s)) ↔ Zkc.Modules.FactorState.Satisfies spec impl := by
  constructor
  · intro h s hs
    obtain ⟨b,hb,hpost⟩ := h s hs
    have hb' : (impl s).success = b := Outcome.returned.inj hb
    simpa [returned,hb'] using hpost
  · intro h s hs
    exact ⟨(impl s).success,rfl,h s hs⟩

def handler (impl : Nat → Zkc.Modules.FactorState.Implementation K E) :
    Handler (signature K) (Zkc.Modules.FactorState.World K) E
  | .demand q plan, s => ⟨.returned (runPlan s.values q plan),s,[]⟩
  | .external id, s => returned (impl id s)

variable {S T F O : Type}

/-- Refuse an unavailable or wrong-arity demand before invoking its handler.
    This guard does not pretend to check every module precondition or source binding. -/
def guard (known : S → List Nat) (h : Handler (signature K) S E) :
    Handler (signature K) S E
  | .demand q p, s =>
    if Zkc.Modules.FactorState.Ready (known s) q then h (.demand q p) s else ⟨.stopped .refused,s,[]⟩
  | .external id, s => h (.external id) s

theorem guarded_handlers_related (R : S → T → Prop) (left : E → List O) (right : F → List O)
    (knownS : S → List Nat) (knownT : T → List Nat)
    (h : Handler (signature K) S E) (g : Handler (signature K) T F)
    (sameKnown : ∀ s t, R s t → knownS s = knownT t)
    (law : HandlerRelated R left right h g) :
    HandlerRelated R left right (guard knownS h) (guard knownT g) := by
  intro op s t rel
  cases op with
  | external id => exact law (.external id) s t rel
  | demand q p =>
    have hk := sameKnown s t rel
    by_cases ready : Zkc.Modules.FactorState.Ready (knownS s) q
    · simpa [guard,ready,← hk] using law (.demand q p) s t rel
    · simp only [guard,← hk,if_neg ready]
      exact ⟨rfl,rel,rfl⟩

end Zkc.Modules.FactorExecution
