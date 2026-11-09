module

public import Zkc.Program.Interpretation

/-!
# Components implemented through another service interface

The implementation is a fixed operation-to-program interpretation, not a proof-selected
whole client. Local laws cover complete outcomes, private state and ordered observations,
including malformed replies and terminal stops. The generic contextual theorem applies to
all well-founded clients. This exact deterministic boundary carries no cryptographic loss.
-/

@[expose] public section

namespace ProtocolProof
open PIR

variable {I J K : Signature} {S T U E F G O A : Type}

/-- A local implementation law for fixed code and fixed complete observations. -/
structure InterpretationContract (implementation : OperationInterpretation I J)
    (source : Handler I S E) (target : Handler J T F)
    (relation : S → T → Prop) (sourceView : E → List O) (targetView : F → List O) : Prop where
  operation : ∀ op s t, relation s t →
    Related relation sourceView targetView (source op s) ((implementation op).run target t)

namespace InterpretationContract

variable {implementation : OperationInterpretation I J}
  {source : Handler I S E} {target : Handler J T F}
  {relation : S → T → Prop} {sourceView : E → List O} {targetView : F → List O}

/-- Reuse one local installation in every adaptive, nested or repeated calling context. -/
theorem run (contract : InterpretationContract implementation source target relation
    sourceView targetView) (client : Process I A) (s : S) (t : T) (initial : relation s t) :
    Related relation sourceView targetView (client.run source s)
      ((client.interpret implementation).run target t) :=
  Process.run_interpret_related implementation source target relation sourceView targetView
    contract.operation client s t initial

/-- Compose implementations through a meaningful intermediate state and common observation. -/
theorem comp {second : OperationInterpretation J K} {backend : Handler K U G}
    {nextRelation : T → U → Prop} {backendView : G → List O}
    (firstLaw : InterpretationContract implementation source target relation sourceView targetView)
    (secondLaw : InterpretationContract second target backend nextRelation targetView backendView) :
    InterpretationContract (fun op ↦ (implementation op).interpret second) source backend
      (fun s u ↦ ∃ t, relation s t ∧ nextRelation t u) sourceView backendView where
  operation op s u initial := by
    obtain ⟨t, hst, htu⟩ := initial
    exact related_trans relation nextRelation sourceView targetView backendView _ _ _
      (firstLaw.operation op s t hst) (secondLaw.run (implementation op) t u htu)

/-- Identity installation preserves all state and events, with no hidden projection. -/
theorem identity (handler : Handler I S E) (view : E → List O) :
    InterpretationContract (fun op ↦ Process.call op Process.done) handler handler
      Eq view view where
  operation op s t same := by
    subst t
    change Related Eq view view (handler op s) ((handler op s).follow _)
    simp only [Process.run, Execution.follow_return]
    exact ⟨rfl, rfl, rfl⟩

/-- A chosen final-state observer requires its own compatibility with the invariant. -/
theorem observe {V : Type}
    (contract : InterpretationContract implementation source target relation sourceView targetView)
    (left : S → V) (right : T → V)
    (compatible : ∀ s t, relation s t → left s = right t)
    (client : Process I A) (s : S) (t : T) (initial : relation s t) :
    ((client.run source s).outcome, left (client.run source s).state,
      observeEvents sourceView (client.run source s).events) =
    (((client.interpret implementation).run target t).outcome,
      right ((client.interpret implementation).run target t).state,
      observeEvents targetView ((client.interpret implementation).run target t).events) :=
  related_observer relation sourceView targetView left right compatible _ _
    (contract.run client s t initial)

end InterpretationContract
end ProtocolProof
