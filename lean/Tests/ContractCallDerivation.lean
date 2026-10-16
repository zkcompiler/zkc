import Zkc.Source.DeriveRegion
import Tests.ContractComposition
import ZkcTools.DeclarationAudit

/-! Source traversal consumes checked callee laws without a hand-authored
caller spine. These are process equations, not security certificates. -/
set_option autoImplicit false
set_option smartUnfolding false
noncomputable section
namespace Tests.ContractCallDerivation
open Zkc.Source Zkc.Source.Structured Tests.ContractComposition

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

private theorem identity_step (ignored actual : Nat) :
    (participantMeaning (unit.tables F G) 1 (unit.protocolTable F G)).OperationLaw
      (fun op => .call op .done) (.protocolApply identitySignature [1, 0] "swapped")
      (identityOccurrence.callSite.operands.eval (inputs (F := F) (G := G) ignored actual).get)
      .nil (.done (.cons (some actual) .nil)) := by
  exact unit.protocolApply_operationLaw (observedSites F G) observeAction (unit.tables F G)
    (fun op => .call op .done) identityDefinition List.mem_cons_self identitySignature rfl
    identityBody rfl [1, 0] "swapped" {} 1 _ (.done (.cons (some actual) .nil))
    (fun _ => rfl)

/-- The local operation rule suffices for the whole actual call and suffix. -/
theorem identity_derived (ignored actual : Nat) :
    Region.Derivation (participantMeaning (unit.tables F G) 1 (unit.protocolTable F G))
      (fun op => .call op .done) identityCall (inputs (F := F) (G := G) ignored actual).get
      (.done (.cons (some actual) .nil)) := by
  derive_region using (exact identity_step ignored actual)

theorem identity_equation (ignored actual : Nat) :
    identityCall.denote (participantMeaning (unit.tables F G) 1 (unit.protocolTable F G))
      (inputs (F := F) (G := G) ignored actual).get = .done (.cons (some actual) .nil) :=
  (identity_derived ignored actual).sound_identity

/-- A nonparticipant needs no callee law, including a fabricated stopped target.
The actual source operation still returns the absent output tuple. -/
theorem outside_derived (ignored actual : Nat) :
    Region.Derivation (participantMeaning (unit.tables F G) 2 (unit.protocolTable F G))
      (fun op => .call op .done) identityCall (inputs (F := F) (G := G) ignored actual).get
      (.done (.cons none .nil)) := by
  derive_region using (
    exact unit.protocolApply_operationLaw (observedSites F G) observeAction (unit.tables F G)
      (fun op => .call op .done) identityDefinition List.mem_cons_self identitySignature rfl
      identityBody rfl [1, 0] "swapped" {} 2 _ (.halt .refused)
      (fun inside => by contradiction))

/-- The generic law also supports plain participants without any site marks. -/
theorem plain_derived (ignored actual : Nat) :
    Region.Derivation
      (participantMeaningWith (.silent (participantInterface F G)) (participantActions F G)
        ⟨[], []⟩ 1 (unit.plainProtocolTable F G))
      (fun op => .call op .done) identityCall (inputs (F := F) (G := G) ignored actual).get
      (.done (.cons (some actual) .nil)) := by
  derive_region using (
    exact unit.protocolApply_operationLaw (.silent (participantInterface F G))
      (participantActions F G) ⟨[], []⟩ (fun op => .call op .done)
      identityDefinition List.mem_cons_self identitySignature rfl identityBody rfl
      [1, 0] "swapped" {} 1 _ (.done (.cons (some actual) .nil)) (fun _ => rfl))

/-- Structural traversal retains a stopped callee's earlier mark and never
executes the caller's suffix, including when the callee has zero outputs. -/
theorem stopped_derived :
    Region.Derivation (participantMeaning (unit.tables F G) 0 (unit.protocolTable F G))
      (fun op => .call op .done)
      (.letOp (.protocolApply stopSignature [0, 1] "call") .nil .nil
        (.letOp (.mark "after-call") .nil .nil (.ret .nil)))
      (Values.nil (Value := Component (assignment F G))).get
      (.call (.mark (qualifyProtocolSite (some "call") "before-stop")) (fun _ => .halt .reject)) := by
  derive_region using (
    first
    | exact unit.protocolApply_operationLaw (observedSites F G) observeAction (unit.tables F G)
        (fun op => .call op .done) stopDefinition (List.mem_cons_of_mem _ List.mem_cons_self)
        stopSignature rfl stopBody rfl [0, 1] "call" {} 0 .nil
        (.call (.mark (qualifyProtocolSite (some "call") "before-stop")) (fun _ => .halt .reject))
        (fun _ => rfl)
    | apply RegionMeaning.OperationLaw.identity
      rfl)

/-- Keeping the exact body as target is a valid identity law, without claiming
any property beyond that same process. -/
example : CallSemanticObligations identityCall
    (fun call => (identitySpecification (F := F) (G := G) call).identity) :=
  CallSemanticObligations.identity _ _

def impossibleSpecification (call : CallOccurrence identityCall) :
    CallSpecification (F := F) (G := G) unit call :=
  { identitySpecification (F := F) (G := G) call with
    premise := fun _ _ _ => False, target := fun _ _ _ => .halt .refused }

theorem impossible_resolved : CallSemanticObligations identityCall
    (impossibleSpecification (F := F) (G := G)) := by
  intro call context self args impossible
  exact False.elim impossible

/-- A vacuous record cannot supply substitution's actual precondition. -/
example (ignored actual : Nat) :
    ¬ (impossibleSpecification (F := F) (G := G) identityOccurrence).premise
      (ProtocolContext.enter {} "swapped" [1, 0]) 1
      (identityOccurrence.callSite.operands.eval (inputs ignored actual).get) := by
  intro impossible
  exact impossible

/-- The desired stopped equation is false despite that vacuous resolution. -/
example (ignored actual : Nat) :
    identityCall.denote (participantMeaning (unit.tables F G) 1 (unit.protocolTable F G))
      (inputs (F := F) (G := G) ignored actual).get ≠ .halt .refused := by
  rw [identity_equation]
  intro impossible
  cases impossible

/-- A different body with the same ABI fails the exact checked-body link. -/
def changedBody : Region protocolDialect [.index] [.index] :=
  .letOp (.mark "extra") .nil .nil identityBody
example : identityDefinition.raw ≠ changedBody.erase := by
  intro same
  cases same

#print axioms Zkc.Source.Structured.UnitPayload.protocolApply_operationLaw
#print axioms identity_equation
#print axioms outside_derived
#print axioms plain_derived
#print axioms stopped_derived

run_cmd do
  ZkcTools.DeclarationAudit.check
    [`Zkc.Source.Structured.ContractCalls, `Zkc.Source.Structured.ContractComposition]
    "CALL-COMPOSITION-AUDIT-PASS" true
end Tests.ContractCallDerivation
