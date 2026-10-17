import Zkc.Source.Structured.ContractComposition

set_option autoImplicit false
set_option smartUnfolding false
noncomputable section
namespace Tests.ContractComposition
open Zkc.Source Zkc.Source.Structured

def identitySignature : ProtocolSignature :=
  { name := "identity", roles := ["P", "V"], inputs := [.index], outputs := [.index],
    inputScopes := [[0]], outputScopes := [[0]] }

def identityBody : Region protocolDialect [.index] [.index] := .ret (.cons .here .nil)
def identityDefinition : CheckedProtocol :=
  { toProtocolSignature := identitySignature, raw := identityBody.erase,
    body := identityBody, formed := identityBody.elaborate_erase }

def stopSignature : ProtocolSignature :=
  { name := "stop", roles := ["P", "V"], inputs := [], outputs := [], inputScopes := [], outputScopes := [] }
def stopBody : Region protocolDialect [] [] :=
  .letOp (.mark "before-stop") .nil .nil <|
  .letOp (.calculate (.booleanConstant false) rfl) .nil .nil <|
  .letOp (.guard 0 "reject") (.cons .here .nil) .nil (.ret .nil)
def stopDefinition : CheckedProtocol :=
  { toProtocolSignature := stopSignature, raw := stopBody.erase,
    body := stopBody, formed := stopBody.elaborate_erase }

def unit : UnitPayload :=
  { definitions := [], protocols := [identityDefinition, stopDefinition], entryIndex := ⟨0, by decide⟩,
    linked := by decide, protocolsLinked := by decide, available := rfl,
    realizationClosed := by decide, mapClosed := by decide }

def identityCall : Region protocolDialect [.index, .index] [.index] :=
  .letOp (.protocolApply identitySignature [1, 0] "swapped") (.cons (.there .here) .nil) .nil
    (.ret (.cons .here .nil))

def identityOccurrence : CallOccurrence identityCall :=
  CallOccurrence.here identitySignature [1, 0] "swapped" _ _

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

def inputs (ignored actual : Nat) : Values (Component (assignment F G)) [.index, .index] :=
  .cons (some ignored) (.cons (some actual) .nil)

/-- Structural inspection supplies the local law. The selected SECOND operand
and swapped role map determine the returned value at root participant one. -/
theorem actual_operand_and_role (ignored actual : Nat) :
    identityCall.denote (participantMeaning (unit.tables F G) 1 (unit.protocolTable F G))
      (inputs (F := F) (G := G) ignored actual).get = .done (.cons (some actual) .nil) := by
  have localProof : CalleeResolution
      (participantMeaning (unit.tables F G) 1 (unit.protocolTable F G) (ProtocolContext.enter {} "swapped" [1, 0]))
      identityBody
      (maskValues 1 ((ProtocolContext.enter {} "swapped" [1, 0]).mapScopes identitySignature.inputScopes)
        (identityOccurrence.callSite.operands.eval (inputs (F := F) (G := G) ignored actual).get)).get
      (.done (.cons (some actual) .nil)) :=
    .inspect (.ret _ _)
  exact unit.protocolApply_substitute identityDefinition List.mem_cons_self identitySignature rfl
    identityBody rfl [1, 0] "swapped" {} 1 identityOccurrence.callSite.operands
    identityOccurrence.continuation.2 (inputs ignored actual).get (by decide) _ localProof

/-- The generated inventory has exactly this one actual call. -/
theorem identity_occurrence_unique (call : CallOccurrence identityCall) : call = identityOccurrence := by
  have member := callInventory_complete call
  change call ∈ [identityOccurrence] at member
  exact List.mem_singleton.mp member

/-- A selected local meaning covers every occurrence by the complete inventory,
without consulting whether the callee has any source clauses. -/
def identitySpecification (call : CallOccurrence identityCall) :
    CallSpecification (F := F) (G := G) unit call := by
  have same := identity_occurrence_unique call
  subst call
  exact {
    definition := identityDefinition
    member := List.mem_cons_self
    sameSignature := rfl
    body := identityBody
    exactRaw := rfl
    premise := fun _ _ _ => True
    target := fun context self actual =>
      .done (maskValues self (context.mapScopes identitySignature.inputScopes) actual) }

theorem identity_obligations : CallSemanticObligations identityCall
    (identitySpecification (F := F) (G := G)) := by
  intro selected context self actual _
  obtain ⟨call, _⟩ := selected
  have same := identity_occurrence_unique call
  subst call
  change Values (Component (assignment F G)) [Ty.index] at actual
  cases actual with
  | cons value rest =>
    cases rest
    exact .inspect (.ret _ _)

/-- The consumer uses generated obligations to recover the local source equation. -/
theorem generated_substitution (ignored actual : Nat) :
    identityCall.denote (participantMeaning (unit.tables F G) 1 (unit.protocolTable F G))
      (inputs (F := F) (G := G) ignored actual).get = .done (.cons (some actual) .nil) :=
  CallSemanticObligations.substitute identitySpecification identity_obligations
    identityOccurrence {} 1 (inputs ignored actual).get (by decide) trivial

/-- The same environment cannot fabricate a value at an excluded input/output role. -/
theorem excluded_copy_absent (ignored actual : Nat) :
    identityCall.denote (participantMeaning (unit.tables F G) 0 (unit.protocolTable F G))
      (inputs (F := F) (G := G) ignored actual).get = .done (.cons none .nil) := by
  have localProof : CalleeResolution
      (participantMeaning (unit.tables F G) 0 (unit.protocolTable F G) (ProtocolContext.enter {} "swapped" [1, 0]))
      identityBody
      (maskValues 0 ((ProtocolContext.enter {} "swapped" [1, 0]).mapScopes identitySignature.inputScopes)
        (identityOccurrence.callSite.operands.eval (inputs (F := F) (G := G) ignored actual).get)).get
      (.done (.cons none .nil)) := .inspect (.ret _ _)
  exact unit.protocolApply_substitute identityDefinition List.mem_cons_self identitySignature rfl
    identityBody rfl [1, 0] "swapped" {} 0 identityOccurrence.callSite.operands
    identityOccurrence.continuation.2 (inputs ignored actual).get (by decide) _ localProof

/-- Wrong full callee identity cannot supply the link required by substitution. -/
example : stopDefinition.signature ≠ identitySignature := by decide
example : identitySignature ≠ { identitySignature with inputScopes := [[1]] } := by decide

/-- No clauses are consulted: an incorrect requested callee behavior still
requires an impossible local equation or structural derivation. -/
theorem unresolved_local_call : ¬ CalleeResolution
    (participantMeaning (unit.tables F G) 1 (unit.protocolTable F G))
    identityBody (Values.cons (some 7) Values.nil).get (.halt .refused) := by
  intro resolution
  have impossible := resolution.sound
  change (PIR.Proc.done (Values.cons (some 7) Values.nil) :
    PIR.Proc (observedInterface F G) (Values (Component (assignment F G)) [Ty.index])) = .halt .refused at impossible
  cases impossible

/-- Zero-result calls still stop. The callee's prefix mark survives and the
caller's suffix mark is not run. -/
theorem zero_result_stop :
    (Region.letOp (dialect := protocolDialect) (.protocolApply stopSignature [0, 1] "call") .nil .nil
      (.letOp (.mark "after-call") .nil .nil (.ret .nil))).denote
      (participantMeaning (unit.tables F G) 0 (unit.protocolTable F G))
      (Values.nil (Value := Component (assignment F G))).get =
      .call (.mark (qualifyProtocolSite (some "call") "before-stop")) (fun _ => .halt .reject) := by
  have localProof : CalleeResolution
      (participantMeaning (unit.tables F G) 0 (unit.protocolTable F G)
        (ProtocolContext.enter {} "call" [0, 1]))
      stopBody Values.nil.get
      (.call (.mark (qualifyProtocolSite (some "call") "before-stop")) (fun _ => .halt .reject)) :=
    .localLaw rfl
  exact unit.protocolApply_substitute stopDefinition (List.mem_cons_of_mem _ List.mem_cons_self)
    stopSignature rfl stopBody rfl [0, 1] "call" {} 0 .nil _ Values.nil.get (by decide) _ localProof

end Tests.ContractComposition
