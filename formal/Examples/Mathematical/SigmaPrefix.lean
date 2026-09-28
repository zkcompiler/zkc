import Examples.Mathematical.SigmaSubject
import Zkc.Source.Mathematical.ClosedMeaning
import Zkc.Source.Mathematical.ProtocolLaws
import Examples.Mathematical.SigmaSteps

/-! Prefix certificates for the actual authored Sigma body.

The source erasure and intrinsic erasure belong to admission's retained body.
These lemmas never evaluate admission inside the kernel.
-/

set_option autoImplicit false
namespace Examples.Mathematical.SigmaSubject
open Zkc.Source Zkc.Source.Mathematical

theorem resolved_prefix {vocabulary : Protocol.Vocabulary}
    {resolver : ProtocolResolution.Resolver vocabulary}
    (roles : resolver.roles.roles = [0, 1])
    (body : ProtocolResolution.Body resolver) (same : body.erase = definition.body) :
    ∃ (region : GraphResolution.Region resolver.graph)
      (wire : (ty : vocabulary.Ty) × vocabulary.Wire ty) (tail : Protocol.Raw Nat vocabulary),
      region.erase = commitmentRegion ∧
      body.lower = .query 0 0 0 [] (.pure region.captures region.lower (.message 1 wire 0 1 0 tail)) := by
  obtain ⟨rest, source_prefix⟩ : ∃ rest, definition.body = .mk
      (.query 0 ⟨0⟩ ⟨0⟩ [] :: .pure commitmentRegion ::
        .message 1 ⟨0⟩ [] ⟨0⟩ ⟨1⟩ ⟨0⟩ :: rest) (.ret []) := ⟨_, rfl⟩
  cases body with
  | mk steps terminal =>
    rw [source_prefix, ProtocolResolution.Body.erase] at same
    have stepsEq := (Raw.Body.mk.inj same).1
    obtain ⟨first, afterFirst, rfl, firstEq, afterFirstEq⟩ := List.map_eq_cons_iff.mp stepsEq
    obtain ⟨second, afterSecond, rfl, secondEq, afterSecondEq⟩ := List.map_eq_cons_iff.mp afterFirstEq
    obtain ⟨third, afterThird, rfl, thirdEq, _⟩ := List.map_eq_cons_iff.mp afterSecondEq
    cases first <;> simp only [ProtocolResolution.Step.erase, Raw.Step.query.injEq,
      reduceCtorEq] at firstEq
    case query site owner capability arguments =>
      obtain ⟨rfl, ownerSource, rfl, rfl⟩ := firstEq
      have ownerRole : owner.role = 0 := by
        have selected := owner.selected
        rw [roles, ownerSource] at selected
        exact (Option.some.inj selected).symm
      cases second <;> simp only [ProtocolResolution.Step.erase, Raw.Step.pure.injEq,
        reduceCtorEq] at secondEq
      case pure region =>
        cases third <;> simp only [ProtocolResolution.Step.erase, Raw.Step.message.injEq,
          reduceCtorEq] at thirdEq
        case message site source wire valid sender receiver value =>
          obtain ⟨rfl, _, _, senderSource, receiverSource, rfl⟩ := thirdEq
          have senderRole : sender.role = 0 := by
            have selected := sender.selected
            rw [roles, senderSource] at selected
            exact (Option.some.inj selected).symm
          have receiverRole : receiver.role = 1 := by
            have selected := receiver.selected
            rw [roles, receiverSource] at selected
            exact (Option.some.inj selected).symm
          refine ⟨region, wire, (ProtocolResolution.Body.mk afterThird terminal).lower, secondEq, ?_⟩
          simp only [ProtocolResolution.Body.lower, List.foldr_cons, ProtocolResolution.Step.lower,
            ownerRole, senderRole, receiverRole, List.map_nil]

theorem prepared_prefix (header : DeclarationAdmission.Header BlsAdmission.installed subject)
    {records} {node : ClosedInstances.Node subject (ClosedInstances.entryKey subject)}
    (prepared : ClosedAssembly.Prepared header records (ClosedInstances.entryKey subject) node) :
    ∃ (region : GraphResolution.Region (RegisteredVocabulary.graph header node.checked.parameters))
      (wire : (ty : (RegisteredVocabulary.vocabulary header 0).Ty) ×
        (RegisteredVocabulary.vocabulary header 0).Wire ty)
      (tail : Protocol.Raw Nat (RegisteredVocabulary.vocabulary header 0)),
      region.erase = commitmentRegion ∧
      prepared.bound.body.checked.program.erase =
        .query 0 0 0 [] (.pure region.captures region.lower (.message 1 wire 0 1 0 tail)) := by
  have selected := node.checked.declaration.selected
  change some definition = some node.checked.declaration.value at selected
  have erased : prepared.bound.body.resolved.erase = definition.body :=
    (ClosedAssembly.Prepared.source_erasure header prepared).trans
      (congrArg Raw.Definition.body (Option.some.inj selected).symm)
  obtain ⟨region, wire, tail, regionEq, prefixEq⟩ := resolved_prefix rfl _ erased
  exact ⟨region, wire, tail, regionEq,
    (ClosedAssembly.Prepared.typed_erasure header prepared).trans prefixEq⟩

/-- The source's declaration zero selects scale by identity, rather than by
matching a convenient group/scalar signature. -/
theorem scale_payload (header : DeclarationAdmission.Header BlsAdmission.installed subject)
    (operation : (RegisteredVocabulary.vocabulary header 0).Op)
    (index : operation.val.val.declaration = 0) :
    BlsMeaning.payload header operation.val = BlsInstallation.Operation.scale := by
  apply BlsMeaning.payload_of_identity
  have selected := (BlsMeaning.declaration header operation.val).selected
  conv at selected => lhs; rw [index]
  have identityIndex := congrArg (Option.map (fun op : Raw.Operation => op.identity.index)) selected
  change some 0 = some (BlsMeaning.declaration header operation.val).value.identity.index at identityIndex
  rw [← Option.some.inj identityIndex]
  rfl

/-- The single node and both capture coordinates come from the retained
source region, including the installed operation identity. -/
theorem commitment_lower (header : DeclarationAdmission.Header BlsAdmission.installed subject)
    {arity} (parameters : Fin arity → Static.Expression 0)
    (region : GraphResolution.Region (RegisteredVocabulary.graph header parameters))
    (same : region.erase = commitmentRegion) :
    ∃ operation : (RegisteredVocabulary.vocabulary header 0).Op,
      BlsMeaning.payload header operation.val = BlsInstallation.Operation.scale ∧
      region.captures = [2, 0] ∧
      region.lower = .operation operation [0, 1] (.outputs [0]) := by
  cases region with
  | mk captures nodes outputs =>
    rw [GraphResolution.Region.erase] at same
    change Raw.Region.mk captures (nodes.map GraphResolution.Node.erase) outputs =
      Raw.Region.mk [⟨2⟩, ⟨0⟩] [.operation ⟨0⟩ [] (.object []) [⟨0⟩, ⟨1⟩]] [⟨0⟩] at same
    obtain ⟨rfl, nodesEq, rfl⟩ := Raw.Region.mk.inj same
    obtain ⟨node, rest, rfl, nodeEq, restEq⟩ := List.map_eq_cons_iff.mp nodesEq
    have empty : rest = [] := List.map_eq_nil_iff.mp restEq
    subst rest
    cases node <;> simp only [GraphResolution.Node.erase, Raw.Node.operation.injEq, reduceCtorEq] at nodeEq
    case operation source operation valid arguments =>
      obtain ⟨operationEq, _, _, rfl⟩ := nodeEq
      obtain ⟨signature, registered, _, _, keyEq⟩ := valid
      have index : operation.val.val.declaration = 0 := by
        have index := congrArg (·.declaration) keyEq
        simpa only [operationEq] using index
      refine ⟨operation, scale_payload header operation index, rfl, ?_⟩
      simp only [GraphResolution.Region.lower, List.foldr_cons, List.foldr_nil,
        List.map_cons, List.map_nil]
      erw [GraphResolution.Node.lower]
      rfl

section Semantics
open Zkc.Algebra.Bls12381
variable [Fact baseModulus.Prime]

/-- For every certificate of the canonical Sigma source, the verifier first
receives an arbitrary peer value at site 1. The continuation extends an
environment fixed before that reply. This is a prefix law, not a security or
whole-trace theorem; certificate existence is exercised by consumer tests. -/
theorem verifier_fresh_receive (generator : G1)
    (admitted : SubjectAdmission.Admitted BlsAdmission.installed subject)
    (arguments : Values (Component (BlsAdmission.interpretation generator admitted).Value 1)
      (closed admitted).entry.signature.arguments) :
    SigmaSteps.FreshReceive (BlsAdmission.interpretation generator admitted) 1 0 1 []
      (closed admitted).entry.signature.results (openMeaning generator admitted 1 arguments) := by
  refine (ClosedAssembly.Result.denote_satisfies admitted.header admitted.assembly
    (BlsAdmission.interpretation generator admitted) 1
    (fun key signature _ execution => key = ClosedInstances.entryKey subject →
      SigmaSteps.FreshReceive (BlsAdmission.interpretation generator admitted) 1 0 1 []
        signature.results execution) ?_ arguments) rfl
  intro records key node prepared earlier inputs same
  subst key
  obtain ⟨region, wire, tail, _, erased⟩ := prepared_prefix admitted.header prepared
  exact SigmaSteps.prefix_fresh_receive _ erased _ earlier [] _ (fun ref => inputs.get ref)

/-- The actual prover entry queries first, computes the captured scale node
without an effect, and sends its result at site 1. The environment in this
equation is the actual entry input extended by the arbitrary service reply. -/
theorem prover_pure_commitment (generator : G1)
    (admitted : SubjectAdmission.Admitted BlsAdmission.installed subject)
    (arguments : Values (Component (BlsAdmission.interpretation generator admitted).Value 0)
      (closed admitted).entry.signature.arguments) :
    ∃ operation : (RegisteredVocabulary.vocabulary admitted.header 0).Op,
      BlsMeaning.payload admitted.header operation.val = BlsInstallation.Operation.scale ∧
      SigmaSteps.QueryPureSend (BlsAdmission.interpretation generator admitted) (fun ref => arguments.get ref)
        (closed admitted).entry.signature.results [] [2, 0]
        (.operation operation [0, 1] (.outputs [0])) (openMeaning generator admitted 0 arguments) := by
  refine (ClosedAssembly.Result.denote_satisfies admitted.header admitted.assembly
    (BlsAdmission.interpretation generator admitted) 0
    (fun key signature inputs execution => key = ClosedInstances.entryKey subject →
      ∃ operation : (RegisteredVocabulary.vocabulary admitted.header 0).Op,
        BlsMeaning.payload admitted.header operation.val = BlsInstallation.Operation.scale ∧
        SigmaSteps.QueryPureSend (BlsAdmission.interpretation generator admitted) (fun ref => inputs.get ref)
          signature.results [] [2, 0] (.operation operation [0, 1] (.outputs [0])) execution) ?_ arguments) rfl
  intro records key node prepared earlier inputs same
  subst key
  obtain ⟨region, wire, tail, regionEq, erased⟩ := prepared_prefix admitted.header prepared
  obtain ⟨operation, payload, capturesEq, graphEq⟩ := commitment_lower admitted.header _ region regionEq
  refine ⟨operation, payload, ?_⟩
  rw [capturesEq, graphEq] at erased
  exact SigmaSteps.prefix_pure_send _ erased _ earlier [] _ (fun ref => inputs.get ref)

end Semantics
end Examples.Mathematical.SigmaSubject
