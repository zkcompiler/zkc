module

public import ZkcExamples.Executable.SumcheckMetadata
public import ZkcExamples.Executable.SumcheckHelpers
public import Zkc.Executable.HelperSchemas
public import Zkc.Executable.DomainNativeByteTransport
public import Zkc.Executable.DomainNormalizationSoundness
public import Zkc.Executable.DomainVerifierTransport
public import ZkcExamples.Construction.SumcheckProof
public meta import Zkc.Construction.ArtifactBindingTactic

@[expose] public section

/-! Interpreted bytes, canonical metered execution and authored source
acceptance. No relation, honesty or codec premise restricts the byte bridge. -/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
namespace ZkcExamples.Executable.SumcheckProof
open Zkc Zkc.Construction Zkc.Executable Zkc.Source
open ZkcExamples.Construction
open Zkc.Construction.Uniform.DomainAdapter

/-- The constructed validator calls the Pending constructor, both consuming wrappers,
the point extension and terminal check by name. -/
theorem helpers_named : Instruction.helpers SumcheckProof.participant.instructions =
    [ZkcExamples.Structured.SumcheckPendingBodies.pendingHelper.name,
      ZkcExamples.Structured.SumcheckPendingBodies.openClaimHelper.name,
      ZkcExamples.Structured.SumcheckHelperBodies.appendHelper.name,
      ZkcExamples.Structured.SumcheckPendingBodies.atPrefixHelper.name,
      ZkcExamples.Structured.SumcheckHelperBodies.checkHelper.name] :=
  helpers

/-- The helper calls of the constructed validator, at the result sorts of the
called helpers. -/
theorem calls : Instruction.callList SumcheckProof.participant.instructions =
    [ZkcExamples.Structured.SumcheckPendingBodies.pendingHelper,
      ZkcExamples.Structured.SumcheckPendingBodies.openClaimHelper,
      ZkcExamples.Structured.SumcheckHelperBodies.appendHelper,
      ZkcExamples.Structured.SumcheckPendingBodies.atPrefixHelper,
      ZkcExamples.Structured.SumcheckHelperBodies.checkHelper].map
      fun helper => (helper.name, helper.outputs.map .data) := by
  decide +kernel

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- Every helper the reading calls is prepared. -/
theorem prepared : ∀ name ∈ Instruction.helpers SumcheckProof.participant.instructions,
    Prepared installed validator (helperTable SumcheckProof.program F G) name := by
  rw [helpers_named]
  exact SumcheckHelpers.prepared

/-- Every helper the reading calls returns values of its declared result sorts. -/
theorem helpersSorted : ∀ call ∈ Instruction.callList SumcheckProof.participant.instructions,
    HelperSorted (helperTable SumcheckProof.program F G) call.1 call.2 := by
  have sorted : ∀ (helper : Zkc.Source.Structured.Helper) {body},
      Zkc.Source.Structured.BodyIn ZkcExamples.Structured.SumcheckSourceViews.unit.definitions helper body →
      HelperSorted (helperTable SumcheckProof.program F G) helper.name (helper.outputs.map .data) := by
    intro helper body association
    apply helperSorted_of_outputs
    intro entry found
    obtain ⟨entry', found', same⟩ :=
      Zkc.Source.Structured.Evaluation.linked_lookup (F := F) (G := G)
        (interface := Zkc.Source.Structured.closedInterface) .closed
        SumcheckProof.program.payload.linked helper (SumcheckHelpers.present association)
    change (helperTable SumcheckProof.program F G).find? (fun value => value.helper.name == helper.name) =
      some entry' at found'
    rw [found] at found'
    cases found'
    rw [same]
  rw [calls]
  intro call member
  simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact sorted _ ZkcExamples.Structured.SumcheckSourceAssociations.pending_association
  · exact sorted _ ZkcExamples.Structured.SumcheckSourceAssociations.openClaim_association
  · exact sorted _ ZkcExamples.Structured.SumcheckSourceContracts.bodies.append
  · exact sorted _ ZkcExamples.Structured.SumcheckSourceAssociations.atPrefix_association
  · exact sorted _ ZkcExamples.Structured.SumcheckSourceAssociations.check_association


/-- Finite nominal admission of the actual native reading. -/
def nativeScope : DomainVM.NativeScope :=
  (DomainVM.checkNativeCode SumcheckProof.program SumcheckProof.context lowered.code
    (DomainVM.nativeEntryScope validator)).get (by decide +kernel)

theorem native_checked : DomainVM.checkNativeLowering SumcheckProof.program SumcheckProof.context
    installed SumcheckProof.participant validator = .ok (lowered, nativeScope) := by
  kernel_rfl

theorem domain_prepared : ∀ name ∈ Instruction.helperList SumcheckProof.participant.instructions,
    Prepared installed validator (Domain.helperTable (Structured.ringModel F G) SumcheckProof.program) name := by
  rw [Domain.Binding.helperTable_ringModel]
  change ∀ name ∈ Instruction.helperList SumcheckProof.participant.instructions,
    Prepared installed validator (Zkc.Construction.helperTable SumcheckProof.program F G) name
  rw [Instruction.helperList_eq, helpers_named]
  exact SumcheckHelpers.prepared

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
def nominalInputs (values : List F) (claim : F) (rounds : Nat) : DomainVM.Environment F G :=
  [.data (.vector "bls12-381.fr" values), .data (.field "bls12-381.fr" claim), .data (.index rounds)]

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem embedded (values : List F) (claim : F) (rounds : Nat) :
    embedValues (SumcheckProof.inputs (G := G) values claim rounds) =
      some (nominalInputs values claim rounds) := rfl

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- The actual public input row followed by the profile's transcript input. -/
def physicalInputs (values : List F) (claim : F) (rounds : Nat)
    (history : Domain.History (Structured.uniformCarriers F G)) : DomainVM.Environment F G :=
  Domain.inputFrame SumcheckProof.context (nominalInputs values claim rounds) history

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem input_schema (values : List F) (claim : F) (rounds : Nat) :
    (physicalInputs (G := G) values claim rounds []).map Domain.Value.sort =
      SumcheckProof.participant.inputs := rfl

theorem return_schema : DomainVM.ReturnSchema SumcheckProof.participant := by decide +kernel

theorem scalar_origin : ScalarVerifier.origin SumcheckProof.participant = Origin.withoutCoordinates := rfl

theorem normalized (values : List F) (claim : F) (rounds : Nat) :
    DomainVM.observation SumcheckProof.program SumcheckProof.context
      (Code.instructions lowered.code) lowered.returned (physicalInputs (G := G) values claim rounds []) =
    DomainVM.observation SumcheckProof.program SumcheckProof.context
      SumcheckProof.participant.instructions SumcheckProof.participant.returned
      (physicalInputs values claim rounds []) := by
  apply CanonicalNormalization.accepted_sound
  · simpa only [Code.instructionList_eq] using (checkLowering_checks accepted).2.2.2.2.2.2
  · exact input_schema values claim rounds

/-- Exact all-budget observation for arbitrary typed inputs, bytes and codecs. -/
theorem executable_metered {m : Type → Type} [Monad m] [LawfulMonad m]
    (challenge : History F G → m F) (decode : PhysicalType → List UInt8 → Option (Payload F G))
    (budget : Nat) (values : List F) (claim : F) (rounds : Nat) (initial : History F G)
    (bytes : List UInt8) :
    Run.observe <$> execute installed validator SumcheckProof.context challenge decode budget
        (SumcheckProof.inputs values claim rounds) initial bytes =
      DomainVM.nativeObservation SumcheckProof.context.suite Origin.withoutCoordinates initial <$>
        DomainVM.metered SumcheckProof.program SumcheckProof.context Origin.withoutCoordinates initial challenge
          (helperCost installed validator) budget lowered (physicalInputs values claim rounds [])
          (decodeProof decode (Plan.types (SumcheckProof.inputs (G := G) values claim rounds) lowered.plan) bytes) :=
  DomainVM.checked_execute_metered SumcheckProof.program SumcheckProof.context initial challenge
    installed SumcheckProof.participant validator decode budget domain_prepared lowered nativeScope native_checked
    (SumcheckProof.inputs values claim rounds) bytes (admitted values claim rounds)
    (nominalInputs values claim rounds) (embedded values claim rounds)

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- Source verdict: the selected Boolean and an empty unread proof. -/
def accepting (result : PIR.Outcome (Option Bool) × Proof F G) : Bool :=
  match result.1, result.2 with
  | .returned (some decision), [] => decision
  | _, _ => false

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem nominal_accepting (result : PIR.Outcome (DomainVM.Environment F G) × Proof F G) :
    DomainVM.nominalAcceptance SumcheckProof.acceptancePosition result =
      accepting (mapOutcome (fun values => ScalarVerifier.acceptance SumcheckProof.acceptancePosition ⟨values, []⟩)
        result.1, result.2) := by
  rcases result with ⟨outcome, unread⟩
  cases outcome with
  | stopped => rfl
  | returned values =>
    simp only [DomainVM.nominalAcceptance, DomainVM.nominalSelected, ScalarVerifier.acceptance, mapOutcome]
    cases values[SumcheckProof.acceptancePosition]? with
    | none => cases unread <;> rfl
    | some value =>
      cases value with
      | transcript | indices => cases unread <;> rfl
      | data payload =>
        rcases payload with ⟨ty, allowed, contents⟩
        cases ty <;> cases unread <;> try rfl

/-- Fixed byte-pruning endpoint: actual participant execution on the published
inputs and actual Plan decoding, for all budgets and arbitrary framed bytes. -/
theorem domain_prunes {m : Type → Type} [Monad m] [LawfulMonad m]
    (challenge : History F G → m F) (decode : PhysicalType → List UInt8 → Option (Payload F G))
    (budget : Nat) (binding : List UInt8) (values : List F) (claim : F) (rounds : Nat)
    (initial : History F G) (bytes : List UInt8) :
    Prunes (fun accepted => accepted = false)
      (validate installed validator SumcheckProof.context challenge decode budget binding
        SumcheckProof.acceptancePosition (SumcheckProof.inputs values claim rounds) initial bytes)
      (accepting <$> ScalarVerifier.verify SumcheckProof.program SumcheckProof.context SumcheckProof.participant
        SumcheckProof.acceptancePosition challenge (SumcheckProof.inputs values claim rounds) initial
        (decodeProof decode (Plan.types (SumcheckProof.inputs (G := G) values claim rounds) lowered.plan) (bytes.drop 40))) := by
  conv_rhs =>
    rw [DomainVM.verifier_observation _ _ _ _ _ _
      (physicalInputs values claim rounds []) rfl
      (input_schema values claim rounds) return_schema, scalar_origin, Functor.map_map]
    simp only [← nominal_accepting]
    rw [← normalized values claim rounds]
  exact DomainVM.checked_validate_prunes SumcheckProof.program SumcheckProof.context initial challenge
    installed SumcheckProof.participant validator decode budget domain_prepared lowered nativeScope native_checked
    binding SumcheckProof.acceptancePosition (SumcheckProof.inputs values claim rounds) bytes
    (admitted values claim rounds) (nominalInputs values claim rounds) (embedded values claim rounds)

/-- The byte endpoint composed with the authored source Fiat–Shamir transform. -/
theorem executable_transform_prunes {m : Type → Type} [Monad m] [LawfulMonad m]
    (challenge : History F G → m F) (decode : PhysicalType → List UInt8 → Option (Payload F G))
    (budget : Nat) (binding : List UInt8) (values : List F) (claim : F) (rounds handle : Nat)
    (initial : History F G) (bytes : List UInt8) :
    Prunes (fun accepted => accepted = false)
      (validate installed validator SumcheckProof.context challenge decode budget binding
        SumcheckProof.acceptancePosition (SumcheckProof.inputs values claim rounds) initial bytes)
      (accepting <$> transform SumcheckProof.context challenge
        (SumcheckProof.verifier values claim rounds handle) initial
        (decodeProof decode (receives rounds) (bytes.drop 40))) := by
  conv_rhs =>
    rw [← SumcheckProof.compiled_transform challenge values claim rounds handle initial,
      SumcheckProof.compiledVerifier, ← plan_types (G := G) values claim rounds]
  exact domain_prunes challenge decode budget binding values claim rounds initial bytes

end ZkcExamples.Executable.SumcheckProof
