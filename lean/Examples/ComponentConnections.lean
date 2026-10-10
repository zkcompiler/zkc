import Zkc.Realization.Acceptance

/-! A non-machine proof/signature/commitment connection.

The cryptographic primitives below are parameters, not implementations or
security assumptions proved here. Component predicates bind the actual public
subject. This client proves how their contracts connect and change boundary
representation; it is not an Orchard or Zcash protocol implementation.
-/

namespace Examples.ComponentConnections

open PIR.Relation Zkc.Realization

structure Statement (Key Message Commitment Signature : Type) where
  key : Key
  message : Message
  commitment : Commitment
  signature : Signature

variable {Key Secret Message Blind Commitment Signature EncodedKey : Type}

def proofFamily (keyOf : Secret → Key) (commit : Message → Blind → Commitment)
    (message : Message) : Family where
  Statement := Key × Commitment
  Witness := Secret × Blind
  holds boundary witness := keyOf witness.1 = boundary.1 ∧
    commit message witness.2 = boundary.2

def proofAccepts (keyOf : Secret → Key) (commit : Message → Blind → Commitment)
    (input : Statement Key Message Commitment Signature) (boundary : Key × Commitment) : Prop :=
  boundary.1 = input.key ∧ boundary.2 = input.commitment ∧
    Valid (proofFamily keyOf commit input.message) boundary

def proofConstraints (keyOf : Secret → Key) (commit : Message → Blind → Commitment)
    (input : Statement Key Message Commitment Signature) (boundary : Key × Commitment)
    (witness : Secret × Blind) : Prop :=
  boundary.1 = input.key ∧ boundary.2 = input.commitment ∧
    (proofFamily keyOf commit input.message).holds boundary witness

theorem proof_realization (keyOf : Secret → Key) (commit : Message → Blind → Commitment) :
    Acceptance (proofAccepts (Signature := Signature) keyOf commit)
      (proofConstraints keyOf commit) where
  sound _ _ witness h := ⟨h.1, h.2.1, witness, h.2.2⟩
  complete _ _ h := by
    obtain ⟨witness, hw⟩ := h.2.2
    exact ⟨witness, h.1, h.2.1, hw⟩

def signatureAccepts (verify : Key → Message → Signature → Bool)
    (input : Statement Key Message Commitment Signature) (boundary : Key × Message) : Prop :=
  boundary.2 = input.message ∧ verify boundary.1 boundary.2 input.signature = true

def signatureConstraints (verify : Key → Message → Signature → Bool)
    (input : Statement Key Message Commitment Signature) (boundary : Key × Message)
    (_ : Unit) : Prop := signatureAccepts verify input boundary

theorem signature_realization (verify : Key → Message → Signature → Bool) :
    Acceptance (signatureAccepts (Commitment := Commitment) verify) (signatureConstraints verify) where
  sound _ _ _ h := h
  complete _ _ h := ⟨(), h⟩

/-- The proof and signature share a key, while their other boundary fields
differ. Each component also binds its own part of the actual statement. -/
theorem connected_realization (keyOf : Secret → Key) (commit : Message → Blind → Commitment)
    (verify : Key → Message → Signature → Bool)
    (input : Statement Key Message Commitment Signature) :
    Connected (fun b => ∃ w, proofConstraints keyOf commit input b w)
        (fun proof signed => proof.1 = signed.1)
        (fun b => ∃ w, signatureConstraints verify input b w) ↔
      Connected (proofAccepts keyOf commit input)
        (fun proof signed => proof.1 = signed.1) (signatureAccepts verify input) :=
  (proof_realization keyOf commit).connected (signature_realization verify)
    (fun _ proof signed => proof.1 = signed.1) input

/-- Re-encode just the signature's key and adapt the connector. The concrete
section supplies coverage here; no shared storage layout is introduced. -/
theorem reencoded_signature (keyOf : Secret → Key) (commit : Message → Blind → Commitment)
    (verify : Key → Message → Signature → Bool)
    (encode : Key → EncodedKey) (decode : EncodedKey → Key)
    (sectionLaw : ∀ key, decode (encode key) = key)
    (input : Statement Key Message Commitment Signature) :
    Connected (proofAccepts keyOf commit input)
        (fun proof (signed : EncodedKey × Message) => proof.1 = decode signed.1)
        (fun signed => ∃ b, signatureAccepts verify input b ∧ signed = (encode b.1, b.2)) ↔
      Connected (proofAccepts keyOf commit input)
        (fun proof signed => proof.1 = signed.1) (signatureAccepts verify input) := by
  apply Connected.represented
    (proofAccepts keyOf commit input) (signatureAccepts verify input)
    _ _ (fun a u => a = u) (fun b v => v = (encode b.1, b.2))
  · intro a _; exact ⟨a, rfl⟩
  · intro b _; exact ⟨(encode b.1, b.2), rfl⟩
  · intro u; exact ⟨fun h => ⟨u, h, rfl⟩, fun ⟨a, h, eqv⟩ => eqv ▸ h⟩
  · intro v; rfl
  · intro a b u v _ _ hau hbv
    subst u; subst v
    simp [sectionLaw]

/-- The supplied signature can verify for a different key even when the proof
component is inhabited. The actual connector rejects that subject mismatch. -/
theorem mismatched_signing_key :
    let input : Statement Bool Unit Unit Bool := ⟨false, (), (), true⟩
    let proof := proofAccepts (fun key : Bool => key) (fun (_ : Unit) (_ : Unit) => ()) input
    let signed := signatureAccepts (fun key (_ : Unit) signature => decide (key = signature)) input
    (∃ b, proof b) ∧ (∃ b, signed b) ∧
      ¬ Connected proof (fun a b => a.1 = b.1) signed := by
  dsimp
  refine ⟨⟨(false, ()), rfl, rfl, (false, ()), rfl, rfl⟩,
    ⟨(true, ()), rfl, rfl⟩, ?_⟩
  rintro ⟨a, b, ha, hab, hb⟩
  have keyFalse : b.1 = false := hab.symm.trans ha.1
  have keyTrue : b.1 = true := of_decide_eq_true hb.2
  cases keyFalse.symm.trans keyTrue

end Examples.ComponentConnections
