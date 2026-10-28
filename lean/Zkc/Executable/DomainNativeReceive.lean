module

public import Zkc.Executable.DomainNativeBytes
public import Zkc.Executable.DomainNativeCodeScope

@[expose] public section

/-! Arbitrary-byte native receive correspondence at every budget. Decoder
failures are observed as refusals, while successful decoding continues with
its actual nominal payload and the physical plan for the remaining bytes. -/
set_option autoImplicit false
namespace Zkc.Executable.DomainVM
open Zkc.Construction Zkc.Source Zkc.Construction.Uniform
variable {F G : Type}

 theorem decode_payload_none (ty : Structured.Ty) (payload : Payload F G)
    (different : ty ≠ payloadType payload) : Value.decode ty (.data payload) = none := by
  cases payload <;> cases ty <;> simp_all [Value.decode, payloadType]

 theorem scalarType_data (ty : Structured.Ty) (eligible : (scalarType ty).isSome = true) :
    Domain.dataType ty = true := by
  cases ty <;> simp_all [scalarType, Domain.dataType, Structured.Ty.isHandle]

variable [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
variable {m : Type → Type} [Monad m]

theorem receive_payload {R : Type} (program : Structured.Program) (context : Context)
    (key : Origin → Origin) (initial : History F G) (challenge : History F G → m F)
    (site peer : String) (env : Environment F G) (payload : Payload F G) (proof : Proof F G)
    (next : Environment F G → Proof F G → m (PIR.Outcome R × Proof F G)) :
    DomainAdapter.runK key initial challenge
      (Domain.step (Structured.ringModel F G) program context
        ⟨.receive site site peer (payloadType payload), [], [.data (payloadType payload)], []⟩ env)
      (payload :: proof) next = next (env ++ [.data (DomainAdapter.embedPayload payload)]) proof := by
  cases payload <;> simp [Domain.step, Domain.dataType, payloadType, DomainAdapter.runK,
    Value.decode, Domain.Value.encode, Domain.Payload.ofValue, Domain.sortsMatch,
    Domain.Value.sort, DomainAdapter.embedPayload, Structured.Ty.isHandle]

theorem receive_wrong_payload {R : Type} (program : Structured.Program) (context : Context)
    (key : Origin → Origin) (initial : History F G) (challenge : History F G → m F)
    (site peer : String) (ty : Structured.Ty) (eligible : (scalarType ty).isSome = true)
    (env : Environment F G) (payload : Payload F G) (proof : Proof F G)
    (different : ty ≠ payloadType payload)
    (next : Environment F G → Proof F G → m (PIR.Outcome R × Proof F G)) :
    DomainAdapter.runK key initial challenge
      (Domain.step (Structured.ringModel F G) program context
        ⟨.receive site site peer ty, [], [.data ty], []⟩ env) (payload :: proof) next =
      pure (.stopped .refused, payload :: proof) := by
  rw [Domain.Correspondence.receive, Domain.View.receive_eq site peer ty env (scalarType_data ty eligible)]
  simp only [DomainAdapter.runK, decode_payload_none ty payload different]

theorem receive_empty {R : Type} (program : Structured.Program) (context : Context)
    (key : Origin → Origin) (initial : History F G) (challenge : History F G → m F)
    (site peer : String) (ty : Structured.Ty) (eligible : (scalarType ty).isSome = true)
    (env : Environment F G)
    (next : Environment F G → Proof F G → m (PIR.Outcome R × Proof F G)) :
    DomainAdapter.runK key initial challenge
      (Domain.step (Structured.ringModel F G) program context
        ⟨.receive site site peer ty, [], [.data ty], []⟩ env) [] next = pure (.stopped .refused, []) := by
  rw [Domain.Correspondence.receive, Domain.View.receive_eq site peer ty env (scalarType_data ty eligible)]
  rfl

/-- The actual native receive and the canonical metered step have the same
observation for every decoder, raw byte string and budget. The sole CPS
premise is the induction hypothesis at successfully received actual payloads. -/
theorem native_receive_metered [LawfulMonad m]
    (program : Structured.Program) (context : Context) (key : Origin → Origin)
    (initial : History F G) (challenge : History F G → m F)
    (vocabulary : Vocabulary) (validator : Validator)
    (decode : PhysicalType → List UInt8 → Option (Payload F G))
    (cost : String → List (Value F G) → Nat) (budget : Nat)
    (site peer output : String) (physical : PhysicalType) (ty : Structured.Ty)
    (physicalSort : physical.sort = .data ty) (eligible : (scalarType ty).isSome = true)
    (state : State F G) (env : Environment F G) (after : List PhysicalType)
    (next : State F G → m (Run F G))
    (exit : List (Value F G) → State F G → m (Run F G))
    (continuation : Environment F G → Proof F G → Nat → m (PIR.Outcome (Environment F G) × Proof F G))
    (continues : ∀ encoded unread payload,
      readFrame state.proof = some (encoded, unread) → decode physical encoded = some payload →
      physical.sort = .data (payloadType payload) →
      Run.observe <$> next
        ({ state with used := state.used + 1, proof := unread, messages := state.messages + 1 }.bind
          [output] [.data payload]) =
        nativeObservation context.suite key initial <$>
          continuation (env ++ [.data (DomainAdapter.embedPayload payload)])
            (decodeProof decode after unread) (state.used + 1)) :
    Run.observe <$> Executable.runStep vocabulary validator context challenge decode budget
      (.receive site site peer output physical) state next exit =
      nativeObservation context.suite key initial <$>
        meteredStep program context key initial challenge cost budget
          (.step ⟨.receive site site peer ty, [], [.data ty], []⟩ 1) env
          (decodeProof decode (physical :: after) state.proof) state.used continuation := by
  simp only [Executable.runStep, meteredStep]
  by_cases available : state.used < budget
  · have fits : state.used + 1 ≤ budget := by omega
    simp only [available, fits, ite_true]
    cases framed : readFrame state.proof with
    | none => simp [decodeProof, framed, receive_empty program context key initial challenge site peer ty eligible]
    | some pair =>
      rcases pair with ⟨encoded, unread⟩
      cases decoded : decode physical encoded with
      | none => simp [decodeProof, framed, decoded, receive_empty program context key initial challenge site peer ty eligible]
      | some payload =>
        by_cases typed : physical.sort = .data (payloadType payload)
        · have typeEq : ty = payloadType payload := ValueSort.data.inj (physicalSort.symm.trans typed)
          subst ty
          simp only [typed, ite_true, decodeProof, framed, decoded,
            receive_payload program context key initial challenge site peer env payload]
          exact continues encoded unread payload framed decoded typed
        · have different : ty ≠ payloadType payload := by intro same; apply typed; simpa [same] using physicalSort
          simp [typed, decodeProof, framed, decoded,
            receive_wrong_payload program context key initial challenge site peer ty eligible env payload _ different]
  · have short : ¬ state.used + 1 ≤ budget := by omega
    simp [available, short, nativeObservation, DomainAdapter.readbackOutcome, Executable.observation]

end Zkc.Executable.DomainVM
