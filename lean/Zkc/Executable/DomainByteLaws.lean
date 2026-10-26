module

public import Zkc.Executable.DomainProcesses
public import Zkc.Executable.Framing

@[expose] public section

/-! Arbitrary-byte receive and honest codec boundaries for the canonical
Process handler. A decoder may return any scalar payload, including the wrong
sort. Missing framing and failed decoding refuse; a wrong typed head remains
unread. No correctness premise on an adversarial decoder is used here. -/
set_option autoImplicit false
namespace Zkc.Executable.DomainVM
open Zkc.Construction Zkc.Source Zkc.Construction.Uniform
variable {F G : Type} {m : Type → Type} [Monad m]

/-- The unread sentinel represents any bytes remaining after the last planned
receive, without interpreting them as another well-typed message. -/
theorem decodeProof_unread (decode : PhysicalType → List UInt8 → Option (Payload F G))
    (bytes : List UInt8) :
    (decodeProof decode [] bytes).isEmpty = bytes.isEmpty := by
  simp only [decodeProof]
  split <;> simp_all

/-- Exact handler reduction at one native framing boundary, before any
assumption about the decoder or decoded payload sort. The continuation still
contains all later actions and failures. -/
theorem runK_receive_bytes {A R : Type}
    (key : Origin → Origin) (initial : History F G) (challenge : History F G → m F)
    (decode : PhysicalType → List UInt8 → Option (Payload F G))
    (physical : PhysicalType) (types : List PhysicalType) (bytes : List UInt8)
    (ty : Structured.Ty) (site schema peer : String)
    (continuation : Structured.assignment F G ty →
      PIR.Process (Domain.effects (Structured.uniformCarriers F G)) A)
    (next : A → Proof F G → m (PIR.Outcome R × Proof F G)) :
    DomainAdapter.runK key initial challenge
      (.call (.receive ty site schema peer) continuation)
      (decodeProof decode (physical :: types) bytes) next =
      (match readFrame bytes with
      | none => pure (.stopped .refused, [])
      | some (encoded, rest) => match decode physical encoded with
        | none => pure (.stopped .refused, [])
        | some payload => match Value.decode ty (.data payload) with
          | none => pure (.stopped .refused, payload :: decodeProof decode types rest)
          | some value => DomainAdapter.runK key initial challenge (continuation value)
              (decodeProof decode types rest) next) := by
  cases frameEq : readFrame bytes with
  | none => simp [decodeProof, frameEq, DomainAdapter.runK]
  | some frame =>
      rcases frame with ⟨encoded, rest⟩
      cases decoded : decode physical encoded <;>
        simp only [decodeProof, frameEq, decoded, DomainAdapter.runK]
      cases Value.decode ty (.data _) <;> rfl

/-- Honest framing is used at the same canonical handler, with explicit codec
and size contracts. This is a representation theorem, independent of whether
the participant ultimately returns or rejects. -/
theorem runK_frames {A R : Type}
    (key : Origin → Origin) (initial : History F G) (challenge : History F G → m F)
    (decode : PhysicalType → List UInt8 → Option (Payload F G))
    (encode : PhysicalType → Payload F G → List UInt8)
    (roundtrip : ∀ type payload, decode type (encode type payload) = some payload)
    (bounded : ∀ type payload, (encode type payload).length ≤ proofLimit)
    (types : List PhysicalType) (payloads : Proof F G) (lengths : types.length = payloads.length)
    (process : PIR.Process (Domain.effects (Structured.uniformCarriers F G)) A)
    (next : A → Proof F G → m (PIR.Outcome R × Proof F G)) :
    DomainAdapter.runK key initial challenge process
      (decodeProof decode types (frames encode types payloads)) next =
        DomainAdapter.runK key initial challenge process payloads next := by
  rw [decodeProof_frames decode encode roundtrip bounded types payloads lengths]

end Zkc.Executable.DomainVM
