import Tools.Interactive.CommitmentCodec

set_option autoImplicit false

namespace Tests.CommitmentCodec
open Tools.Interactive
open Tools.Artifact (magic little)

private def identity : CommitmentIdentity :=
  ⟨2, ByteArray.mk (Array.replicate 32 13), ByteArray.mk (Array.replicate 32 29)⟩

private def wire (proof : Bool) (i : CommitmentIdentity) : ByteArray :=
  (magic.push (if proof then 7 else 6)) ++ "ZKCAR006".toUTF8 ++
    ByteArray.mk #[if proof then 3 else 2] ++ little 8 i.rank ++ i.setup ++ i.key ++
    ByteArray.mk (Array.replicate (if proof then 96*i.rank else 48) 0)

-- Dummy point bytes test the structural boundary only; subgroup validity stays
-- external and is not established by the shape decoder.
example : (CommitmentIdentity.decode identity.json).map (· == identity) = .ok true := by native_decide
example : (CommitmentIdentity.fromWire "commitment" (wire false identity)).map (· == identity) = .ok true := by native_decide
example : (CommitmentIdentity.fromWire "proof" (wire true identity)).map (· == identity) = .ok true := by native_decide
example : (CommitmentIdentity.fromWire "proof" (wire false identity)).map (fun _ => ()) =
    .error "wire-header" := by native_decide
example : (CommitmentIdentity.fromWire "commitment" ((wire false identity).push 0)).map (fun _ => ()) =
    .error "pcs-length" := by native_decide
example : (CommitmentIdentity.fromWire "commitment" (wire false { identity with rank := 0 })).map (fun _ => ()) =
    .error "pcs-rank" := by native_decide
example : identity.matches { identity with rank := 1, key := ByteArray.empty } =
    .error "arity-mismatch" := by native_decide
example : identity.matches { identity with key := ByteArray.mk (Array.replicate 32 30) } =
    .error "key-mismatch" := by native_decide
example : identity.matches { identity with setup := ByteArray.mk (Array.replicate 32 14) } =
    .error "key-mismatch" := by native_decide

end Tests.CommitmentCodec
