import Tools.Artifact.Codec

/-! Public identity of the installed multilinear commitment scheme. Fingerprints
identify selected material; authorization and group validity are separate. This
decoder reuses the independent wire-shape codec, never the native backend.
-/

set_option autoImplicit false

namespace Tools.Interactive
open Lean (Json)

structure CommitmentIdentity where
  rank : Nat
  setup : ByteArray
  key : ByteArray
  deriving BEq

def CommitmentIdentity.json (identity : CommitmentIdentity) : Json :=
  .arr #[.str (toString identity.rank), .str (Tools.Artifact.hex identity.setup),
    .str (Tools.Artifact.hex identity.key)]

def CommitmentIdentity.decode (json : Json) : Result CommitmentIdentity := do
  let [rank, setup, key] ← Decode.array json | throw "pcs-identity"
  let rank ← Decode.natural rank
  ensure (0 < rank && rank ≤ limits.rank) "pcs-rank"
  let setup ← Tools.Artifact.unhex (← Decode.string setup)
  let key ← Tools.Artifact.unhex (← Decode.string key)
  ensure (setup.size == 32 && key.size == 32) "pcs-fingerprint-width"
  return ⟨rank, setup, key⟩

def CommitmentIdentity.fromWire (kind : String) (bytes : ByteArray) : Result CommitmentIdentity := do
  ensure (["commitment", "proof"].contains kind) "pcs-kind"
  let _ ← Tools.Artifact.decodeWire kind bytes
  return ⟨Tools.Artifact.valueLE (bytes.extract 15 23), bytes.extract 23 55, bytes.extract 55 87⟩

/-- Rank mismatch precedes setup/key mismatch in the installed contract. -/
def CommitmentIdentity.matches (expected actual : CommitmentIdentity) : Result Unit := do
  ensure (expected.rank == actual.rank) "arity-mismatch"
  ensure (expected.setup == actual.setup && expected.key == actual.key) "key-mismatch"

end Tools.Interactive
