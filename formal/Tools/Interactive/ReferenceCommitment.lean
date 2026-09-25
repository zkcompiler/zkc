import Tools.Interactive.ReferenceState

/-! Logical PCS custody and wrappers. External services compute commitment/proof
bytes and verification equations. They never provide private opening state or
polynomial evaluations. Exact requests retain the actual key and original.
-/

set_option autoImplicit false

namespace Tools.Interactive.Reference

private def outputIdentity (location : Location) (expected : CommitmentIdentity)
    (kind : String) (bytes : ByteArray) : RunM Unit := do
  let actual ← checked location (CommitmentIdentity.fromWire kind bytes)
  checked location (expected.matches actual)

def commit (location : Location) (key : CommitmentIdentity) (table : Math.Table) : RunM (List Value) := do
  checked location (authorized (← get) location.scope.role (.proverKey key))
  require location (key.rank == table.rank) "arity-mismatch"
  let [.commitment bytes] ← external location "pcs.commit" ["multilinear.kzg.bls12-381/1"] []
      [.proverKey key, .table table]
    | failAt location "refused" "primitive-response"
  outputIdentity location key "commitment" bytes
  return [.commitment bytes, .opening ⟨key, table, bytes⟩]

def openCommitment (location : Location) (state : OpeningState) (point : List Math.Fr) : RunM (List Value) := do
  checked location (authorized (← get) location.scope.role (.opening state))
  require location (state.identity.rank == point.length) "arity-mismatch"
  let value ← checked location (state.original.evaluate point)
  let [.proof bytes] ← external location "pcs.open" ["multilinear.kzg.bls12-381/1"] []
      [.opening state, .point point]
    | failAt location "refused" "primitive-response"
  outputIdentity location state.identity "proof" bytes
  return [.field value, .proof bytes]

def checkCommitment (location : Location) (key : CommitmentIdentity) (commitment : ByteArray)
    (point : List Math.Fr) (value : Math.Fr) (proof : ByteArray) : RunM (List Value) := do
  for input in [Value.verifierKey key, .commitment commitment, .proof proof] do
    checked location (authorized (← get) location.scope.role input)
  outputIdentity location key "commitment" commitment
  outputIdentity location key "proof" proof
  require location (key.rank == point.length) "arity-mismatch"
  let [.boolean accepted] ← external location "pcs.check" ["multilinear.kzg.bls12-381/1"] []
      [.verifierKey key, .commitment commitment, .point point, .field value, .proof proof]
    | failAt location "refused" "primitive-response"
  return [.boolean accepted]

end Tools.Interactive.Reference
