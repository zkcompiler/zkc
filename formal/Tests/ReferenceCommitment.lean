import Tools.Interactive.GenericReference

set_option autoImplicit false

namespace Tests.ReferenceCommitment
open Tools.Interactive
open Reference
open Lean (Json)

private def identity : CommitmentIdentity :=
  ⟨2, ByteArray.mk (Array.replicate 32 13), ByteArray.mk (Array.replicate 32 29)⟩
private def location : Location := Location.plain "test" "root" "site" "P"
private def initial : State := { setupKeys := [("P", [identity])] }

-- These zero point bytes test structural service contracts, not cryptography.
private def wire (proof : Bool) (key : CommitmentIdentity) : ByteArray :=
  (Tools.Artifact.magic.push (if proof then 7 else 6)) ++ "ZKCAR006".toUTF8 ++
    ByteArray.mk #[if proof then 3 else 2] ++ Tools.Artifact.little 8 key.rank ++ key.setup ++ key.key ++
    ByteArray.mk (Array.replicate (if proof then 96*key.rank else 48) 0)

private def summary (result : Except Fault (List Value) × State) : String :=
  match result.1 with
  | .ok values => (valuesJson values).compress
  | .error fault => fault.reason ++ ":" ++ fault.detail

private def serviceState (contract : String) (inputs : List Value) (outputs : List Value) : State :=
  { initial with answers := Std.HashMap.ofList [
      ((requestJson location contract ["multilinear.kzg.bls12-381/1"] [] inputs).compress,
        .arr #[.str "ok", valuesJson outputs])] }

private def probe (wrongKey : Bool) : String := Id.run do
  let .ok table := Math.Table.admit 2 [0,1,4,9] | return "bad table"
  let output := wire false (if wrongKey then { identity with key := ByteArray.mk (Array.replicate 32 30) } else identity)
  let committed := (commit location identity table).run
    (serviceState "pcs.commit" [.proverKey identity, .table table] [.commitment output])
  let .ok [.commitment bytes, .opening original] := committed.1 | return summary committed
  -- A valid response constructs exact custody rather than trusting a handle.
  if bytes != output || original.identity != identity || original.original.cells != table.cells then
    return "changed original"
  let request := [.opening original, .point [2,3]]
  let state := serviceState "pcs.open" request [.proof (wire true identity)]
  let (result, finalState) := (openCommitment location original [2,3]).run state
  if !finalState.resources.isEmpty then return "invented resource"
  match result with
  | .ok [.field value, .proof _] => return toString value.val
  | _ => return summary (result, finalState)

example : probe false = "35" := by native_decide
example : probe true = "refused:key-mismatch" := by native_decide

-- Key declarations remain role-scoped even though their identity is public.
example : authorized initial "P" (.proverKey identity) = .ok () := by native_decide
example : authorized initial "V" (.proverKey identity) = .error "unauthorized-setup" := by native_decide
example : (decodeValue (.arr #[.str "opening_state:multilinear.kzg.bls12-381/1", .arr #[]])).map
    (fun _ => ()) = .error "reference-value-not-supported" := by native_decide

private def duplicateSetup : Json := .arr #[.str "zkc.reference-setups/1",
  .arr #[.arr #[.str "P", .arr #[identity.json, identity.json]]], .arr #[]]
example : (setupContext ["P"] duplicateSetup).map (fun _ => ()) = .error "duplicate-setup" := by native_decide

private def receiving : Json := receiveKey location "commitment" "V" "commitment:multilinear.kzg.bls12-381/1"
private def receiveProbe (selected : Option CommitmentIdentity) : String :=
  summary ((do
    validateReceivingKey location receiving (.commitment (wire false identity))
    pure []).run { initial with receivingKeys := selected.toList.map fun key => (receiving, key) })
example : receiveProbe none = "refused:receiving-setup-missing" := by native_decide
example : receiveProbe (some { identity with rank := 1 }) = "refused:arity-mismatch" := by native_decide
example : receiveProbe (some { identity with key := ByteArray.mk (Array.replicate 32 30) }) =
    "refused:key-mismatch" := by native_decide
example : receiveProbe (some identity) = "[]" := by native_decide

end Tests.ReferenceCommitment
