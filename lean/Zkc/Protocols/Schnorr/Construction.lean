module

public import Zkc.Protocols.Schnorr.Common
public import Zkc.Semantics.Interpretation

@[expose] public section

/-! A concrete interpreted Schnorr construction with typed statement binding.

This is an ideal-oracle construction of an actual interactive process. It is
not a claim about a native byte codec or a particular hash implementation.
-/
namespace Zkc.Protocols.Schnorr.Construction
open Common
open Zkc.Source Zkc.Source.Common Zkc.Source.Common.Native

/-- All public inputs fixed before the adversary starts. Source and construction
identities separate domains; they do not certify the identified implementation. -/
structure Binding (Context G : Type) where
  source : String
  construction : String
  context : Context
  base : G
  key : G
  deriving DecidableEq

abbrev QueryKey (Context G : Type) := Binding Context G × G

def oracleSignature (Context F G : Type) : PIR.Signature :=
  ⟨QueryKey Context G, fun _ => F⟩

variable {Context F G : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq G]

/-- Proof transport is already decoded into a commitment and response. The
contract fixes the only reachable receive/query sites. Unsupported source
shapes receive no certificate just because this interpretation is total. -/
def operations (binding : Binding Context G) (proof : G × F) :
    PIR.OperationInterpretation (actions (F := F) (G := G))
      (oracleSignature Context F G)
  | .send .. => .done ()
  | .query .. => .call (binding, proof.1) .done
  | .receive ty .. => .done (match ty with
      | .boolean => false
      | .field _ => proof.2
      | .group _ => proof.1
      | .service _ => 0)

abbrev Verifier (Context F G : Type) :=
  Binding Context G → G × F → PIR.Proc (oracleSignature Context F G) (Option Bool)

/-- Construction acts on the supplied process, including its stops and results. -/
def construct (program : Common.Verifier F G) (service : Nat) : Verifier Context F G :=
  fun binding proof =>
    (program binding.base binding.key service).interpret (operations binding proof)

/-- The central process law is derived from the actual source certificate. -/
theorem construct_eq {wiring : Wiring} {program : Common.Verifier F G}
    (certificate : VerifierContract wiring program) (service : Nat)
    (binding : Binding Context G) (proof : G × F) :
    construct program service binding proof =
      .call (binding, proof.1) (fun (challenge : F) =>
        .done (some (decide (proof.2 • binding.base = proof.1 + challenge • binding.key)))) := by
  unfold construct
  rw [(certificate.realizes binding.base binding.key service).process_eq]
  rfl

/-- An external constructed carrier must prove this process equality under its
selected primitive meanings. No acceptance, probability or security is a field. -/
def Realizes (actual : Verifier Context F G) (program : Common.Verifier F G)
    (service : Nat) : Prop :=
  ∀ binding proof, PIR.ExactRefinement (actual binding proof)
    (construct program service binding proof)

omit [DecidableEq G] in
theorem construct_realizes (program : Common.Verifier F G) (service : Nat) :
    Realizes (construct (Context := Context) program service) program service :=
  fun _ _ => ⟨rfl⟩

omit [Field F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- Typed keys bind the entire public subject and current commitment. -/
theorem queryKey_eq_iff (left right : Binding Context G) (first second : G) :
    (left, first) = (right, second) ↔ left = right ∧ first = second :=
  by simp only [Prod.mk.injEq]

end Zkc.Protocols.Schnorr.Construction
