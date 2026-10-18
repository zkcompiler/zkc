module

public import ZkcExamples.NativePrograms.Schnorr
public import Zkc.Specification

@[expose] public section

/-! A downstream consumer adds a property without changing the compiler,
contract, source certificate, or Python registry. The typed API is extensible;
the bounded command-line generator deliberately has a reviewed registry. -/

namespace ZkcExamples.NativePrograms.CustomProperty
open Zkc.Verification Zkc.Source Zkc.Source.Common Zkc.Source.Common.Native
open Zkc.Protocols.Schnorr.Common

def source : Zkc.Verification.Imported Snapshot.check SchnorrData.snapshot :=
  ⟨Schnorr.imported, by rfl⟩

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G]
  [Module F G] [DecidableEq G]

def denote (program : Zkc.Source.Common.Native.Imported) : Verifier F G :=
  fun base key service =>
    if same : program.snapshot.inputs = SchnorrData.snapshot.inputs then
      if result : program.snapshot.result = .boolean then
        cast (congrArg (fun ty => PIR.Proc (actions (F := F) (G := G))
          (Option (ScalarValue F G ty))) result)
          (program.denote (scalarMeaning F G) id 1
            (same ▸ Schnorr.verifierInputs (F := F) base key service))
      else .halt .refused
    else .halt .refused

theorem sourceCertificate : Certificate source (denote (F := F) (G := G))
    (VerifierContract Schnorr.wiring) :=
  ⟨Schnorr.contract⟩

/-- An extension selects a precisely stated property, not a theorem name inferred
from the source text. Here an invalid response equation must not accept. -/
def rejectionProperty (base key : G) (service : Nat) (prover : Strategy F G)
    (challenge : F) : Property (Verifier F G) where
  assumptions _ := prover.response challenge • base ≠ prover.commitment + challenge • key
  conclusion program :=
    (run program base key service prover challenge).outcome ≠ .returned (some true)

omit [DecidableEq F] in
theorem rejectionConsumer (wiring : Wiring) (base key : G) (service : Nat)
    (prover : Strategy F G) (challenge : F) :
    Consumer (VerifierContract wiring) (rejectionProperty base key service prover challenge) := by
  constructor
  intro program contract different accepts
  exact different ((contract.accepted_iff base key service prover challenge).mp accepts)

/-- The generic certificate API composes source admission with a new consumer. -/
theorem imported_rejects (base key : G) (service : Nat) (prover : Strategy F G)
    (challenge : F) :
    (rejectionProperty base key service prover challenge).assumptions (denote source.program) →
    (rejectionProperty base key service prover challenge).conclusion (denote source.program) :=
  sourceCertificate.verify (rejectionConsumer Schnorr.wiring base key service prover challenge)

end ZkcExamples.NativePrograms.CustomProperty
