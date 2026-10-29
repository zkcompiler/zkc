import ZkcExamples.NativePrograms.Schnorr
import ZkcExamples.NativePrograms.Sumcheck

/-! Common clients now observe the single Structured participant semantics.
The former flat-program-to-region lowering has been retired. These controls
retain the actual-source arbitrary-handler and input-availability boundaries.
Present-input certificates do not assert arbitrary-input validity. -/

set_option autoImplicit false
noncomputable section
namespace Tests.CommonRegion
open Zkc.Source Zkc.Source.Structured PIR
open ZkcExamples.NativePrograms

variable {F G : Type} [Field F] [DecidableEq F]
  [AddCommGroup G] [Module F G] [DecidableEq G]

/-- Equality quantifies over arbitrary replies, stops, events and handler state. -/
theorem verifier_execution (base key : G) (service : Nat) {S E : Type}
    (handler : Handler (Schnorr.actions (F := F) (G := G)) S E) (state : S) :
    (Schnorr.verifier base key service).run handler state =
      (Schnorr.experiment (F := F) base key service).run handler state :=
  congrArg (fun process => process.run handler state)
    (Schnorr.verifier_correspondence base key service)

example {m : Type → Type} [Monad m] (base key : G) (service : Nat) {S E : Type}
    (handler : MonadHandler m (Schnorr.actions (F := F) (G := G)) S E) (state : S) :
    (Schnorr.verifier base key service).runM handler state =
      (Schnorr.experiment (F := F) base key service).runM handler state :=
  congrArg (fun process => process.runM handler state)
    (Schnorr.verifier_correspondence base key service)

/-- Missing service stops only after the independent commitment is received. -/
example (base key : G) :
    (Schnorr.program.participant F G 1
      (.cons (some base) (.cons (some key) (.cons none (.cons none (.cons none .nil)))))).bind
        (fun values => .done (values.get .here)) =
      .call (.receive (.group "bls12-381.g1") "label_636f6d6d69746d656e74_0" 0)
        (fun _ => .halt .incomplete) := by rfl

/-- A foreign role sees no action or exported output. -/
example (base key : G) (service : Nat) :
    Schnorr.program.participant F G 2 (Schnorr.verifierInputs base key service) =
      .done (.cons none .nil) := by rfl

/-- Output filtering occurs after execution: missing prover inputs still stop. -/
example (base key : G) (service : Nat) :
    Schnorr.program.participant F G 0 (Schnorr.verifierInputs base key service) =
      .halt .incomplete := by rfl

/-- The actual complete returned row is the source of the scalar observation. -/
theorem scalar_view (base key : G) (service : Nat) :
    ((Schnorr.program.participant F G 1 (Schnorr.verifierInputs base key service)).bind
      fun values => .done (values.get .here)).interpret CommonAdapter.project =
        Schnorr.experiment (F := F) base key service :=
  Schnorr.verifier_correspondence base key service

end Tests.CommonRegion
end
