module

public import ZkcExamples.NativePrograms.Schnorr
public import ZkcExamples.NativePrograms.SchnorrHelpers
public import ZkcExamples.NativePrograms.SchnorrReordered

@[expose] public section

/-! Several native source forms share one semantic contract and its property theorems. -/

set_option autoImplicit false
noncomputable section

namespace ZkcExamples.NativePrograms.SchnorrVariants
open Zkc.Source Zkc.Source.Common Zkc.Source.Common.Native

inductive Form where
  | original | helpers | reordered

variable {F G : Type} [Field F] [DecidableEq F]
    [AddCommGroup G] [Module F G] [DecidableEq G]

abbrev helpers := SchnorrHelpers.verifier (F := F) (G := G)
abbrev reordered := SchnorrReordered.verifier (F := F) (G := G)

def verifier (form : Form) : Zkc.Protocols.Schnorr.Common.Verifier F G :=
  match form with
  | .original => Schnorr.verifier
  | .helpers => helpers
  | .reordered => reordered

theorem helpers_correspondence (base key : G) (service : Nat) :
    helpers (F := F) base key service = Schnorr.experiment (F := F) base key service :=
  (SchnorrHelpers.process_view_eq base key service).trans (SchnorrHelpers.correspondence base key service)

theorem reordered_correspondence (base key : G) (service : Nat) :
    reordered (F := F) base key service = Schnorr.experiment (F := F) base key service :=
  (SchnorrReordered.process_view_eq base key service).trans (SchnorrReordered.correspondence base key service)

theorem contract (form : Form) : Zkc.Protocols.Schnorr.Common.VerifierContract Schnorr.wiring (verifier (F := F) (G := G) form) := by
  cases form with
  | original => exact Schnorr.contract
  | helpers => exact ⟨fun base key service => ⟨helpers_correspondence base key service⟩⟩
  | reordered => exact ⟨fun base key service => ⟨reordered_correspondence base key service⟩⟩

abbrev run (form : Form) := Zkc.Protocols.Schnorr.Common.run (verifier (F := F) (G := G) form)

open Schnorr

theorem perfect_completeness (form : Form) (base : G) (secret nonce challenge : F) (service : Nat) :
    (run form base (secret • base) service ⟨nonce • base, fun c => nonce + c * secret⟩ challenge).outcome =
      .returned (some true) := by
  exact (contract form).perfect_completeness base secret nonce challenge service

theorem special_soundness (form : Form) (base key : G) (service : Nat) (prover : Strategy F G)
    (first second : F) (distinct : first ≠ second)
    (acceptFirst : (run form base key service prover first).outcome = .returned (some true))
    (acceptSecond : (run form base key service prover second).outcome = .returned (some true)) :
    ((prover.response first - prover.response second) / (first - second)) • base = key := by
  exact (contract form).special_soundness base key service prover first second distinct acceptFirst acceptSecond

end ZkcExamples.NativePrograms.SchnorrVariants

end
