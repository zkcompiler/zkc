module

public import ZkcExamples.NativePrograms.Schnorr
public import ZkcExamples.NativePrograms.Variants.SchnorrHelpersData

public import ZkcExamples.NativePrograms.Variants.SchnorrReorderedData

@[expose] public section

/-! Several native source forms share one semantic contract and its property theorems. -/

set_option autoImplicit false

namespace ZkcExamples.NativePrograms.SchnorrVariants
open Zkc.Source Zkc.Source.Common Zkc.Source.Common.Native

inductive Form where
  | original | helpers | reordered

def helpersImport : Imported := Variants.SchnorrHelpersData.snapshot.check.toOption.get (by decide +kernel)

def reorderedImport : Imported := Variants.SchnorrReorderedData.snapshot.check.toOption.get (by decide +kernel)

variable {F G : Type} [Field F] [DecidableEq F]
    [AddCommGroup G] [Module F G] [DecidableEq G]

def helpers (base key : G) (service : Nat) : PIR.Process (Zkc.Protocols.Schnorr.Common.actions (F := F) (G := G)) (Option Bool) :=
  helpersImport.denote (scalarMeaning F G) id 1 (Schnorr.verifierInputs base key service)

def reordered (base key : G) (service : Nat) : PIR.Process (Zkc.Protocols.Schnorr.Common.actions (F := F) (G := G)) (Option Bool) :=
  reorderedImport.denote (scalarMeaning F G) id 1 (Schnorr.verifierInputs base key service)

def verifier (form : Form) : Zkc.Protocols.Schnorr.Common.Verifier F G :=
  match form with
  | .original => Schnorr.verifier
  | .helpers => helpers
  | .reordered => reordered

theorem helpers_correspondence (base key : G) (service : Nat) :
    helpers (F := F) base key service = Schnorr.experiment base key service := by
  rfl

theorem reordered_correspondence (base key : G) (service : Nat) :
    reordered (F := F) base key service = Schnorr.experiment base key service := by
  apply PIR.Process.call_congr
  intro commitment
  apply PIR.Process.call_congr
  intro challenge
  apply PIR.Process.call_congr
  intro acknowledgement
  apply PIR.Process.call_congr
  intro response
  change PIR.Process.done (some (decide (response • base = challenge • key + commitment))) =
    PIR.Process.done (some (decide (response • base = commitment + challenge • key)))
  rw [add_comm (challenge • key) commitment]

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
