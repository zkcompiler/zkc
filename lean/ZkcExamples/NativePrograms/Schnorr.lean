module

public import ZkcExamples.NativePrograms.SchnorrData

public import Zkc.Protocols.Schnorr.Common

@[expose] public section

/-! The imported native DSL Schnorr program, with its exact source bindings.

The maintained native bridge check regenerates the fixture from the public DSL
Entry and checks the original hash against the native interface. The data renderer is tested against that export; kernel checking below admits
the transparent constructor data and proves properties of its elaborated body.
-/

set_option autoImplicit false

namespace ZkcExamples.NativePrograms.Schnorr

open Zkc.Source Zkc.Source.Common Zkc.Source.Common.Native

def imported : Imported := (SchnorrData.snapshot.check).toOption.get (by decide +kernel)

variable {F G : Type} [Field F] [DecidableEq F]
    [AddCommGroup G] [Module F G] [DecidableEq G]

abbrev meaning := scalarMeaning F G
abbrev actions := Participant.interface Nat Ty services (ScalarValue F G)

def verifierInputs (base key : G) (challengeService : Nat) :
    Values (fun ty => Option (ScalarValue F G ty)) SchnorrData.snapshot.inputs :=
  .cons (some base) (.cons (some key) (.cons none (.cons none (.cons (some challengeService) .nil))))

def wiring : Zkc.Protocols.Schnorr.Common.Wiring :=
  ⟨0, "bls12-381.g1", "bls12-381.fr", "label_636f6d6d69746d656e74_0",
    "label_6368616c6c656e6765", "label_64656c6976657279_0", "label_726573706f6e7365_0"⟩

abbrev experiment := Zkc.Protocols.Schnorr.Common.experiment (F := F) (G := G) wiring

def verifier (base key : G) (service : Nat) : PIR.Proc (actions (F := F) (G := G)) (Option Bool) :=
  imported.denote (scalarMeaning F G) id 1 (verifierInputs base key service)

/-- Equality of open processes preserves every handler's replies, stops, state
and events, including malicious responses and aborted prefixes. -/
theorem verifier_correspondence (base key : G) (challengeService : Nat) :
    imported.denote (scalarMeaning F G) id 1 (verifierInputs base key challengeService) =
      experiment base key challengeService := by
  rfl

/-- One implementation proof supplies both completeness and special soundness. -/
theorem contract : Zkc.Protocols.Schnorr.Common.VerifierContract wiring (verifier (F := F) (G := G)) :=
  ⟨fun base key service => ⟨verifier_correspondence base key service⟩⟩

export Zkc.Protocols.Schnorr.Common (Strategy transcriptHandler)
abbrev run := Zkc.Protocols.Schnorr.Common.run (verifier (F := F) (G := G))

theorem accepted_iff (base key : G) (service : Nat) (prover : Strategy F G) (challenge : F) :
    (run base key service prover challenge).outcome = .returned (some true) ↔
      prover.response challenge • base = prover.commitment + challenge • key := by
  exact contract.accepted_iff base key service prover challenge

theorem perfect_completeness (base : G) (secret nonce challenge : F) (service : Nat) :
    (run base (secret • base) service ⟨nonce • base, fun c => nonce + c * secret⟩ challenge).outcome =
      .returned (some true) := by
  exact contract.perfect_completeness base secret nonce challenge service

/-- Actual imported-program acceptance in two challenges yields a key opening.
This is special soundness; a probabilistic rewinding reduction is separate. -/
theorem special_soundness (base key : G) (service : Nat) (prover : Strategy F G)
    (first second : F) (distinct : first ≠ second)
    (acceptFirst : (run base key service prover first).outcome = .returned (some true))
    (acceptSecond : (run base key service prover second).outcome = .returned (some true)) :
    ((prover.response first - prover.response second) / (first - second)) • base = key := by
  exact contract.special_soundness base key service prover first second distinct acceptFirst acceptSecond

end ZkcExamples.NativePrograms.Schnorr
