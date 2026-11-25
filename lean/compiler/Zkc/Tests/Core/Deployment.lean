import Zkc.Core.Format.Canonical
import Zkc.Core.Scheme.Deploy
import Zkc.Core.Run.Execute
import Zkc.Core.Admission.Admit
import Zkc.Tests.Core.Consumers

/-!
Unit tests and negative controls for canonical wire formats, non-interactive Fiat-Shamir
deployment (`DeploymentPlan`, two-layer `Core.Handler`), and the fuel-bounded Lean reference
executor (`execute`, `provePlan`, `verifyPlan`, `runInteractive`).
-/

namespace Zkc.Core.Tests.Deployment

open Zkc.Core

-- Compute concrete protocol runs by kernel reduction in tests.
unseal Zkc.Core.fnMeaning Zkc.Core.roleMeaning Zkc.Core.protocolMeaning

set_option maxRecDepth 8000

/-! ## Canonical wire format checks -/

theorem byteWidth_cases :
    byteWidth 0 = 0 ∧
    byteWidth 1 = 0 ∧
    byteWidth 2 = 1 ∧
    byteWidth 256 = 1 ∧
    byteWidth 257 = 2 ∧
    byteWidth (2 ^ 64) = 8 ∧
    byteWidth (2 ^ 65) = 9 := by
  decide +kernel

theorem formatFin_roundtrip_and_reject :
    (formatFin 257).write 256 = [0, 1] ∧
    (formatFin 257).read [0, 1, 99] = some (256, [99]) ∧
    (formatFin 257).read [1, 1] = none ∧
    (formatFin 257).read [256, 0] = none ∧
    (formatFin 17).write 16 = [16] ∧
    (formatFin 17).read [17] = none ∧
    (formatFin 17).read [] = none := by
  decide +kernel

theorem formatBool_roundtrip_and_reject :
    formatBool.write false = [0] ∧
    formatBool.write true = [1] ∧
    formatBool.read [0, 42] = some (false, [42]) ∧
    formatBool.read [1] = some (true, []) ∧
    formatBool.read [2] = none ∧
    formatBool.read [] = none := by
  decide +kernel

theorem formatNat_leb128_roundtrip_and_canonical :
    formatNat.write 0 = [0] ∧
    formatNat.write 127 = [127] ∧
    formatNat.write 128 = [128, 1] ∧
    formatNat.write 300 = [172, 2] ∧
    formatNat.read [0, 7] = some (0, [7]) ∧
    formatNat.read [128, 1, 9] = some (128, [9]) ∧
    formatNat.read [172, 2] = some (300, []) ∧
    -- Non-canonical encodings with trailing zero 7-bit groups must be rejected.
    formatNat.read [128, 0] = none ∧
    formatNat.read [129, 0] = none ∧
    formatNat.read [128, 128, 0] = none ∧
    formatNat.read [256] = none := by
  decide +kernel

theorem formatSeq_roundtrip_and_reject :
    (formatSeqSized (formatFin 17) 3).write [1, 5, 16] = [1, 5, 16] ∧
    (formatSeqSized (formatFin 17) 3).read [1, 5, 16, 99] = some ([1, 5, 16], [99]) ∧
    (formatSeqSized (formatFin 17) 3).read [1, 5] = none ∧
    (formatSeqSized (formatFin 17) 3).read [1, 5, 17] = none ∧
    (formatSeqUnsized formatBool).write [true, false, true] = [3, 1, 0, 1] ∧
    (formatSeqUnsized formatBool).read [3, 1, 0, 1, 88] = some ([true, false, true], [88]) ∧
    (formatSeqUnsized formatBool).read [3, 1, 0] = none ∧
    (formatSeqUnsized formatBool).read [128, 0] = none := by
  decide +kernel

/-! ## Concrete toy Schnorr group model (`q = 11`, `p = 23`, generator `g = 2`) -/

/-- Modular exponentiation `(base ^ exp) % modulus`. -/
def powMod (base : Nat) : Nat → Nat → Nat
  | 0, m => 1 % m
  | exp + 1, m => (base * powMod base exp m) % m

theorem powMod_lt (base exp m : Nat) (hm : 0 < m) : powMod base exp m < m := by
  cases exp with
  | zero => exact Nat.mod_lt 1 hm
  | succ e => exact Nat.mod_lt _ hm

/-- Toy multiplicative Schnorr group of prime order `q = 11` inside `Z_23*` with generator `2`. -/
def toySigmaModel : Model sigmaVocabulary where
  Carrier
    | .scalar => Nat
    | .point => Nat
  valid
    | .scalar, x => x < 11
    | .point, y => y < 23
  literal
    | .scalar, n => some (n % 11)
    | .point, n => some (n % 23)
  apply key _ known args :=
    match key, known, args with
    | .base, rfl, .cons s .nil => some (.cons (powMod 2 s 23) .nil)
    | .add, rfl, .cons a (.cons b .nil) => some (.cons ((a + b) % 11) .nil)
    | .mul, rfl, .cons a (.cons b .nil) => some (.cons ((a * b) % 11) .nil)
    | .scale, rfl, .cons s (.cons p .nil) => some (.cons (powMod p s 23) .nil)
    | .plus, rfl, .cons a (.cons b .nil) => some (.cons ((a * b) % 23) .nil)
    | .same, rfl, .cons a (.cons b .nil) => some (.cons (decide (a = b)) .nil)
  inDomain _ _ _ _ := true
  defined key _ known args := by
    cases key <;> cases known
    · cases args with | cons s rest => cases rest; rfl
    · cases args with | cons a rest => cases rest with | cons b rest2 => cases rest2; rfl
    · cases args with | cons a rest => cases rest with | cons b rest2 => cases rest2; rfl
    · cases args with | cons s rest => cases rest with | cons p rest2 => cases rest2; rfl
    · cases args with | cons a rest => cases rest with | cons b rest2 => cases rest2; rfl
    · cases args with | cons a rest => cases rest with | cons b rest2 => cases rest2; rfl
  total _ _ _ _ _ := rfl
  decides key _ known _ kind _ := by cases key <;> cases known <;> cases kind
  keeps key _ known args outs _ h := by
    cases key <;> cases known
    · cases args with | cons s rest =>
        cases rest
        injection h with hEq; subst hEq
        exact ⟨powMod_lt 2 s 23 (by decide), trivial⟩
    · cases args with | cons a rest => cases rest with | cons b rest2 =>
        cases rest2
        injection h with hEq; subst hEq
        exact ⟨Nat.mod_lt _ (by decide), trivial⟩
    · cases args with | cons a rest => cases rest with | cons b rest2 =>
        cases rest2
        injection h with hEq; subst hEq
        exact ⟨Nat.mod_lt _ (by decide), trivial⟩
    · cases args with | cons s rest => cases rest with | cons p rest2 =>
        cases rest2
        injection h with hEq; subst hEq
        exact ⟨powMod_lt p s 23 (by decide), trivial⟩
    · cases args with | cons a rest => cases rest with | cons b rest2 =>
        cases rest2
        injection h with hEq; subst hEq
        exact ⟨Nat.mod_lt _ (by decide), trivial⟩
    · cases args with | cons a rest => cases rest with | cons b rest2 =>
        cases rest2
        injection h with hEq; subst hEq
        exact ⟨trivial, trivial⟩
  literals key n _ := by
    cases key
    · exact ⟨n % 11, rfl, Nat.mod_lt _ (by decide)⟩
    · exact ⟨n % 23, rfl, Nat.mod_lt _ (by decide)⟩
  support law _ known _ v :=
    match law, known with
    | (), rfl => v < 11
  supported law _ known _ _ _ h := by
    cases law
    cases known
    exact h

/-- Lawful canonical codecs for `toySigmaModel`. -/
def toySigmaCodecs : ValidCodecs toySigmaModel where
  format
    | .scalar => formatFin 11
    | .point => formatFin 23
  lawful
    | .scalar => formatFin_lawful 11
    | .point => formatFin_lawful 23

/-- Vocabulary encoder for `sigmaVocabulary`. -/
def toySigmaEncoder : VocabEncoder sigmaVocabulary where
  typeKey
    | .scalar => [0]
    | .point => [1]
  rowKey
    | .base => [0]
    | .add => [1]
    | .mul => [2]
    | .scale => [3]
    | .plus => [4]
    | .same => [5]
  lawKey _ := [0]

/-- Simple deterministic polynomial sponge state update for testing Fiat-Shamir binding. -/
def mixBytes (acc : Nat) : List Nat → Nat
  | [] => acc
  | b :: rest => mixBytes ((acc * 257 + b + 31) % 65521) rest

/-- Deterministic lawful `TranscriptModel` for `toySigmaModel`. -/
def toyTranscript : TranscriptModel sigmaVocabulary toySigmaModel where
  State := Nat
  init idBytes := mixBytes 1 idBytes
  absorb st label bytes := mixBytes (mixBytes st label) bytes
  squeeze st _ τ label :=
    let st' := mixBytes st (0xFF :: label)
    match τ with
    | .nominal .scalar => some (st' % 11, st')
    | _ => none

theorem toyTranscript_lawful : toyTranscript.Lawful := by
  intro st law s hlaw hins τ hout label
  cases law
  simp only [sigmaVocabulary] at hlaw
  injection hlaw with hs
  subst hs
  subst hout
  refine ⟨(mixBytes st (0xFF :: label)) % 11, mixBytes st (0xFF :: label), rfl, ?_⟩
  refine ⟨Nat.mod_lt _ (by decide), ⟨[], .nominal .scalar⟩, rfl, rfl, rfl, Nat.mod_lt _ (by decide)⟩

/-! ## End-to-end admission, deployment, proving, verifying, and negative controls -/

/-- A fixed private randomness source returning nonce `r` at the prover's private coin. -/
def fixedNonceSource (nonce : Nat) : Source toySigmaModel := fun _ τ =>
  match τ with
  | .nominal .scalar => some (nonce % 11)
  | _ => none

/-- Extract the admitted `sigmaByNames` program via kernel-verified admission. -/
def admittedSigma : Admitted sigmaVocabulary :=
  (admit sigmaByNames noAssociation).toOption.get (by decide +kernel)

/-- Extract the validated `DeploymentPlan` for `sigmaScheme`. -/
def sigmaPlan : DeploymentPlan sigmaVocabulary :=
  (planDeployment toySigmaEncoder admittedSigma sigmaScheme).toOption.get (by decide +kernel)

/-- Catalogue scheme declaration over `sigmaByNames` using `merlin3Bls12381`. -/
def sigmaCatalogueScheme : Declaration :=
  { sigmaScheme with construction := .catalogue .merlin3Bls12381 (some "schnorr-v1") }

/-- Extract the validated `DeploymentPlan` for `sigmaCatalogueScheme`. -/
def sigmaCataloguePlan : DeploymentPlan sigmaVocabulary :=
  (planDeployment toySigmaEncoder admittedSigma sigmaCatalogueScheme).toOption.get (by decide +kernel)

/-- Deploying the catalogue scheme resolves prover/verifier and yields a distinct identity. -/
theorem sigmaCatalogue_planned_and_distinct_identity :
    sigmaCataloguePlan.prover = 0 ∧
    sigmaCataloguePlan.verifier = 1 ∧
    sigmaCataloguePlan.identity ≠ sigmaPlan.identity := by
  decide +kernel

/-- Build the typed input `HList` for a Schnorr-shaped protocol from `(witness, statement)`. -/
def sigmaInputs (insTys : List (LTy sigmaVocabulary)) (witness statement : Nat) :
    Option (HList (LVal toySigmaModel) insTys) :=
  match insTys with
  | [⟨.nominal .scalar, [0]⟩, ⟨.nominal .point, [0, 1]⟩] =>
      some (.cons (witness : Nat) (.cons (statement : Nat) .nil))
  | _ => none

/-- Run prover on `(witness, statement, nonce)` for a validated `DeploymentPlan`. -/
def runSigmaProve (plan : DeploymentPlan sigmaVocabulary) (witness statement nonce : Nat) :
    Option (List Nat) :=
  (sigmaInputs plan.entry.ins witness statement).bind fun ins =>
    provePlan toySigmaModel plan toySigmaCodecs toyTranscript
      (hideAll toySigmaModel plan.prover ins) (fixedNonceSource nonce) 64

/-- Run verifier on `(statement, proof)` for a validated `DeploymentPlan`. -/
def runSigmaVerify (plan : DeploymentPlan sigmaVocabulary) (statement : Nat)
    (proof : List Nat) : Bool :=
  match sigmaInputs plan.entry.ins 0 statement with
  | some ins =>
      (verifyPlan toySigmaModel plan toySigmaCodecs toyTranscript
        (hideAll toySigmaModel plan.verifier ins) proof (fixedNonceSource 0) 64).isSome
  | none => false

/-- Check honest proving and verifying: `w = 7`, `Y = 2^7 % 23 = 13`, nonce `r = 5`. -/
def checkHonestProof (plan : DeploymentPlan sigmaVocabulary) : Bool :=
  match runSigmaProve plan 7 13 5 with
  | some proof =>
      decide (proof.length = 2) &&
      proof.all (fun b => decide (b < 256)) &&
      runSigmaVerify plan 13 proof
  | none => false

theorem sigma_honest_proves_and_verifies : checkHonestProof sigmaPlan = true := by
  decide +kernel

/-- Check all verifier negative controls: wrong statement, mutated response byte, truncated
proof, trailing garbage byte, out-of-range scalar byte, and dishonest witness all reject. -/
def checkNegativeControls (plan : DeploymentPlan sigmaVocabulary) : Bool :=
  match runSigmaProve plan 7 13 5, runSigmaProve plan 6 13 5 with
  | some goodProof, some badWitnessProof =>
      !runSigmaVerify plan 12 goodProof &&
      !runSigmaVerify plan 13 [goodProof.getD 0 0, (goodProof.getD 1 0 + 1) % 11] &&
      !runSigmaVerify plan 13 (goodProof.take 1) &&
      !runSigmaVerify plan 13 (goodProof ++ [0]) &&
      !runSigmaVerify plan 13 [goodProof.getD 0 0, 11] &&
      !runSigmaVerify plan 13 badWitnessProof
  | _, _ => false

theorem sigma_negative_controls : checkNegativeControls sigmaPlan = true := by
  decide +kernel

/-- Derive the Fiat-Shamir challenge for `sigmaPlan` on a given `(statement, commitment)`. -/
def sigmaChallenge (plan : DeploymentPlan sigmaVocabulary) (statement commitment : Nat) :
    Option Nat :=
  match sigmaInputs plan.entry.ins 0 statement with
  | some ins =>
      let st0 := startTranscript toySigmaModel toySigmaCodecs toyTranscript plan.identity
        (statementValues toySigmaModel plan.prover plan.verifier plan.verifier (.inr rfl)
          (hideAll toySigmaModel plan.verifier ins))
      let st1 := toyTranscript.absorb st0 (messageLabel ⟨[], ⟨12⟩⟩)
        ((canonicalFormat toySigmaModel toySigmaCodecs (.nominal .point)).write commitment)
      (toyTranscript.squeeze st1 () (.nominal .scalar) (coinLabel ⟨[], ⟨13⟩⟩)).map Prod.fst
  | none => none

/-- Check Weak Fiat-Shamir prevention: two different valid statements (`Y = 13` with `w = 7`
and `Y = 2` with `w = 1`) using the same nonce `r = 5` (same commitment `A = 9`) derive
different Fiat-Shamir challenges, produce distinct proofs, and do not cross-verify. -/
def checkWeakFsBinding (plan : DeploymentPlan sigmaVocabulary) : Bool :=
  match sigmaChallenge plan 13 9, sigmaChallenge plan 2 9,
      runSigmaProve plan 7 13 5, runSigmaProve plan 1 2 5 with
  | some c1, some c2, some p1, some p2 =>
      decide (c1 ≠ c2) &&
      decide (p1.getD 0 0 = p2.getD 0 0) &&
      decide (p1 ≠ p2) &&
      runSigmaVerify plan 13 p1 &&
      runSigmaVerify plan 2 p2 &&
      !runSigmaVerify plan 13 p2 &&
      !runSigmaVerify plan 2 p1
  | _, _, _, _ => false

theorem sigma_weak_fs_statement_binding : checkWeakFsBinding sigmaPlan = true := by
  decide +kernel

/-- Check the interactive two-role scheduler on an honest Schnorr run. -/
def checkInteractiveAccepts (plan : DeploymentPlan sigmaVocabulary) : Bool :=
  match sigmaInputs plan.entry.ins 7 13 with
  | some ins =>
      let pProg := roleMeaning toySigmaModel plan.admitted.program plan.callee 0 []
        (hideAll toySigmaModel 0 ins)
      let vProg := roleMeaning toySigmaModel plan.admitted.program plan.callee 1 []
        (hideAll toySigmaModel 1 ins)
      match runInteractive toySigmaModel (fixedNonceSource 5) 0 1 pProg vProg 32 with
      | (.ended (.returned _), .ended (.returned _), _) => true
      | _ => false
  | none => false

theorem sigma_interactive_accepts : checkInteractiveAccepts sigmaPlan = true := by
  decide +kernel

end Zkc.Core.Tests.Deployment
