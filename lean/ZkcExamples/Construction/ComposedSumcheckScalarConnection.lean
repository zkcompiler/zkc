module

public import ZkcExamples.Structured.Generated.Connections.TwoSums
public import ZkcExamples.Construction.ComposedSumcheckProofParticipant
public import ZkcExamples.Construction.ComposedSumcheckProofData
public import ZkcExamples.Construction.ComposedSumcheckSourceHandles
public import Zkc.Construction.ScalarConnection
public import Zkc.Construction.Uniform.ScalarSupportProposer

@[expose] public section

/-! Complete retained scalar transport for the exact TwoSums artifact.
The generated root supplies all-input correspondence; source-only capability
naturality preserves both captured calls, arbitrary replies and exact stops. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ZkcExamples.Construction.ComposedSumcheckScalarConnection
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open Uniform.DomainAdapter
open ZkcExamples.Structured

abbrev program := Generated.Connections.TwoSums.program
abbrev context := Generated.Connections.TwoSums.context
abbrev routing := Generated.Connections.TwoSums.validatorRouting
abbrev artifact := ComposedSumcheckProofParticipant.participant

theorem artifact_identity : Generated.Connections.TwoSums.validatorArtifact = artifact := rfl
theorem source_identity : program.snapshot = ComposedSumcheckProofData.snapshot := by kernel_rfl

def sourceABI : Original.InputABI :=
  (SourceConnection.canonicalABI program 1 artifact).toOption.get (by decide +kernel)

theorem checkedConnection : SourceConnection.Connected program routing 1 sourceABI artifact :=
  ScalarConnection.canonicalize Generated.Connections.TwoSums.validatorConnected (by kernel_rfl)

theorem requiredConnection : ConnectionAdmission.Required program context .validator artifact :=
  ConnectionAdmission.ofConnected (boundary := ⟨sourceABI, routing⟩) (by kernel_rfl) checkedConnection

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

def sourceInputs (left right : List F) (leftClaim rightClaim : F) (count handle : Nat) :
    Values (Component (assignment F G)) program.payload.entry.inputs :=
  .cons (some left) (.cons (some right) (.cons (some leftClaim) (.cons (some rightClaim)
    (.cons (some count) (.cons (some handle) .nil)))))

def sourceVerifier (left right : List F) (leftClaim rightClaim : F) (count handle : Nat) :
    PIR.Process (Actions F G) (Option Bool) :=
  ((program.participant F G 1 (sourceInputs left right leftClaim rightClaim count handle)).bind
    fun outputs => .done (outputs.get .here)).interpret CommonAdapter.project

/-- Exact transport for every raw vector, claim and count, all proof streams,
stops, oracle replies and history prefixes, at the fixed canonical source ABI. -/
theorem canonical_transform {m : Type → Type} [Monad m] [LawfulMonad m]
    (challenge : History F G → m F) (left right : List F) (leftClaim rightClaim : F)
    (count : Nat) (initial : History F G) (proof : Proof F G) :
    runK (ScalarVerifier.origin artifact) initial challenge
      (Domain.participant (ringModel F G) program context artifact
        [.data (.vector "bls12-381.fr" left), .data (.vector "bls12-381.fr" right),
          .data (.field "bls12-381.fr" leftClaim), .data (.field "bls12-381.fr" rightClaim),
          .data (.index count), .transcript context.suite []]) proof
      (fun result unread => pure (.returned (ScalarVerifier.acceptance 0 result), unread)) =
    transform context challenge
      (sourceVerifier left right leftClaim rightClaim count routing.selectedHandle) initial proof := by
  exact ScalarConnection.transform (F := F) (G := G) checkedConnection rfl _ rfl (by decide +kernel)
    _ (sourceInputs left right leftClaim rightClaim count routing.selectedHandle)
    (by kernel_rfl) (by kernel_rfl) (by derive_scalar_support) .here (by rfl) challenge initial proof

/-- Full source process naturality, before acceptance selection. -/
theorem source_handle (left right : List F) (leftClaim rightClaim : F)
    (count original replacement : Nat) :
    (sourceVerifier (G := G) left right leftClaim rightClaim count original).interpret
      (Uniform.ScalarHandles.replace replacement) =
    sourceVerifier left right leftClaim rightClaim count replacement := by
  unfold sourceVerifier sourceInputs
  simp only [PIR.Process.interpret_bind]
  apply congrArg₂ PIR.Process.bind
  · exact ComposedSumcheckSourceHandles.participant_handle (G := G)
      (some left) (some right) (some leftClaim) (some rightClaim) (some count) original replacement
  · rfl

/-- All public inputs and capability labels, preserving all replies, exact
stops and unread suffixes through the same checked root. -/
theorem transform {m : Type → Type} [Monad m] [LawfulMonad m]
    (challenge : History F G → m F) (left right : List F) (leftClaim rightClaim : F)
    (count handle : Nat) (initial : History F G) (proof : Proof F G) :
    runK (ScalarVerifier.origin artifact) initial challenge
      (Domain.participant (ringModel F G) program context artifact
        [.data (.vector "bls12-381.fr" left), .data (.vector "bls12-381.fr" right),
          .data (.field "bls12-381.fr" leftClaim), .data (.field "bls12-381.fr" rightClaim),
          .data (.index count), .transcript context.suite []]) proof
      (fun result unread => pure (.returned (ScalarVerifier.acceptance 0 result), unread)) =
    Zkc.Construction.transform context challenge
      (sourceVerifier left right leftClaim rightClaim count handle) initial proof := by
  have law := canonical_transform challenge left right leftClaim rightClaim count initial proof
  have relabel := Uniform.ScalarHandles.transform context routing.selectedHandle challenge
    (sourceVerifier (G := G) left right leftClaim rightClaim count handle) initial proof
  rw [source_handle] at relabel
  exact law.trans relabel

end ZkcExamples.Construction.ComposedSumcheckScalarConnection
