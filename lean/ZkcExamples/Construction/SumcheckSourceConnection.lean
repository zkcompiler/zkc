module

public import ZkcExamples.Construction.SumcheckArtifact
public import ZkcExamples.Structured.SumcheckSourceVerifier
public import ZkcExamples.Structured.Generated.Connections.SmallSumcheck
public import Zkc.Construction.ScalarConnection
public import Zkc.Construction.Uniform.ScalarSupportProposer
public import Zkc.Construction.Uniform.ScalarHandles

@[expose] public section

/-! Retained Sumcheck execution uses the generic checked connection. The only
family-specific presentation below is a source-to-source capability relabeling;
no artifact, instruction, route, frame or oracle simulation is authored here. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ZkcExamples.Construction.SumcheckSourceConnection
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open Uniform Uniform.DomainAdapter
open ZkcExamples.Structured
open SumcheckVerifierLaws SumcheckSourceVerifier
attribute [local implicit_reducible] CheckedProtocol.signature
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

abbrev artifact := SumcheckProof.participant
abbrev program := SumcheckProof.program
abbrev context := SumcheckProof.context
abbrev routing := Generated.Connections.SmallSumcheck.validatorRouting

theorem artifact_identity : Generated.Connections.SmallSumcheck.validatorArtifact = artifact := rfl
theorem source_identity : Generated.Connections.SmallSumcheck.program = program := by kernel_rfl

def sourceABI : Original.InputABI :=
  (SourceConnection.canonicalABI program 1 artifact).toOption.get (by decide +kernel)

theorem checkedConnection : SourceConnection.Connected program routing 1 sourceABI artifact :=
  ScalarConnection.canonicalize Generated.Connections.SmallSumcheck.validatorConnected (by kernel_rfl)

theorem requiredConnection : ConnectionAdmission.Required program context .validator artifact :=
  ConnectionAdmission.ofConnected (boundary := ⟨sourceABI, routing⟩) (by kernel_rfl) checkedConnection

omit [AddCommGroup G] [Module F G] [DecidableEq G] in
private theorem round_handle (ctx : ProtocolContext) (original replacement : Nat) (state : List F × F) :
    (((roundPresent (G := G) ctx original state).interpret CommonAdapter.project).interpret
      (ScalarHandles.replace replacement)) =
    (roundPresent ctx replacement state).interpret CommonAdapter.project := by
  simp only [roundPresent, PIR.Process.interpret, CommonAdapter.project, PIR.Process.bind,
    ScalarHandles.replace]
  congr 1
  funext low
  congr 1
  funext high
  split <;> rfl

omit [AddCommGroup G] [Module F G] [DecidableEq G] in
private theorem repeat_handle (ctx : ProtocolContext) (original replacement count : Nat)
    (state : List F × F) :
    (((PIR.repeatN count (roundPresent (G := G) ctx original) state).interpret CommonAdapter.project).interpret
      (ScalarHandles.replace replacement)) =
    (PIR.repeatN count (roundPresent ctx replacement) state).interpret CommonAdapter.project := by
  simp only [Zkc.Source.interpret_repeat, round_handle]

theorem source_handle (values : List F) (claim : F) (rounds original replacement : Nat) :
    (SumcheckProof.verifier (G := G) values claim rounds original).interpret
      (ScalarHandles.replace replacement) =
    SumcheckProof.verifier values claim rounds replacement := by
  have expansion (handle : Nat) : program.participant F G 1
      (SumcheckProof.verifierInputs values claim rounds handle) =
      (SumcheckVerifierPrelude.admittedRounds SumcheckSourceNormalForms.reduceMaximum childContext
        (some rounds) (some handle) (some claim)).bind
        (fun pc => SumcheckVerifierTerminal.actualOwnedCheck SumcheckSourceViews.unit 1
          (some values) pc.1 pc.2) := verifier_optional (some values) (some claim) (some rounds) (some handle)
  unfold SumcheckProof.verifier SumcheckProof.process
  rw [expansion original, expansion replacement]
  simp only [SumcheckVerifierPrelude.admittedRounds, SumcheckVerifierPrelude.pendingRounds]
  split
  · rw [repeat_present (F := F) (G := G) childContext original rounds ([], claim),
      repeat_present (F := F) (G := G) childContext replacement rounds ([], claim)]
    simp only [PIR.Process.bind_assoc, PIR.Process.bind,
      PIR.Process.interpret_bind]
    rw [repeat_handle]
    congr 1
    funext state
    rw [SumcheckVerifierTerminal.terminal_decision]
    split_ifs <;> rfl
  · rfl

/-- All raw public inputs, arbitrary proof suffixes, initial histories and
oracle replies, with the artifact's own scalar key policy fixed before evidence. -/
theorem transform {m : Type → Type} [Monad m] [LawfulMonad m]
    (challenge : History F G → m F) (values : List F) (claim : F)
    (rounds handle : Nat) (initial : History F G) (proof : Proof F G) :
    runK (ScalarVerifier.origin artifact) initial challenge
      (Domain.participant (ringModel F G) program context artifact
        [.data (.vector "bls12-381.fr" values), .data (.field "bls12-381.fr" claim),
          .data (.index rounds), .transcript context.suite []]) proof
      (fun result unread => pure (.returned (ScalarVerifier.acceptance 0 result), unread)) =
    Zkc.Construction.transform context challenge (SumcheckProof.verifier values claim rounds handle) initial proof := by
  let physical : Domain.Environment (uniformCarriers F G) :=
    [.data (.vector "bls12-381.fr" values), .data (.field "bls12-381.fr" claim),
      .data (.index rounds), .transcript context.suite []]
  have law := ScalarConnection.transform (F := F) (G := G) checkedConnection rfl _ rfl (by decide +kernel)
    physical (SumcheckProof.verifierInputs values claim rounds routing.selectedHandle)
    (by kernel_rfl) (by kernel_rfl) (by derive_scalar_support) .here (by rfl) challenge initial proof
  change _ = Zkc.Construction.transform context challenge
    (SumcheckProof.verifier values claim rounds routing.selectedHandle) initial proof at law
  have relabel := ScalarHandles.transform context routing.selectedHandle challenge
    (SumcheckProof.verifier (G := G) values claim rounds handle) initial proof
  rw [source_handle] at relabel
  exact law.trans relabel

end ZkcExamples.Construction.SumcheckSourceConnection
