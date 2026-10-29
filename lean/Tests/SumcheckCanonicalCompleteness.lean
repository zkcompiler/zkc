module

public import ZkcExamples.Executable.SumcheckCompleteness

@[expose] public section

/-! Symbolic consumers and negative controls for the full retained Sumcheck. -/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
namespace Tests.SumcheckCanonicalCompleteness
open Zkc Zkc.Construction Zkc.Executable Zkc.Source
open Zkc.Source.Structured
open ZkcExamples.Executable
open ZkcExamples.Structured
open Uniform
attribute [local implicit_reducible] CheckedProtocol.signature
open Zkc.Construction.Uniform.DomainAdapter

attribute [local irreducible] DomainVM.Sufficient DomainVM.Passes DomainVM.metered
  ZkcExamples.Construction.SumcheckProof.compiledVerifier ZkcExamples.Construction.SumcheckProof.verifier

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

abbrev run (oracle : History F G → F) (budget : Nat) (values : List F) (claim : F)
    (rounds : Nat) (proof : Proof F G) :=
  DomainVM.metered (m := Id) ZkcExamples.Construction.SumcheckProof.program
    ZkcExamples.Construction.SumcheckProof.context Origin.withoutCoordinates [] oracle
    SumcheckCharges.cost budget SumcheckProof.lowered (SumcheckProof.physicalInputs values claim rounds []) proof

/-- The consumer keeps the round count symbolic and uses the actual Entry. -/
theorem variable_honest (oracle : History F G → F) (values : List F) (rounds : Nat)
    (admitted : rounds ≤ SumcheckProof.maximum) (shaped : values.length = 2 ^ rounds) :
    ∃ history suffix, run oracle (72 + 59 * rounds) values values.sum rounds
      ((SumcheckCompleteness.honestRounds oracle [] values rounds).map (.field "bls12-381.fr")) =
      (.returned [.data (.boolean true), .transcript ZkcExamples.Construction.SumcheckProof.context.suite history], []) ∧
      readbackHistory Origin.withoutCoordinates history = some suffix :=
  SumcheckCompleteness.honest_metered oracle _ values rounds admitted shaped []
    (by rw [SumcheckCharges.charge_eq])

theorem zero_honest (oracle : History F G → F) (value : F) :
    ∃ history suffix, run oracle 72 [value] value 0 [] =
      (.returned [.data (.boolean true), .transcript ZkcExamples.Construction.SumcheckProof.context.suite history], []) ∧
      readbackHistory Origin.withoutCoordinates history = some suffix := by
  simpa [SumcheckCompleteness.honestRounds, SumcheckDomainHonest.messages, SumcheckMessages.honestRounds] using
    variable_honest oracle [value] 0 (by decide +kernel) (by simp)

theorem one_honest (oracle : History F G → F) (low high : F) :
    ∃ history suffix, run oracle 131 [low, high] (low + high) 1
      ((SumcheckCompleteness.honestRounds oracle [] [low, high] 1).map (.field "bls12-381.fr")) =
      (.returned [.data (.boolean true), .transcript ZkcExamples.Construction.SumcheckProof.context.suite history], []) ∧
      readbackHistory Origin.withoutCoordinates history = some suffix := by
  simpa using variable_honest oracle [low, high] 1 (by decide +kernel) (by simp)

theorem two_honest (oracle : History F G → F) (a b c d : F) :
    ∃ history suffix, run oracle 190 [a,b,c,d] (a + (b + (c + d))) 2
      ((SumcheckCompleteness.honestRounds oracle [] [a,b,c,d] 2).map (.field "bls12-381.fr")) =
      (.returned [.data (.boolean true), .transcript ZkcExamples.Construction.SumcheckProof.context.suite history], []) ∧
      readbackHistory Origin.withoutCoordinates history = some suffix := by
  simpa using variable_honest oracle [a,b,c,d] 2 (by decide +kernel) (by simp)

/-- A symbolic static maximum and round count exercise the reusable loop rule;
the family does not assume that the current Entry has two rounds. -/
theorem variable_budget (maximum rounds : Nat) (small : maximum < 64)
    (values : List F) (claim : F) (history : Domain.History (Structured.uniformCarriers F G))
    (proof : Proof F G) (shaped : values.length = 2 ^ rounds) :
    DomainVM.Sufficient ZkcExamples.Construction.SumcheckProof.program
      ZkcExamples.Construction.SumcheckProof.context SumcheckCharges.cost (72 + 59 * rounds)
      (SumcheckCharges.lowered maximum) (SumcheckProof.physicalInputs values claim rounds history) proof :=
  SumcheckCharges.sufficient_family maximum small _ values claim rounds history proof shaped
    (by rw [SumcheckCharges.charge_eq])

/-- Insufficient budget stops before even the Pending constructor. -/
theorem zero_budget (oracle : History F G → F) (values : List F) (claim : F)
    (rounds : Nat) (proof : Proof F G) :
    run oracle 0 values claim rounds proof = (.stopped .exhausted, proof) := by
  unfold run
  rw [SumcheckCharges.lowered_eq]
  simp [SumcheckCharges.lowered, SumcheckShape.code, DomainVM.metered,
    DomainVM.meteredK, DomainVM.meteredStep]
  rfl

/-- False zero-round claims remain false through the all-input checked
endpoint, independently of the proof suffix and oracle. -/
theorem false_claim_compiled (oracle : History F G → F) (value claim : F) (wrong : value ≠ claim)
    (proof : Proof F G) :
    ZkcExamples.Construction.SumcheckProof.compiledVerifier (m := Id) oracle [value] claim 0 [] proof =
      (.returned (some false), proof) := by
  rw [ZkcExamples.Construction.SumcheckProof.compiled_transform (m := Id) oracle [value] claim 0 77]
  unfold ZkcExamples.Construction.SumcheckProof.verifier ZkcExamples.Construction.SumcheckProof.process
  have zero := SumcheckSourceVerifier.verifier_zero (F := F) (G := G) (some [value]) claim (some 77)
  change ZkcExamples.Construction.SumcheckProof.program.participant F G 1
    (ZkcExamples.Construction.SumcheckProof.verifierInputs [value] claim 0 77) = _ at zero
  rw [zero, SumcheckVerifierTerminal.terminal_equation]
  · simp [PrimitiveLibrary.HasShape, Zkc.Polynomial.Multilinear.restrictPrefixValues, wrong,
      PIR.Process.bind, PIR.Process.interpret, transform]
    rfl
  · change 1 < indexLimit; decide
  · change 0 < indexLimit; decide

/-- The full metered result and exact unread suffix are preserved for false
claims as well as honest true claims. -/
theorem false_claim (oracle : History F G → F) (value claim : F) (wrong : value ≠ claim)
    (proof : Proof F G) :
    run oracle 72 [value] claim 0 proof =
      (.returned [.data (.boolean false), .transcript ZkcExamples.Construction.SumcheckProof.context.suite []], proof) := by
  let sourcePost := fun (result : Values (Component (assignment F G))
      ZkcExamples.Construction.SumcheckProof.program.payload.entry.outputs × Domain.History (uniformCarriers F G))
      (unread : Proof F G) => result = (.cons (some false) .nil, []) ∧ unread = proof
  let post := fun (result : Domain.Result (uniformCarriers F G)) (unread : Proof F G) =>
    result.values = [.data (.boolean false), .transcript ZkcExamples.Construction.SumcheckProof.context.suite []] ∧ unread = proof
  have source : DomainVM.Passes Uniform.SourceProcess.legacyOrigin [] oracle
      (Uniform.SourceProcess.sourceView ZkcExamples.Construction.SumcheckProof.context
        ((ZkcExamples.Construction.SumcheckProof.program.participant F G 1
          (ZkcExamples.Construction.SumcheckProof.verifierInputs [value] claim 0
            ZkcExamples.Construction.SumcheckSourceConnection.routing.selectedHandle)).interpret CommonAdapter.project) [])
      proof sourcePost := by
    have zero := SumcheckSourceVerifier.verifier_zero (F := F) (G := G) (some [value]) claim
      (some ZkcExamples.Construction.SumcheckSourceConnection.routing.selectedHandle)
    change ZkcExamples.Construction.SumcheckProof.program.participant F G 1
      (ZkcExamples.Construction.SumcheckProof.verifierInputs [value] claim 0
        ZkcExamples.Construction.SumcheckSourceConnection.routing.selectedHandle) = _ at zero
    rw [zero, SumcheckVerifierTerminal.terminal_equation 1 [value] [] claim
      (by change 1 < indexLimit; decide) (by change 0 < indexLimit; decide)]
    simp [PrimitiveLibrary.HasShape, Zkc.Polynomial.Multilinear.restrictPrefixValues, wrong,
      List.foldl_nil, PIR.Process.interpret,
      Uniform.SourceProcess.sourceView, DomainVM.Passes, sourcePost]
  have passes := Uniform.ScalarCheckedBytes.connected (F := F) (G := G)
    ZkcExamples.Construction.SumcheckSourceConnection.checkedConnection rfl _ rfl (by decide +kernel)
    (SumcheckProof.physicalInputs [value] claim 0 [])
    (ZkcExamples.Construction.SumcheckProof.verifierInputs [value] claim 0
      ZkcExamples.Construction.SumcheckSourceConnection.routing.selectedHandle)
    (by kernel_rfl) (by kernel_rfl) (by derive_scalar_support) [] oracle proof sourcePost post source (by
      intro scalar actual target unread result history related good
      obtain ⟨rfl, rfl⟩ := good
      have output : actual.1 = .cons (some false) .nil := result.symm
      have empty : actual.2.history = [] := by
        simpa only [Uniform.ScalarProjection.history, List.map_eq_nil_iff] using history.symm
      obtain ⟨data, encoding, targetValues⟩ := related.values
      rw [output] at encoding
      change some [.data (.boolean false)] = some data at encoding
      cases encoding
      dsimp only [post]
      refine ⟨?_, rfl⟩
      rw [targetValues, empty]
      rfl)
  have observed : DomainVM.Passes Origin.withoutCoordinates [] oracle
      (DomainVM.observation ZkcExamples.Construction.SumcheckProof.program
        ZkcExamples.Construction.SumcheckProof.context (Code.instructions SumcheckProof.lowered.code)
        SumcheckProof.lowered.returned (SumcheckProof.physicalInputs [value] claim 0 [])) proof
      (fun returned unread => returned = [.data (.boolean false),
        .transcript ZkcExamples.Construction.SumcheckProof.context.suite []] ∧ unread = proof) := by
    rw [SumcheckProof.normalized]
    apply DomainVM.Passes.participant_observation
    rw [DomainVM.Passes.forgetCheckpoints, DomainVM.Passes.bind]
    have key : ScalarVerifier.origin ZkcExamples.Construction.SumcheckProof.participant = Origin.withoutCoordinates := rfl
    rw [key] at passes
    apply DomainVM.Passes.mono _ _ _ _ _ _ _ ?_ passes
    intro returned unread good
    simpa only [DomainVM.Passes] using good
  obtain ⟨returned, unread, good, executed⟩ := DomainVM.metered_success (F := F) (G := G)
    ZkcExamples.Construction.SumcheckProof.program ZkcExamples.Construction.SumcheckProof.context
    Origin.withoutCoordinates [] oracle SumcheckCharges.cost 72 SumcheckProof.lowered
    (SumcheckProof.physicalInputs [value] claim 0 []) proof _
    (SumcheckCharges.sufficient 72 [value] claim 0 [] proof (by simp) (by rw [SumcheckCharges.charge_eq])) observed
  obtain ⟨rfl, rfl⟩ := good
  exact executed

/-- A malformed empty table cannot produce a true zero-round decision. -/
theorem wrong_shape (oracle : History F G → F) (claim : F) (proof : Proof F G) :
    ZkcExamples.Construction.SumcheckProof.compiledVerifier (m := Id) oracle [] claim 0 [] proof =
      (.returned (some false), proof) := by
  rw [ZkcExamples.Construction.SumcheckProof.compiled_transform (m := Id) oracle [] claim 0 77]
  unfold ZkcExamples.Construction.SumcheckProof.verifier ZkcExamples.Construction.SumcheckProof.process
  have zero := SumcheckSourceVerifier.verifier_zero (F := F) (G := G) (some []) claim (some 77)
  change ZkcExamples.Construction.SumcheckProof.program.participant F G 1
    (ZkcExamples.Construction.SumcheckProof.verifierInputs [] claim 0 77) = _ at zero
  rw [zero, SumcheckVerifierTerminal.terminal_equation]
  · simp [PrimitiveLibrary.HasShape, PIR.Process.bind, PIR.Process.interpret, transform]
    rfl
  · change 0 < indexLimit; decide
  · change 0 < indexLimit; decide

end Tests.SumcheckCanonicalCompleteness
