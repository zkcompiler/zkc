module

public import ZkcExamples.Executable.SumcheckCompleteness

@[expose] public section

/-! Symbolic consumers and negative controls for the full retained Sumcheck. -/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
namespace Tests.SumcheckCanonicalCompleteness
open Zkc Zkc.Construction Zkc.Executable Zkc.Source
open ZkcExamples.Executable
open ZkcExamples.Construction.SumcheckDomainConnection
open Zkc.Construction.Uniform.DomainAdapter

attribute [local irreducible] DomainVM.Sufficient

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

abbrev run (oracle : History F G → F) (budget : Nat) (values : List F) (claim : F)
    (rounds : Nat) (proof : Proof F G) :=
  DomainVM.metered (m := Id) ZkcExamples.Construction.SumcheckProof.program
    ZkcExamples.Construction.SumcheckProof.context Origin.withoutCoordinates [] oracle
    SumcheckCharges.cost budget SumcheckProof.lowered (frame values claim rounds []) proof

/-- The consumer keeps the round count symbolic and uses the actual Entry. -/
theorem variable_honest (oracle : History F G → F) (values : List F) (rounds : Nat)
    (admitted : rounds ≤ SumcheckProof.maximum) (shaped : values.length = 2 ^ rounds) :
    ∃ history suffix, run oracle (68 + 59 * rounds) values values.sum rounds
      ((SumcheckCompleteness.honestRounds oracle [] values rounds).map (.field "bls12-381.fr")) =
      (.returned [.data (.boolean true), .transcript ZkcExamples.Construction.SumcheckProof.context.suite history], []) ∧
      readbackHistory Origin.withoutCoordinates history = some suffix :=
  SumcheckCompleteness.honest_metered oracle _ values rounds admitted shaped []
    (by rw [SumcheckCharges.charge_eq])

theorem zero_honest (oracle : History F G → F) (value : F) :
    ∃ history suffix, run oracle 68 [value] value 0 [] =
      (.returned [.data (.boolean true), .transcript ZkcExamples.Construction.SumcheckProof.context.suite history], []) ∧
      readbackHistory Origin.withoutCoordinates history = some suffix := by
  simpa [SumcheckCompleteness.honestRounds, SumcheckDomainHonest.messages, SumcheckMessages.honestRounds] using
    variable_honest oracle [value] 0 (by decide +kernel) (by simp)

theorem one_honest (oracle : History F G → F) (low high : F) :
    ∃ history suffix, run oracle 127 [low, high] (low + high) 1
      ((SumcheckCompleteness.honestRounds oracle [] [low, high] 1).map (.field "bls12-381.fr")) =
      (.returned [.data (.boolean true), .transcript ZkcExamples.Construction.SumcheckProof.context.suite history], []) ∧
      readbackHistory Origin.withoutCoordinates history = some suffix := by
  simpa using variable_honest oracle [low, high] 1 (by decide +kernel) (by simp)

theorem two_honest (oracle : History F G → F) (a b c d : F) :
    ∃ history suffix, run oracle 186 [a,b,c,d] (a + (b + (c + d))) 2
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
      ZkcExamples.Construction.SumcheckProof.context SumcheckCharges.cost (68 + 59 * rounds)
      (SumcheckFamily.lowered maximum) (frame values claim rounds history) proof :=
  SumcheckFamily.sufficient_family maximum small _ values claim rounds history proof shaped
    (by rw [SumcheckFamily.charge_eq])

/-- Insufficient budget stops before even the empty-point helper. -/
theorem zero_budget (oracle : History F G → F) (values : List F) (claim : F)
    (rounds : Nat) (proof : Proof F G) :
    run oracle 0 values claim rounds proof = (.stopped .exhausted, proof) := by
  unfold run
  rw [SumcheckFamily.lowered_eq]
  simp [SumcheckFamily.lowered, SumcheckShape.code, DomainVM.metered,
    DomainVM.meteredK, DomainVM.meteredStep]
  rfl

/-- Budget sufficiency does not force a returned Boolean to be true. The
zero-round actual terminal check returns false on a false public claim, and
preserves the entire supplied unread suffix. -/
theorem false_claim (oracle : History F G → F) (value claim : F) (wrong : value ≠ claim)
    (proof : Proof F G) :
    run oracle 68 [value] claim 0 proof =
      (.returned [.data (.boolean false), .transcript ZkcExamples.Construction.SumcheckProof.context.suite []], proof) := by
  have checked : Zkc.Protocols.Sumcheck.Multilinear.check [value] (Fin.elim0 : Fin 0 → F) claim = false := by
    apply Bool.eq_false_iff.mpr
    intro accepted
    have same := Zkc.Protocols.Sumcheck.Multilinear.check_zero_iff [value] claim |>.mp accepted
    exact wrong (List.singleton_inj.mp same)
  have point : Zkc.Polynomial.Quadratic.point 0 (Zkc.Polynomial.coordinates 0 []) Fin.elim0 =
      (Fin.elim0 : Fin 0 → F) := funext fun index => Fin.elim0 index
  have passes : DomainVM.Passes Origin.withoutCoordinates ([] : History F G) oracle
      (rootProcess [value] claim 0 []) proof
      (fun returned unread => returned =
        [.data (.boolean false), .transcript ZkcExamples.Construction.SumcheckProof.context.suite []] ∧ unread = proof) := by
    simp [rootProcess, reduce, PIR.Process.bind, terminal, Structured.indexLimit, DomainVM.Passes, point, checked]
  obtain ⟨returned, unread, good, executed⟩ := DomainVM.metered_success (F := F) (G := G)
    ZkcExamples.Construction.SumcheckProof.program ZkcExamples.Construction.SumcheckProof.context
    Origin.withoutCoordinates [] oracle SumcheckCharges.cost 68 SumcheckProof.lowered
    (frame [value] claim 0 []) proof _
    (SumcheckCharges.sufficient (F := F) (G := G) 68 [value] claim 0 [] proof (by simp)
      (by rw [SumcheckFamily.charge_eq]))
    (SumcheckDomainHonest.of_root_passes (F := F) (G := G) oracle [] [value] claim 0 [] proof _ passes)
  rcases good with ⟨rfl, rfl⟩
  exact executed

omit [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- Wrong-shaped tables cannot have a true terminal decision even with no
messages required. This is the actual all-input source-connected root. -/
theorem wrong_shape (oracle : History F G → F) (claim : F) (proof : Proof F G) :
    ¬ DomainVM.Passes Origin.withoutCoordinates ([] : History F G) oracle
      (rootProcess [] claim 0 []) proof
      (fun returned _ => returned[0]? = some (.data (.boolean true))) := by
  simp [rootProcess, reduce, PIR.Process.bind, terminal, Structured.indexLimit, DomainVM.Passes,
    Zkc.Protocols.Sumcheck.Multilinear.check, Zkc.Polynomial.Multilinear.ofList?]

end Tests.SumcheckCanonicalCompleteness
