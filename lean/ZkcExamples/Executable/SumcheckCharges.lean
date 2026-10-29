module

public import ZkcExamples.Executable.SumcheckFamilyBudget
public import Zkc.Executable.HelperCosts
public import Zkc.Executable.DomainFitsRules
public import Zkc.Executable.DomainSuccess
public import ZkcExamples.Executable.SumcheckProofFacts
public import ZkcExamples.Executable.SumcheckHelpers
public import ZkcExamples.Executable.SumcheckShape
public import ZkcExamples.Executable.SumcheckCheckedRound
public import ZkcExamples.Executable.SumcheckProof
public import ZkcExamples.Structured.SumcheckArtifacts.DomainHelpers
public meta import Zkc.Construction.ArtifactBindingTactic

@[expose] public section

/-! Canonical budgets for the retained Sumcheck round and arbitrary loop bounds.
Only the final specialization selects the retained Entry's static maximum.
The helpers are the admitted program's Domain helpers; their charges are the
actual executable local-function costs at the reached arguments. -/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
namespace ZkcExamples.Executable.SumcheckCharges
open Zkc Zkc.Construction Zkc.Executable Zkc.Source
open Zkc.Construction.Uniform
open Zkc.Construction.ArtifactBinding
open ZkcExamples.Structured
open SumcheckShape SumcheckFamily

-- Compose the generic transport laws without reducing the concrete evaluator.
attribute [local irreducible] PIR.Yields DomainVM.Continues

abbrev validator : Validator := SumcheckProof.validator
abbrev context : Context := ZkcExamples.Construction.SumcheckProof.context
abbrev scalar : String := "bls12-381.fr"

abbrev coordinate : PhysicalType := ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩
def maximum : Nat := maximumOf ZkcExamples.Construction.SumcheckProof.participant.instructions

/-- Names read from the actual retained participant. -/
abbrev names : Names := Names.of ZkcExamples.Construction.SumcheckProof.participant.instructions

def lowered (maximum : Nat) : Lowered :=
  ⟨code names maximum, [13, 10], [.loop 2 maximum [.receive coordinate, .receive coordinate]]⟩

-- The generated facts expose the same executable reading, including returns.
theorem lowered_eq : ZkcExamples.Executable.SumcheckProof.lowered = lowered maximum := by kernel_rfl

theorem round_charge : Code.charges (helperBound ZkcExamples.Executable.SumcheckProof.validator) (roundCode names) = some 38 := by decide +kernel

def roundCharge : Nat :=
  (Code.charges (helperBound ZkcExamples.Executable.SumcheckProof.validator) (roundCode names)).getD 0

def charge (rounds : Nat) : Nat :=
  1 + 2 + 1 + 1 + 1 + rounds * (roundCharge + 1) + 1 + 1 + 1 + (62 + 20 * rounds) + 1

theorem charge_eq (rounds : Nat) : charge rounds = 72 + 59 * rounds := by
  simp only [charge, roundCharge, round_charge, Option.getD_some]
  omega

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

abbrev cost : String → List (Value F G) → Nat := helperCost installed ZkcExamples.Executable.SumcheckProof.validator

def carried (point : List F) (claim : F) (history : Domain.History (Structured.uniformCarriers F G)) : DomainVM.Environment F G :=
  [.data (.vector "bls12-381.fr" point), .data (.field "bls12-381.fr" claim), .transcript context.suite history]

def Carried (count : Nat) (values : DomainVM.Environment F G) (_ : Proof F G) : Prop :=
  ∃ point claim history, values = carried point claim history ∧ point.length = count

theorem round_yields (values : List F) (publicClaim : F) (rounds : Nat)
    (initial : Domain.History (Structured.uniformCarriers F G))
    (index : Nat) (point : List F) (claim : F) (history : Domain.History (Structured.uniformCarriers F G)) :
    PIR.Yields (fun final => ∀ next,
      Domain.read final yielded = some next → Domain.sortsMatch (carriedSorts names) next = true →
        ∀ unread, Carried (point.length + 1) next unread)
      (Domain.evaluate (Structured.ringModel F G) ZkcExamples.Construction.SumcheckProof.program context
        (roundBody names) (SumcheckCheckedRound.inputs values publicClaim rounds initial index point claim history)) := by
  have source := SumcheckCheckedRound.target_yields values publicClaim rounds initial index point claim history
  refine source.mono ?_
  intro final good next read _ unread
  obtain ⟨nextPoint, nextClaim, suffix, found, length⟩ := good
  rw [found] at read
  cases read
  exact ⟨nextPoint, nextClaim, suffix, rfl, length⟩

/-- Source full-return invariants and the actual Code charge reading establish
round sufficiency for every reply and proof suffix at the reached typed prefix. -/
theorem round_fits (values : List F) (publicClaim : F) (rounds : Nat)
    (initial : Domain.History (Structured.uniformCarriers F G))
    (index : Nat) (point : List F) (claim : F) (history : Domain.History (Structured.uniformCarriers F G))
    (proof : Proof F G) (used budget : Nat) (within : used + 38 ≤ budget) :
    DomainVM.FitsK ZkcExamples.Construction.SumcheckProof.program context cost budget (roundCode names)
      (SumcheckCheckedRound.inputs values publicClaim rounds initial index point claim history) proof used
      (fun final unread charged => charged ≤ used + 38 ∧ ∀ next,
        Domain.read final yielded = some next →
          Domain.sortsMatch (carriedSorts names) next = true → Carried (point.length + 1) next unread) := by
  apply ScalarSourceCost.fits _ _ cost (helperBound validator)
    (fun _ _ bound _ => helperCost_le installed validator bound _) budget
    (roundCode names) 38 round_charge _ proof used _ (by
      change ScalarSourceCost.schema
        [.data (.vector "bls12-381.fr"), .data (.field "bls12-381.fr"), .data .index,
          .transcript context.suite, .data (.vector "bls12-381.fr"), .data (.field "bls12-381.fr"),
          .data (.vector "bls12-381.fr"), .data (.field "bls12-381.fr"), .data .index,
          .data (.vector "bls12-381.fr"), .data (.field "bls12-381.fr"), .transcript context.suite]
        (roundCode names) = true
      decide +kernel) within
  rw [SumcheckShape.roundCode_instructions]
  apply DomainVM.Continues.of_yields_all_proofs
  exact (round_yields values publicClaim rounds initial index point claim history).mono
    (fun _ good unread next read sorted => good next read sorted unread)

/-- Actual program instance of the parameterized canonical family. -/
def programShape (maximum : Nat) (small : maximum < 64) : ProgramShape.Description :=
  ⟨ZkcExamples.Construction.SumcheckProof.program, ZkcExamples.Construction.SumcheckProof.context,
    names, maximum, small, rfl⟩

theorem programContract (maximum : Nat) (small : maximum < 64) :
    ProgramShape.Contract (programShape maximum small) (cost (F := F) (G := G)) 38 where
  pending := SumcheckArtifacts.DomainHelpers.pending ZkcExamples.Construction.SumcheckProof.program
    (by change SumcheckPendingLaws.Bodies SumcheckCheckedRound.program.payload.definitions
        rw [SumcheckCheckedRound.source_payload]
        exact SumcheckSourceVerifier.claimBodies)
  openClaim := SumcheckArtifacts.DomainHelpers.claim_identity ZkcExamples.Construction.SumcheckProof.program
    SumcheckPendingBodies.openClaimHelper.name
    (by change Structured.BodyIn SumcheckCheckedRound.program.payload.definitions _ _
        rw [SumcheckCheckedRound.source_payload]
        exact SumcheckSourceVerifier.claimBodies.openClaim)
  atPrefix := SumcheckArtifacts.DomainHelpers.claim_identity ZkcExamples.Construction.SumcheckProof.program
    SumcheckPendingBodies.atPrefixHelper.name
    (by change Structured.BodyIn SumcheckCheckedRound.program.payload.definitions _ _
        rw [SumcheckCheckedRound.source_payload]
        exact SumcheckSourceVerifier.claimBodies.atPrefix)
  pendingCost := fun _ => helperCost_le installed ZkcExamples.Executable.SumcheckProof.validator
    (show helperBound ZkcExamples.Executable.SumcheckProof.validator names.pendingHelper = some 2 by kernel_rfl) _
  openClaimCost := fun _ _ => helperCost_le installed ZkcExamples.Executable.SumcheckProof.validator
    (show helperBound ZkcExamples.Executable.SumcheckProof.validator names.openClaimHelper = some 1 by kernel_rfl) _
  atPrefixCost := fun _ _ => helperCost_le installed ZkcExamples.Executable.SumcheckProof.validator
    (show helperBound ZkcExamples.Executable.SumcheckProof.validator names.atPrefixHelper = some 1 by kernel_rfl) _
  checkCost := fun _ _ _ small shaped => SumcheckHelpers.check_cost small shaped
  round := round_fits

/-- The retained schedule generalized only in its static maximum. All typed
public claims, proof streams and query replies are covered; a refused loop
bound has no post-entry charge obligation. -/
theorem sufficient_family (maximum : Nat) (small : maximum < 64) (budget : Nat)
    (values : List F) (claim : F) (rounds : Nat)
    (history : Domain.History (Structured.uniformCarriers F G)) (proof : Proof F G)
    (shaped : values.length = 2 ^ rounds) (fits : charge rounds ≤ budget) :
    DomainVM.Sufficient ZkcExamples.Construction.SumcheckProof.program
      ZkcExamples.Construction.SumcheckProof.context cost budget (lowered maximum)
      (ZkcExamples.Executable.SumcheckProof.physicalInputs values claim rounds history) proof := by
  exact ProgramShape.sufficient (programShape maximum small) cost 38 (programContract maximum small)
    budget values claim rounds history proof shaped (by simpa only [charge_eq] using fits)

/-- Canonical sufficiency for the exact retained Entry, with the retained
interpreted-byte contract's input shape and budget assumptions. -/
theorem sufficient (budget : Nat) (values : List F) (claim : F) (rounds : Nat)
    (history : Domain.History (Structured.uniformCarriers F G)) (proof : Proof F G)
    (shaped : values.length = 2 ^ rounds) (fits : charge rounds ≤ budget) :
    DomainVM.Sufficient ZkcExamples.Construction.SumcheckProof.program
      ZkcExamples.Construction.SumcheckProof.context cost budget ZkcExamples.Executable.SumcheckProof.lowered
      (ZkcExamples.Executable.SumcheckProof.physicalInputs values claim rounds history) proof := by
  rw [lowered_eq]
  exact sufficient_family maximum (by decide +kernel) budget values claim rounds history proof shaped fits



end ZkcExamples.Executable.SumcheckCharges
