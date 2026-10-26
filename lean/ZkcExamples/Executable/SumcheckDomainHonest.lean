module

public import ZkcExamples.Executable.SumcheckFamily
public import ZkcExamples.Executable.SumcheckCharges
public import ZkcExamples.Executable.SumcheckProof
public import ZkcExamples.Executable.SumcheckMetadata

@[expose] public section

/-! The actual retained participant instantiates the reusable canonical family.
All mathematical induction and generated round/resource correspondence belong
to the family modules. This module discharges only actual local admission facts. -/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
namespace ZkcExamples.Executable.SumcheckDomainHonest
open Zkc Zkc.Construction Zkc.Executable Zkc.Source Zkc.Source.Structured
open Zkc.Construction.Uniform Zkc.Construction.Uniform.DomainAdapter
open Zkc.Construction.ArtifactBinding
open ZkcExamples.Construction.SumcheckDomainConnection
open Zkc.Polynomial.Multilinear

abbrev transcript : SumcheckMessages.Transcript := SumcheckProof.transcript
abbrev messages {F G : Type} [Field F] (oracle : History F G → F) :=
  SumcheckMessages.honestRounds transcript oracle

/-- The actual artifact, with finite native admission and exact static witnesses. -/
def artifact : SumcheckFamily.Artifact where
  description := SumcheckCharges.programShape SumcheckProof.maximum (by decide +kernel)
  vocabulary := installed
  participant := ZkcExamples.Construction.SumcheckProof.participant
  validator := SumcheckProof.validator
  lowered := SumcheckProof.lowered
  final := SumcheckProof.nativeScope
  checked := SumcheckProof.native_checked
  instructions := by kernel_rfl
  returns := by kernel_rfl
  inputSorts := by kernel_rfl
  codeReading := by rw [SumcheckCharges.lowered_eq]; rfl
  returned := by kernel_rfl
  coordinate := SumcheckProof.coordinate
  plan := SumcheckProof.plan_eq
  admitted := SumcheckProof.admitted

/-- Every selected occurrence, schema and typed request is checked against the
actual retained templates. These facts are independent of the static maximum. -/
theorem programOccurrences (maximum : Nat) (small : maximum < 64) :
    SumcheckFamily.Source.Occurrences (SumcheckCharges.programShape maximum small) where
  firstSchema := by kernel_rfl
  secondSchema := by kernel_rfl
  first := fun _ => by kernel_rfl
  second := fun _ => by kernel_rfl
  draw := fun _ => by kernel_rfl
  delivery := fun _ => by kernel_rfl
  firstRequest := by kernel_rfl
  secondRequest := by kernel_rfl
  deliveryRequest := by kernel_rfl
  firstKey := fun _ => by kernel_rfl
  secondKey := fun _ => by kernel_rfl
  drawKey := fun _ => by kernel_rfl
  deliveryKey := fun _ => by kernel_rfl

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- Local mathematical helper laws, derived from actual closed Domain calls.
Only bounded shaped terminal arguments are required by the family theorem. -/
theorem programHelpers (maximum : Nat) (small : maximum < 64) :
    SumcheckFamily.Source.Helpers (F := F) (G := G) (SumcheckCharges.programShape maximum small) where
  empty := empty_helper
  append := append_helper
  check := by
    intro values point claim pointSmall shaped
    change Domain.callHelper (ringModel F G) ZkcExamples.Construction.SumcheckProof.program
      ZkcExamples.Structured.SumcheckHelperBodies.checkHelper.name [.data .boolean]
      [.data (.vector "bls12-381.fr" values), .data (.vector "bls12-381.fr" point),
        .data (.field "bls12-381.fr" claim)] = _
    rw [check_helper]
    have pointBound : point.length < indexLimit := lt_trans pointSmall (by decide)
    have vectorBound : values.length < indexLimit := by rw [shaped]; exact SumcheckHelpers.indexLimit_pow pointSmall
    simp only [pointBound, pointSmall, vectorBound, ite_true]
    have decoded : (ofList? (0 + point.length) values).isSome :=
      (ofList?_isSome_iff values).mpr (by simpa only [Nat.zero_add] using shaped)
    obtain ⟨table, tableEq⟩ := Option.isSome_iff_exists.mp decoded
    rw [Zkc.Protocols.Sumcheck.Multilinear.check, tableEq,
      restrictPrefixValues_complete values point table tableEq, List.sum_singleton]

/-- The retained helper prices generate the exact original 68 + 59r budget. -/
theorem programPrices (maximum : Nat) (small : maximum < 64) :
    SumcheckFamily.Source.Prices (SumcheckCharges.programShape maximum small)
      (helperCost installed SumcheckProof.validator (F := F) (G := G)) 2 where
  empty := helperCost_le installed SumcheckProof.validator
    (show helperBound SumcheckProof.validator SumcheckCharges.names.emptyHelper = some 2 by kernel_rfl) []
  append := fun _ _ => helperCost_le installed SumcheckProof.validator
    (show helperBound SumcheckProof.validator SumcheckCharges.names.appendHelper = some 2 by kernel_rfl) _
  check := fun _ _ _ small shaped => SumcheckHelpers.check_cost small shaped

/-- No whole-run success or equality is supplied by the concrete instance. -/
theorem realization : SumcheckFamily.Realization (F := F) (G := G) artifact 2 where
  occurrences := programOccurrences _ _
  helpers := programHelpers _ _
  prices := programPrices _ _
  prepared := SumcheckProof.domain_prepared

/-- Concrete observation success is an instance of the shared mathematical
proof, preserving the original postcondition and exact unread suffix. -/
theorem observation_passes (oracle : History F G → F) (initial : History F G)
    (values : List F) (rounds : Nat) (admitted : rounds ≤ SumcheckProof.maximum)
    (shaped : values.length = 2 ^ rounds) :
    DomainVM.Passes Origin.withoutCoordinates initial oracle
      (DomainVM.observation ZkcExamples.Construction.SumcheckProof.program
        ZkcExamples.Construction.SumcheckProof.context
        (Code.instructions SumcheckProof.lowered.code) SumcheckProof.lowered.returned
        (frame values values.sum rounds []))
      ((messages oracle initial values rounds).map (.field "bls12-381.fr"))
      (fun returned unread => returned[0]? = some (.data (.boolean true)) ∧ unread = [] ∧
        ∃ history, returned = [.data (.boolean true), .transcript ZkcExamples.Construction.SumcheckProof.context.suite history] ∧
          ∃ suffix, readbackHistory Origin.withoutCoordinates history = some suffix) := by
  rw [SumcheckCharges.lowered_eq]
  change DomainVM.Passes Origin.withoutCoordinates initial oracle
    (DomainVM.observation artifact.description.program artifact.description.context
      (Code.instructions (SumcheckShape.code artifact.description.names artifact.description.maximum)) [8,7]
      (SumcheckFamily.ProgramShape.inputs artifact.description values values.sum rounds [])) _ _
  rw [SumcheckFamily.code_instructions]
  have realized := realization (F := F) (G := G)
  apply DomainVM.Passes.mono Origin.withoutCoordinates initial oracle _ _ _ _ ?_
    (SumcheckFamily.Source.observation_passes artifact.description realized.occurrences realized.helpers
      oracle initial values rounds admitted shaped)
  intro returned unread good
  obtain ⟨rfl, history, rfl, suffix, mapped⟩ := good
  exact ⟨rfl, rfl, history, rfl, suffix, mapped⟩

end ZkcExamples.Executable.SumcheckDomainHonest
