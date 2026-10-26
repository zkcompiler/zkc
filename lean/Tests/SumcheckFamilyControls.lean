module

public import ZkcExamples.Executable.SumcheckCompleteness
public import Mathlib.Algebra.Field.ZMod

@[expose] public section

/-! A second finite native realization and focused refusal controls. The
alternate entry is a constructed test fixture; it makes no compiler-export or
source-security claim. Both realizations validate actual framed native bytes. -/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
namespace Tests.SumcheckFamilyControls
open Zkc Zkc.Construction Zkc.Executable Zkc.Source
open Zkc.Construction.Uniform Zkc.Construction.Uniform.DomainAdapter
open Zkc.Construction.ArtifactBinding
open ZkcExamples.Executable

abbrev actual : SumcheckFamily.Artifact := SumcheckDomainHonest.artifact

def alternateEntry : String := "sumcheck.family.alternate"

def alternateTemplate (template : Template) : Template := { template with entry := alternateEntry }

def alternateNames : SumcheckShape.Names :=
  { actual.description.names with
    firstMessage := alternateTemplate actual.description.names.firstMessage
    secondMessage := alternateTemplate actual.description.names.secondMessage
    draw := alternateTemplate actual.description.names.draw
    delivery := alternateTemplate actual.description.names.delivery }

def alternateContext : Context :=
  { actual.description.context with entry := alternateEntry }

def alternateDescription : SumcheckFamily.ProgramShape.Description :=
  ⟨actual.description.program, alternateContext, alternateNames, 3, by decide, rfl⟩

def alternateParticipant : Participant :=
  { actual.participant with
    policy := { actual.participant.policy with entry := alternateEntry }
    instructions := SumcheckShape.instructions alternateNames 3 }

def alternateFunction (function : Zkc.Executable.Function) : Zkc.Executable.Function :=
  { function with body := function.body.map fun
    | .operation site binding parameters inputs outputs =>
        .operation site binding (parameters.map fun
          | .template template => .template (alternateTemplate template)
          | parameter => parameter) inputs outputs
    | step => step }

def alternateValidator : Validator :=
  { actual.validator with
    entry := alternateEntry
    functions := actual.validator.functions.map alternateFunction
    body := actual.validator.body.map fun
      | .loop site count _ induction carried captures body outputs =>
          .loop site count 3 induction carried captures body outputs
      | action => action }

def alternateLowered : Lowered :=
  ⟨SumcheckShape.code alternateNames 3, [8,7], [.loop 2 3 [.receive actual.coordinate, .receive actual.coordinate]]⟩

/-- A fresh finite check, not a reused semantic equation, admits this fixture. -/
theorem alternate_checked : DomainVM.checkNativeLowering alternateDescription.program alternateContext
    installed alternateParticipant alternateValidator = .ok (alternateLowered, actual.final) := by kernel_rfl

def alternate : SumcheckFamily.Artifact where
  description := alternateDescription
  vocabulary := installed
  participant := alternateParticipant
  validator := alternateValidator
  lowered := alternateLowered
  final := actual.final
  checked := alternate_checked
  instructions := rfl
  returns := actual.returns
  inputSorts := actual.inputSorts
  codeReading := rfl
  returned := rfl
  coordinate := actual.coordinate
  plan := rfl
  admitted := fun _ _ _ => rfl

/-- The alternate context changes the actual projected oracle keys. -/
theorem entries_differ : actual.description.context.entry ≠ alternate.description.context.entry := by decide +kernel

theorem oracle_keys_differ :
    (SumcheckFamily.Source.transcript actual.description).draw ≠
      (SumcheckFamily.Source.transcript alternate.description).draw := by decide +kernel

theorem alternateOccurrences : SumcheckFamily.Source.Occurrences alternate.description where
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

abbrev helperNames : List String := [actual.description.names.emptyHelper,
  actual.description.names.appendHelper, actual.description.names.checkHelper]

theorem helper_functions_agree : ∀ name ∈ helperNames, FunctionAgrees actual.validator alternateValidator name := by
  intro name member
  simp only [helperNames, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  all_goals exact functionAgrees_of (by kernel_rfl) (by decide +kernel)

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

theorem alternateRealization : SumcheckFamily.Realization (F := F) (G := G) alternate 2 where
  occurrences := alternateOccurrences
  helpers := {
    empty := (SumcheckDomainHonest.realization (F := F) (G := G)).helpers.empty
    append := (SumcheckDomainHonest.realization (F := F) (G := G)).helpers.append
    check := (SumcheckDomainHonest.realization (F := F) (G := G)).helpers.check }
  prices := {
    empty := by
      change helperCost installed alternateValidator actual.description.names.emptyHelper [] ≤ 2
      rw [← helperCost_agrees installed (helper_functions_agree actual.description.names.emptyHelper (by simp [helperNames])) []]
      exact (SumcheckDomainHonest.realization (F := F) (G := G)).prices.empty
    append := by
      intro point answer
      change helperCost installed alternateValidator actual.description.names.appendHelper
        [.vector actual.description.names.scalar point, .data (.field actual.description.names.scalar answer)] ≤ 2
      rw [← helperCost_agrees installed (helper_functions_agree actual.description.names.appendHelper (by simp [helperNames])) _]
      exact (SumcheckDomainHonest.realization (F := F) (G := G)).prices.append point answer
    check := by
      intro values point claim small shaped
      change helperCost installed alternateValidator actual.description.names.checkHelper
        [.vector actual.description.names.scalar values, .vector actual.description.names.scalar point,
          .data (.field actual.description.names.scalar claim)] = 62 + 20 * point.length
      rw [← helperCost_agrees installed (helper_functions_agree actual.description.names.checkHelper (by simp [helperNames])) _]
      exact (SumcheckDomainHonest.realization (F := F) (G := G)).prices.check values point claim small shaped }
  prepared := by
    have names : Instruction.helperList alternate.participant.instructions = helperNames := by kernel_rfl
    rw [names]
    intro name member
    apply prepared_agrees installed (helper_functions_agree name member)
    apply (SumcheckDomainHonest.realization (F := F) (G := G)).prepared name
    have original : Instruction.helperList actual.participant.instructions = helperNames := by kernel_rfl
    rwa [original]

/-- Three rounds at a different root and different oracle keys, on arbitrary
field values, initial history, oracle, and coordinate-only codec inverse. -/
theorem alternate_three_accepted (oracle : History F G → F)
    (decode : PhysicalType → List UInt8 → Option (Payload F G)) (encode : F → List UInt8)
    (roundtrip : ∀ value, decode alternate.coordinate (encode value) = some (.field alternate.description.names.scalar value))
    (bounded : ∀ value, (encode value).length ≤ proofLimit) (binding : List UInt8) (bindingLength : binding.length = 32)
    (values : List F) (shaped : values.length = 8) (initial : History F G) :
    validate (m := Id) alternate.vocabulary alternate.validator alternate.description.context oracle decode 245 binding 0
      (alternate.dataInputs values values.sum 3) initial
      (SumcheckMessages.honestBytes encode binding
        (SumcheckMessages.honestRounds (SumcheckFamily.Source.transcript alternate.description) oracle initial values 3)) = true := by
  have success := SumcheckFamily.honest_accepted (F := F) (G := G) alternate 2 alternateRealization oracle decode encode roundtrip bounded 245 binding
    bindingLength values 3 (by decide) (show values.length = 2 ^ 3 by simpa using shaped) initial (by decide)
  exact success

/-- Same family, zero rounds, nonempty initial history permitted. -/
theorem alternate_zero_accepted (oracle : History F G → F)
    (decode : PhysicalType → List UInt8 → Option (Payload F G)) (encode : F → List UInt8)
    (roundtrip : ∀ value, decode alternate.coordinate (encode value) = some (.field alternate.description.names.scalar value))
    (bounded : ∀ value, (encode value).length ≤ proofLimit) (binding : List UInt8) (bindingLength : binding.length = 32)
    (value : F) (initial : History F G) :
    validate (m := Id) alternate.vocabulary alternate.validator alternate.description.context oracle decode 68 binding 0
      (alternate.dataInputs [value] value 0) initial (SumcheckMessages.honestBytes encode binding []) = true := by
  have success := SumcheckFamily.honest_accepted (F := F) (G := G) alternate 2 alternateRealization oracle decode encode roundtrip bounded 68 binding
    bindingLength [value] 0 (by decide) (by simp) initial (by decide)
  simpa only [List.sum_singleton, SumcheckMessages.honestRounds] using success

end Tests.SumcheckFamilyControls
