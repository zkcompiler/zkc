module

public import ZkcSecurity.Generation.SumcheckViews
public import ZkcSecurity.Generation.UniformRoot

@[expose] public section

/-! Produce honest-pair assembly from admitted source metadata and installed
mathematics. The author selects a mathematical formula law and nonvacuity proof;
input projection, every round occurrence and all structural proof composition
come from the retained pair. Generated proofs are checked independently. -/
set_option autoImplicit false
namespace ZkcSecurity.Generation.SumcheckCompleteness
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcTools.StructuredSource.Constructed (literal)

structure Output extends toUniform : UniformRoot.Output where
  roundsModule : String
  validatorViewModule : String
  mathematicsModule : String
  formulaLaw : String
  nonvacuityLaw : String

structure Input where
  metadata : SubjectABI.Metadata
  producer : Participant
  validator : Participant
  output : Output

def source (input : Input) : Except String String := do
  let { metadata, producer, validator, output } := input
  let rounds ← RoundDescriptors.discover producer validator
  let patterns ← rounds.mapM fun descriptor => do
    let some pattern := descriptor.pattern? producer validator | throw "honest-assembly-round-pattern"
    pure pattern
  let some first := patterns.head? | throw "honest-assembly-no-rounds"
  if !patterns.all (fun pattern => pattern.plan.field == first.plan.field) then
    throw "honest-assembly-multiple-fields-requires-domain-family"
  let allNames := SubjectABI.names metadata.types
  let view := output.validatorViewModule
  let producer := output.producerModule
  let validator := output.validatorModule
  let subject := output.subjectModule
  let field := literal first.plan.field
  let mut text := "  prepare_target_readback [Scalar, Group] for subject using honestInput_iff\n" ++
    "    reading (application_read " ++ " ".intercalate allNames ++ ")\n" ++
    "    evaluating " ++ output.formulaLaw ++ "\n" ++
    "  have indexCapacity : 64 < indexLimit := by decide +kernel\n"
  let mut rules := []
  for index in List.range rounds.length do
    let round := "round" ++ toString index
    let helpers := "helpers" ++ toString index
    let rule := "sourceRule" ++ toString index
    rules := rules ++ [rule]
    text := text ++ "  have " ++ helpers ++ " := DomainHelpers.round_helpers (K := Scalar) (H := Group)\n" ++
      "    " ++ subject ++ ".imported.program " ++ view ++ ".helper_bodies " ++ round ++ ".plan rfl rfl rfl rfl\n" ++
      "  have " ++ rule ++ " := ReadbackRound.sourceLoopBind\n" ++
      "    (A := Domain.Result (ringModel Scalar Group).toCarriers) (B := Domain.Result (ringModel Scalar Group).toCarriers)\n" ++
      "    " ++ round ++ ".plan " ++ field ++ " rfl " ++ subject ++ ".imported.program " ++ helpers ++ "\n" ++
      "    subject.selection.context " ++ round ++ ".sites _ _ _ _\n" ++
      "    (" ++ round ++ ".producer_block Scalar Group _ subject.selection.context rfl)\n" ++
      "    (" ++ round ++ ".validator_block Scalar Group _ subject.selection.context rfl)\n" ++
      "  dsimp only [" ++ round ++ ".producerCapture, " ++ round ++ ".validatorCapture, " ++ round ++ ".descriptor] at " ++ rule ++ "\n" ++
      "  simp only [" ++ view ++ ".context_suite, Nat.reduceAdd] at " ++ rule ++ "\n"
  text := text ++ "  compose_component_readback [" ++ ", ".intercalate rules ++ "]\n" ++
    "    normalizing (\n" ++
    "      try (\n        rw [" ++ producer ++ ".participant_eq, " ++ validator ++ ".participant_eq]\n" ++
    "        simp only [producerInputs, validatorInputs]\n" ++
    "        unfold_component_bodies [" ++ producer ++ ".view, " ++ validator ++ ".view])\n" ++
    "      normalize_sumcheck_readback [Scalar, Group, " ++ subject ++ ".imported.program, " ++ view ++ ".helper_bodies]\n" ++
    "        unfolding [" ++ view ++ ".context_suite])\n" ++
    "    solving (first | rfl | assumption | omega)\n    finishing rfl\n\n" ++
    ""
  let presentation ← UniformRoot.presentation metadata output.toUniform "Readback"
  RootCompleteness.source metadata output.toUniform.toOutput {
    imports := [view, output.roundsModule, output.mathematicsModule,
      "ZkcSecurity.Families.Sumcheck.TableComponentReadbackExecution",
      "ZkcSecurity.Realizations.Sumcheck.ReadbackHelpers",
      "ZkcSecurity.FiatShamir.HonestReadbackCompleteness"]
    metaImports := ["ZkcSecurity.Tools.ComponentReadback", "ZkcSecurity.Tools.TargetEvaluation"]
    opens := ["ZkcSecurity.Domains.PrimeField", "ZkcSecurity.Realizations.Sumcheck ZkcExamples.Structured",
      "ZkcSecurity.Families.Sumcheck.TableComponent",
      "ZkcSecurity.Families.Sumcheck.TableComponent.Execution ReadbackRound", output.roundsModule]
    description := "Installed table mathematics and realization laws are explicit."
    nonvacuityLaw := output.nonvacuityLaw
    declarations := UniformRoot.declarations output.toUniform
    body := presentation ++ text }

end ZkcSecurity.Generation.SumcheckCompleteness
