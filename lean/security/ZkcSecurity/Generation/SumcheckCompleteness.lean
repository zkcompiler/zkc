module

public import ZkcSecurity.Generation.SumcheckViews

@[expose] public section

/-! Produce honest-pair assembly from admitted source metadata and installed
mathematics. The author selects a mathematical formula law and nonvacuity proof;
input projection, every round occurrence and all structural proof composition
come from the retained pair. Generated proofs are checked independently. -/
set_option autoImplicit false
namespace ZkcSecurity.Generation.SumcheckCompleteness
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcTools.StructuredSource.Constructed (literal)

structure Output where
  moduleName : String
  subjectModule : String
  producerModule : String
  validatorModule : String
  roundsModule : String
  validatorViewModule : String
  abiModule : String
  mathematicsModule : String
  formulaLaw : String
  nonvacuityLaw : String
  fieldType : String
  groupType : String
  sampling : String

structure Input where
  metadata : SubjectABI.Metadata
  producer : Participant
  validator : Participant
  output : Output

def carrier (ty : Ty) : String :=
  match ty with
  | .boolean => "Bool"
  | .index => "Nat"
  | .field _ => "Scalar"
  | .vector _ => "List Scalar"
  | .group _ => "Group"
  | .service _ => "Option Nat"

def source (input : Input) : Except String String := do
  let { metadata, producer, validator, output } := input
  let rounds ← RoundDescriptors.discover producer validator
  let patterns ← rounds.mapM fun descriptor => do
    let some pattern := descriptor.pattern? producer validator | throw "honest-assembly-round-pattern"
    pure pattern
  let some first := patterns.head? | throw "honest-assembly-no-rounds"
  if !patterns.all (fun pattern => pattern.plan.field == first.plan.field) then
    throw "honest-assembly-multiple-fields-requires-domain-family"
  let some producerPositions := metadata.producerPositions | throw "honest-assembly-source-interface"
  let allNames := SubjectABI.names metadata.types
  let producerNames := ((List.range metadata.types.length).filter fun index =>
    producerPositions.contains index || metadata.publicPositions.contains index).map SubjectABI.inputName
  let validatorNames := metadata.publicPositions.map SubjectABI.inputName
  let view := output.validatorViewModule
  let producer := output.producerModule
  let validator := output.validatorModule
  let subject := output.subjectModule
  let abi := output.abiModule
  let field := literal first.plan.field
  let imports := [view, producer, abi, output.roundsModule, output.mathematicsModule,
    "ZkcSecurity.Families.Sumcheck.TableComponentReadbackExecution",
    "ZkcSecurity.Examples.Components.SumcheckReadbackHelpers",
    "ZkcSecurity.FiatShamir.HonestReadbackCompleteness"]
  let mut text := "module\n\n" ++ String.join (imports.map fun name => "public import " ++ name ++ "\n") ++
    "public meta import ZkcSecurity.Tools.ComponentReadback\n" ++
    "public meta import ZkcSecurity.Tools.TargetEvaluation\n\n" ++
    "@[expose] public section\nnoncomputable section\n\n" ++
    "/-! Generated from the admitted pair by Generation.SumcheckCompleteness.\n" ++
    "Installed formula mathematics is explicit; input and execution assembly\n" ++
    "is source driven and kernel checked. Regenerate; do not hand edit. -/\n" ++
    "set_option autoImplicit false\nset_option backward.isDefEq.respectTransparency false\n" ++
    "set_option maxRecDepth 20000\nset_option maxHeartbeats 8000000\n" ++
    "set_option linter.unusedSimpArgs false\n" ++
    "namespace " ++ output.moduleName ++ "\n" ++
    "open Zkc.Source Zkc.Source.Structured Zkc.Construction\n" ++
    "open ZkcSecurity.Examples.Components ZkcExamples.Structured\n" ++
    "open ZkcSecurity.Families.Sumcheck.TableComponent\n" ++
    "open ZkcSecurity.Families.Sumcheck.TableComponent.Execution ReadbackRound\n" ++
    "open ZkcSecurity.Claims.HonestPair ZkcSecurity.Domains.PrimeField\n" ++
    "open ZkcSecurity.FiatShamir\nopen " ++ subject ++ " (subject)\n" ++
    "open " ++ abi ++ "\nopen " ++ output.roundsModule ++ "\n\n" ++
    "abbrev Scalar := " ++ output.fieldType ++ "\nabbrev Group := " ++ output.groupType ++ "\n" ++
    "local instance : ∀ event : Domain.Event subject.domainModel.toCarriers,\n" ++
    "    SampleableType (Domain.Raw event) := " ++ output.sampling ++ "\n\n" ++
    "theorem readback (values : Data) (related : subject.Relation (abi.pack values))\n" ++
    "    (honest : subject.HonestInput (abi.pack values)) :\n" ++
    "    Readback\n" ++
    "      (fun _ result => Domain.acceptanceAt subject.selection.position result.values = some true)\n" ++
    "      (Domain.participant subject.domainModel " ++ subject ++ ".imported.program\n" ++
    "        subject.selection.context " ++ subject ++ ".selected.artifacts.producer (abi.producer values))\n" ++
    "      (Domain.participant subject.domainModel " ++ subject ++ ".imported.program\n" ++
    "        subject.selection.context " ++ subject ++ ".selected.artifacts.validator (abi.validator values)) := by\n" ++
    "  obtain ⟨" ++ ", ".intercalate (allNames ++ ["rfl"]) ++ "⟩ := data_surjective values\n"
  for (ty, name) in metadata.types.zip allNames do
    text := text ++ "  change " ++ carrier ty ++ " at " ++ name ++ "\n"
  text := text ++ "  change Readback _\n" ++
    "    (Domain.participant (ringModel Scalar Group) _ _ " ++ producer ++ ".artifact " ++
      SubjectABI.call "producerInputs" producerNames ++ ")\n" ++
    "    (Domain.participant (ringModel Scalar Group) _ _ " ++ validator ++ ".artifact " ++
      SubjectABI.call "validatorInputs" validatorNames ++ ")\n" ++
    "  prepare_target_readback [Scalar, Group] for subject using honestInput_iff\n" ++
    "    reading (application_read " ++ " ".intercalate allNames ++ ")\n" ++
    "    evaluating " ++ output.formulaLaw ++ "\n" ++
    "  have indexCapacity : 64 < indexLimit := by decide +kernel\n"
  let mut rules := []
  for index in List.range rounds.length do
    let round := "round" ++ toString index
    let helpers := "helpers" ++ toString index
    let rule := "sourceRule" ++ toString index
    rules := rules ++ [rule]
    text := text ++ "  have " ++ helpers ++ " := SumcheckDomainHelpers.round_helpers (K := Scalar) (H := Group)\n" ++
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
    "theorem compiled_ideal_complete : CanonicalCompleteness subject 0 :=\n" ++
    "  Readback.perfect_abi subject abi " ++ output.nonvacuityLaw ++ " readback\n\n" ++
    "end " ++ output.moduleName ++ "\n"
  pure text

end ZkcSecurity.Generation.SumcheckCompleteness
