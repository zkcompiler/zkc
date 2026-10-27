module

import ZkcExamples.Structured.OriginalArtifacts.SmallSumcheckProducerRoot
import ZkcExamples.Structured.OriginalArtifacts.SmallSumcheckValidatorRoot
import ZkcExamples.Structured.OriginalArtifacts.TwoSumsProducerRoot
import ZkcExamples.Structured.OriginalArtifacts.TwoSumsValidatorRoot
import ZkcSecurity.Generation.ConstructionBindings
meta import Lean.Util.FoldConsts
meta import Lean.Elab.Command

/-! Kernel checks of the exact outputs. These imports have no dependency on the
legacy per-root component certificates. False callback/root equations must fail. -/
set_option autoImplicit false
namespace TestsSecurity.ConstructionBindingsCertificates
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcExamples.Structured.OriginalArtifacts

open ZkcSecurity.Generation.ConstructionBindings
open ZkcExamples.Structured.SumcheckArtifacts.ArtifactBinding

def validatorLoop : Zkc.Construction.Instruction := TwoSums.validatorArtifact.instructions[1]'(by decide +kernel)
def producerLoop : Zkc.Construction.Instruction := TwoSums.producerArtifact.instructions[10]'(by decide +kernel)

/-- Syntax refusals concern method applicability, including mutations whose
semantics might agree. They do not assert semantic inequivalence. -/
def mutations (instruction : Zkc.Construction.Instruction) (fresh : Nat) : List Zkc.Construction.Instruction :=
  [{ instruction with body := instruction.body.tail },
   { instruction with operation := .loop "changed" 4 [] },
   { instruction with results := [] },
   { instruction with body := instruction.body.reverse },
   { instruction with body := instruction.body ++
     [⟨.calculate (.booleanConstant false), [], [.data .boolean], []⟩,
      ⟨.guard "extra-stop", [fresh], [], []⟩] }]

-- All six actual installed bodies: distinct captures and labels for both roles.
example : templateMatches false SmallSumcheck.context SmallSumcheck.occurrence0 5
    (SmallSumcheck.validatorArtifact.instructions[1]'(by decide +kernel)) = true := by kernel_rfl
example : templateMatches true SmallSumcheck.context SmallSumcheck.occurrence0 13
    (SmallSumcheck.producerArtifact.instructions[10]'(by decide +kernel)) = true := by kernel_rfl
example : templateMatches false TwoSums.context TwoSums.occurrence0 7 validatorLoop = true := by kernel_rfl
example : templateMatches true TwoSums.context TwoSums.occurrence0 14 producerLoop = true := by kernel_rfl
example : templateMatches false TwoSums.context TwoSums.occurrence1 12
    (TwoSums.validatorArtifact.instructions[4]'(by decide +kernel)) = true := by kernel_rfl
example : templateMatches true TwoSums.context TwoSums.occurrence1 29
    (TwoSums.producerArtifact.instructions[21]'(by decide +kernel)) = true := by kernel_rfl

-- Removed instructions, loop metadata, output sorts, order and an added stop.
example : (mutations validatorLoop 34).map
    (templateMatches false TwoSums.context TwoSums.occurrence0 7) =
    [false, false, false, false, false] := by kernel_rfl
example : (mutations producerLoop 39).map
    (templateMatches true TwoSums.context TwoSums.occurrence0 14) =
    [false, false, false, false, false] := by kernel_rfl

-- Incorrect captures, output references and occurrence labels refuse separately.
example : templateMatches false TwoSums.context TwoSums.occurrence0 8 validatorLoop = false := by kernel_rfl
example : templateMatches true TwoSums.context TwoSums.occurrence0 15 producerLoop = false := by kernel_rfl
example : templateMatches false TwoSums.context TwoSums.occurrence0 7
    { validatorLoop with operation := .loop (qualifyProtocolSite
        TwoSums.occurrence0.protocol.applicationPrefix "s15") 4 [28, 34, 27] } = false := by kernel_rfl
example : templateMatches true TwoSums.context TwoSums.occurrence0 14
    { producerLoop with operation := .loop (qualifyProtocolSite
        TwoSums.occurrence0.protocol.applicationPrefix "s15") 4 [35, 36, 37, 39, 34] } = false := by kernel_rfl
example : templateMatches false TwoSums.context TwoSums.occurrence0 7
    { validatorLoop with operation := .loop (qualifyProtocolSite
        TwoSums.occurrence0.protocol.applicationPrefix "s15") 4 [33, 28, 27] } = false := by kernel_rfl
example : templateMatches true TwoSums.context TwoSums.occurrence0 14
    { producerLoop with operation := .loop (qualifyProtocolSite
        TwoSums.occurrence0.protocol.applicationPrefix "s15") 4 [35, 37, 36, 38, 34] } = false := by kernel_rfl
example : templateMatches false TwoSums.context TwoSums.occurrence1 7 validatorLoop = false := by kernel_rfl
example : templateMatches true TwoSums.context TwoSums.occurrence1 14 producerLoop = false := by kernel_rfl

-- A changed diagnostic guard label is invisible to View.guard but is checked syntax.
example : templateMatches false TwoSums.context TwoSums.occurrence0 7
    { validatorLoop with body := validatorLoop.body.map fun step =>
      match step.operation with
      | .guard _ => { step with operation := .guard "changed-diagnostic" }
      | _ => step } = false := by kernel_rfl

#check SmallSumcheck.ValidatorCall0.body_syntax
#check SmallSumcheck.ProducerCall0.body_syntax
#check TwoSums.ValidatorCall0.body_instance
#check TwoSums.ValidatorCall1.output_instance
#check TwoSums.ProducerCall0.body_instance
#check TwoSums.ProducerCall1.output_instance

-- A semantic stop distinction, independent of syntactic method applicability.
example {F G : Type} : IsEmpty (Original.Simulation
    (fun (_ : Unit) (_ : Unit) => True)
    (fun (_ : PIR.Process (Domain.effects (uniformCarriers F G)) Unit) _ => True)
    (.done ()) (.halt .reject)) := Original.Simulation.done_not_halt () .reject

example : True := by
  fail_if_success
    have : SmallSumcheck.validatorArtifact.instructions = [] := by kernel_rfl
  fail_if_success
    have : TwoSums.producerArtifact.returned = [] := by kernel_rfl
  fail_if_success
    have : SmallSumcheck.occurrence0.draw = SmallSumcheck.occurrence0.delivery := by kernel_rfl
  fail_if_success
    have : TwoSums.occurrence0.draw = TwoSums.occurrence1.draw := by kernel_rfl
  trivial

#print axioms ZkcExamples.Structured.Generated.OriginalArtifacts.SmallSumcheckProducerSource.body_binding
#print axioms ZkcExamples.Structured.Generated.OriginalArtifacts.SmallSumcheckProducerSource.participant_binding
#print axioms ZkcExamples.Structured.Generated.OriginalArtifacts.TwoSumsProducerSource.body_binding
#print axioms ZkcExamples.Structured.Generated.OriginalArtifacts.TwoSumsProducerSource.participant_binding
#print axioms SmallSumcheck.context_checked
#print axioms SmallSumcheck.policy_checked
#print axioms SmallSumcheck.occurrence0_delivery_checked
#print axioms SmallSumcheck.ValidatorCall0.capture_size
#print axioms SmallSumcheck.ValidatorCall0.loop_operands
#print axioms SmallSumcheck.ValidatorCall0.loop_operation
#print axioms SmallSumcheck.ValidatorCall0.callback
#print axioms SmallSumcheck.ProducerCall0.callback
#print axioms TwoSums.ValidatorCall0.callback
#print axioms TwoSums.ValidatorCall1.callback
#print axioms TwoSums.ProducerCall0.callback
#print axioms TwoSums.ProducerCall1.callback
#print axioms ZkcExamples.Structured.SumcheckArtifacts.ArtifactBindingTemplates.validatorRound
#print axioms ZkcExamples.Structured.SumcheckArtifacts.OriginalProducerTemplates.producerRound
#print axioms SmallSumcheckProducerRoot.producer_source
#print axioms TwoSumsProducerRoot.producer_source
#print axioms SmallSumcheckProducerRoot.producer
#print axioms SmallSumcheckValidatorRoot.validator
#print axioms TwoSumsProducerRoot.producer
#print axioms TwoSumsValidatorRoot.validator

open Lean Elab Command in
/-- Follow stored declarations, including private auxiliaries in the actual
instance modules. Stop at the shared simulation and ordinary library boundary. -/
meta def checkSharing (callback shared : Name) : CommandElabM Unit := do
  let env ← getEnv
  let owner := env.getModuleIdxFor? callback
  let simulations := [
    `ZkcExamples.Structured.SumcheckArtifacts.ArtifactBindingTemplates.validatorRound,
    `ZkcExamples.Structured.SumcheckArtifacts.OriginalProducerTemplates.producerRound]
  let constructors := [
    `Zkc.Construction.Original.Simulation.done,
    `Zkc.Construction.Original.Simulation.halt,
    `Zkc.Construction.Original.Simulation.call,
    `Zkc.Construction.Original.Simulation.checkpoint]
  let mut pending := [callback]
  let mut seen : NameSet := {}
  while let some name := pending.head? do
    pending := pending.tail!
    if seen.contains name then continue
    seen := seen.insert name
    if simulations.contains name then
      unless name == shared do throwError "unexpected shared simulation below {callback}: {name}"
      continue
    if constructors.contains name then
      throwError "per-occurrence simulation construction below {callback}: {name}"
    let moduleName : Option Name := do
      let index ← env.getModuleIdxFor? name
      (env.header.modules[index.toNat]?).map (·.module)
    if env.getModuleIdxFor? name == owner || moduleName.any (fun moduleName =>
        moduleName.toString.startsWith "ZkcExamples.Structured.OriginalArtifacts.") then
      let information ← getConstInfo name
      pending := information.getUsedConstantsAsSet.toList ++ pending
  unless seen.contains shared do throwError "missing shared proof below {callback}: {shared}"
  logInfo m!"{callback}: one shared simulation, no per-occurrence simulation construction"

run_cmd do
  for callback in [
      `ZkcExamples.Structured.OriginalArtifacts.SmallSumcheck.ValidatorCall0.callback,
      `ZkcExamples.Structured.OriginalArtifacts.TwoSums.ValidatorCall0.callback,
      `ZkcExamples.Structured.OriginalArtifacts.TwoSums.ValidatorCall1.callback] do
    checkSharing callback `ZkcExamples.Structured.SumcheckArtifacts.ArtifactBindingTemplates.validatorRound
  for callback in [
      `ZkcExamples.Structured.OriginalArtifacts.SmallSumcheck.ProducerCall0.callback,
      `ZkcExamples.Structured.OriginalArtifacts.TwoSums.ProducerCall0.callback,
      `ZkcExamples.Structured.OriginalArtifacts.TwoSums.ProducerCall1.callback] do
    checkSharing callback `ZkcExamples.Structured.SumcheckArtifacts.OriginalProducerTemplates.producerRound

end TestsSecurity.ConstructionBindingsCertificates
