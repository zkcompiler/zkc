module

public import ZkcSecurity.Generation.UniformRoot

@[expose] public section

/-! Install the Sigma method in the shared root assembler. This extension
contains no per-root occurrence paths, ABI positions, hand-picked message
values or root-shape proof wrappers. It proposes ordinary proofs over the
actual generated views; unsupported behavior remains an unproved obligation. -/
set_option autoImplicit false
namespace ZkcSecurity.Generation.SigmaCompleteness
open Zkc.Source.Structured

structure Input where
  metadata : SubjectABI.Metadata
  output : UniformRoot.Output
  /-- Additional installation modules supplying the checked law below. -/
  imports : List String := []
  /-- A term checked as `Nonvacuous subject`, for the already fixed subject.
  Without one, generation proposes the usual all-default witness. -/
  nonvacuityLaw : Option String := none

def zeroInput : Ty → String
  | .boolean => "false"
  | .index | .field _ | .group _ => "0"
  | .vector _ => "[]"
  | .service _ => "none"

def source (input : Input) : Except String String := do
  let metadata := input.metadata
  let output := input.output
  let names := SubjectABI.names metadata.types
  let zeros := metadata.types.map zeroInput
  let presentation ← UniformRoot.presentation metadata output "SampledReadback (SampledReadback.Allowed subject)"
  RootCompleteness.source metadata output.toOutput {
    imports := ["ZkcSecurity.FiatShamir.SampledReadbackCompleteness"] ++ input.imports
    metaImports := ["ZkcSecurity.Tools.SigmaReadback"]
    opens := ["ZkcSecurity.Domains.PrimeField", "ZkcSecurity.Tools.SigmaReadback"]
    description := "Installed Sigma module algebra and actual authorized private sampling."
    relation := "SampledReadback (SampledReadback.Allowed subject)"
    adapter := "SampledReadback.perfect_abi"
    nonvacuityLaw := "nonvacuous"
    declarations := UniformRoot.declarations output ++
      (match input.nonvacuityLaw with
      | some law => "theorem nonvacuous : Nonvacuous subject :=\n  " ++ law ++ "\n\n"
      | none => "theorem nonvacuous : Nonvacuous subject := by\n" ++
      "  refine ⟨" ++ SubjectABI.call "inputs" zeros ++ ", ?_, ?_⟩\n" ++
      "  · apply (Subject.relation_iff_of_read subject _ _ " ++
        SubjectABI.call "application_read" zeros ++ ").mpr\n    rfl\n" ++
      "  · rw [honestInput_iff]\n    trivial\n\n")
    body := presentation ++
      "  prepare_sigma_relation for subject reading " ++ SubjectABI.call "application_read" names ++ "\n" ++
      "  rw [" ++ output.producerModule ++ ".participant_eq, " ++ output.validatorModule ++ ".participant_eq]\n" ++
      "  simp only [producerInputs, validatorInputs]\n" ++
      "  unfold_component_bodies [" ++ output.producerModule ++ ".view, " ++ output.validatorModule ++ ".view]\n" ++
      "  prove_sigma_readback\n" ++
      "    normalizing (normalize_sigma_process [context_eq])\n" ++
      "    authorizing rfl\n" ++
      "    finishing rfl\n" }

end ZkcSecurity.Generation.SigmaCompleteness
