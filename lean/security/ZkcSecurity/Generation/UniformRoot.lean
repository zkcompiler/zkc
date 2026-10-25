module

public import ZkcSecurity.Generation.RootCompleteness

@[expose] public section

/-! Opt-in presentation for installed uniform ring/module realizations.
This is a method library, not a restriction imposed by common root assembly.
Nominal source tags stay in the checked ABI and the actual Process views. -/
set_option autoImplicit false
namespace ZkcSecurity.Generation.UniformRoot
open Zkc.Source.Structured

structure Output extends RootCompleteness.Output where
  fieldType : String
  groupType : String
  sampling : String

def carrier : Ty → String
  | .boolean => "Bool"
  | .index => "Nat"
  | .field _ => "Scalar"
  | .vector _ => "List Scalar"
  | .group _ => "Group"
  | .service _ => "Option Nat"

def declarations (output : Output) : String :=
  "abbrev Scalar := " ++ output.fieldType ++ "\nabbrev Group := " ++ output.groupType ++ "\n" ++
  "local instance : ∀ event : Domain.Event subject.domainModel.toCarriers,\n" ++
  "    SampleableType (Domain.Raw event) := " ++ output.sampling ++ "\n\n"

def presentation (metadata : SubjectABI.Metadata) (output : Output) (relation : String) :
    Except String String := do
  let some positions := metadata.producerPositions | throw "uniform-root-source-interface"
  let producerNames := ((List.range metadata.types.length).filter fun index =>
    positions.contains index || metadata.publicPositions.contains index).map SubjectABI.inputName
  let validatorNames := metadata.publicPositions.map SubjectABI.inputName
  let mut text := ""
  for (ty, name) in metadata.types.zip (SubjectABI.names metadata.types) do
    text := text ++ "  change " ++ carrier ty ++ " at " ++ name ++ "\n"
  pure (text ++ "  change " ++ relation ++ " _\n" ++
    "    (Domain.participant (ringModel Scalar Group) _ _ " ++ output.producerModule ++ ".artifact " ++
      SubjectABI.call "producerInputs" producerNames ++ ")\n" ++
    "    (Domain.participant (ringModel Scalar Group) _ _ " ++ output.validatorModule ++ ".artifact " ++
      SubjectABI.call "validatorInputs" validatorNames ++ ")\n")

end ZkcSecurity.Generation.UniformRoot
