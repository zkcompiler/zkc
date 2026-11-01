module

public import ZkcTools.StructuredSource.Bindings.SourceInstallation

@[expose] public section

/-! Source-specific naming, specialization and helper queries for the retained
GKR example. All traversal and equation printing belongs to reusable tooling.
This configuration is measured as authored client work. -/
namespace Tests.Generators.SourceConfigurations.Gkr
open Zkc.Source Zkc.Source.Structured Zkc.Source.Structured.NormalForm
open Zkc.Source.Structured.Bindings
open ZkcTools.StructuredSource.Bindings

def domain : String := "bls12-381.fr"
def field : Ty := .field domain
def vector : Ty := .vector domain

def configure (program : Program) : Except String SourceInstallation := do
  let roundsIndex ← uniqueProtocol program ⟨"gkr::Rounds", [("F", .field domain), ("Max", .natural "4")]⟩
  let callerIndex ← uniqueProtocol program ⟨"gkr::Gkr", [("F", .field domain),
    ("MaxLayers", .natural "4"), ("MaxWidth", .natural "4")]⟩
  let some rounds := program.payload.protocols[roundsIndex]? | throw "gkr-rounds-index"
  let some caller := program.payload.protocols[callerIndex]? | throw "gkr-caller-index"
  let (layer, site) ← callbackCalling program callerIndex 1 rounds.signature
  let output ← uniqueCallback program callerIndex fun callback =>
    callback.spec.state == [vector, vector] && callback.spec.captures == [.service ("random." ++ domain ++ "/0")]
  let signature := sourceSignature program
  let roundsForm ← normalize signature rounds.body 1 rounds.roles.length (optionalPattern rounds.inputs)
  let [roundsOpen] := prefixHelpers roundsForm | throw "gkr-rounds-open"
  let [roundsClose] ← afterRepeatHelpers roundsForm | throw "gkr-rounds-close"
  let layerPattern := optionalPattern (.index :: (layer.callback.spec.state ++ layer.callback.spec.captures))
  let layerForm ← normalize signature layer.callback.body 1 caller.roles.length layerPattern
  let [layerOpen, pending] := prefixHelpers layerForm | throw "gkr-layer-prefix"
  let producer ← normalize signature layer.callback.body 0 caller.roles.length layerPattern
  let block ← uniqueCandidate "gkr-block-reference"
    (helperOccurrences (prefixHelpers producer) .local [vector, .index, .index] [vector]).eraseDups
  let mut associations := []
  for (name, helper) in [("roundsOpen", roundsOpen), ("roundsClose", roundsClose),
      ("layerOpen", layerOpen), ("pending", pending)] do
    associations := associations ++ [(name, ← helperIndex program helper)]
  let (_, empty) ← uniqueHelper program .local [] [vector]
  let (_, append) ← uniqueHelperWhere program fun definition =>
    rounds.helpers.contains definition.helper && singlePrimitive definition (.vectorAppend domain)
  let (_, value) ← uniqueHelper program .math (List.replicate 4 field) [field]
  let (_, quadratic) ← uniqueHelper program .math (List.replicate 8 field) [field]
  let (message, roundMessage) ← uniqueHelper program .local (List.replicate 4 vector) (List.replicate 3 field)
  let [left, right] := helperOccurrences message.helpers .local (List.replicate 4 vector) [vector]
    | throw "gkr-value-occurrences"
  let leftIndex ← helperIndex program left
  let rightIndex ← helperIndex program right
  let some leftDefinition := program.payload.definitions[leftIndex]? | throw "gkr-left-index"
  let (valueCallback, valueCallbackIndex) ← uniqueHelper program .local
    (List.replicate 4 field ++ List.replicate 4 vector) [field] (some leftDefinition)
  let (_, valueRealization) ← uniqueHelper program .local (List.replicate 4 field) [field] (some valueCallback)
  let (quadratics, quadraticsIndex) ← uniqueHelper program .local (List.replicate 8 vector) [vector] (some message)
  let (quadraticCallback, quadraticCallbackIndex) ← uniqueHelper program .local
    (List.replicate 8 field ++ List.replicate 8 vector) [field] (some quadratics)
  let (_, quadraticRealization) ← uniqueHelper program .local (List.replicate 8 field) [field] (some quadraticCallback)
  let (wrapper, linearWrapper) ← uniqueHelper program .local (List.replicate 3 field) [field] (some message)
  let (_, linearCoefficient) ← uniqueHelper program .math (List.replicate 3 field) [field] (some wrapper)
  let (restriction, gateRestriction) ← uniqueHelper program .local (List.replicate 4 vector ++ [field])
    (List.replicate 4 vector)
  let (factor, factorRestriction) ← uniqueHelper program .local [vector, field] [vector] (some restriction)
  let (maps, interpolations) ← uniqueHelper program .local [vector, vector, field] [vector] (some factor)
  let (interpolationCallback, interpolationCallbackIndex) ← uniqueHelper program .local
    [field, field, vector, vector, field] [field] (some maps)
  let (_, interpolationRealization) ← uniqueHelper program .local (List.replicate 3 field) [field] (some interpolationCallback)
  let (_, interpolation) ← uniqueHelper program .math (List.replicate 3 field) [field] (some maps)
  associations := associations ++ [("empty", empty), ("append", append), ("gateValue", value),
    ("gateValuesLeft", leftIndex), ("gateValuesRight", rightIndex),
    ("gateValueCallback", valueCallbackIndex), ("gateValueRealization", valueRealization),
    ("gateQuadratic", quadratic), ("gateQuadratics", quadraticsIndex),
    ("gateQuadraticCallback", quadraticCallbackIndex), ("gateQuadraticRealization", quadraticRealization),
    ("linearCoefficient", linearCoefficient), ("linearWrapper", linearWrapper), ("roundMessage", roundMessage),
    ("interpolation", interpolation), ("interpolations", interpolations),
    ("interpolationCallback", interpolationCallbackIndex), ("interpolationRealization", interpolationRealization),
    ("factorRestriction", factorRestriction), ("gateRestriction", gateRestriction)]
  let bodyHelpers ← [("valuesBelow", [vector, vector, vector, .index, .index, .index, .index], [vector]),
    ("layerGates", [vector, vector, vector, vector, .index], List.replicate 4 vector),
    ("evaluate", [vector, vector], [field])].mapM fun (name, inputs, outputs) => do
      let (_, index) ← uniqueHelper program .local inputs outputs
      return (name, index)
  let blockIndex ← helperIndex program block
  return {
    protocols := [roundsIndex, callerIndex]
    templates := { moduleName := "Zkc.Protocols.Gkr.Source.RoundHelpers"
                   namespaceName := "ZkcExamples.Structured.Generated.Bindings.GkrRoundsGate" }
    namespaceSuffix := "Gate"
    associations := associations
    callerSource := fun outputSettings => do
      let mut text := callerSourceHeader outputSettings
      for (name, index) in bodyHelpers do
        text := text ++ (← helperBodySource program name index)
      text := text ++ callbackAliasSource output 1 "output"
      text := text ++ (← helperAliasSource program "selectBlock" blockIndex)
      text := text ++ (← callbackCallSource program layer site [0, 1] 1 "firstLeft" "layer")
      return text ++ "end\nend " ++ outputSettings.moduleName ++ "Caller\n" }

end Tests.Generators.SourceConfigurations.Gkr
