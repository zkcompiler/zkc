module

public import ZkcExamples.Structured.GkrGateGoals
public import ZkcExamples.Structured.GkrSourceLaws
public import Zkc.Source.Structured.HelperCallbacks
meta import ZkcTools.StructuredSource.HelperCallbacks
meta import ZkcTools.StructuredSource.HelperPresentation
meta import ZkcTools.StructuredSource.NamedValues
meta import ZkcTools.StructuredSource.ProcessReference

@[expose] public section

/-! Complete circuit helper statements and named rows, selected from the actual
source before choosing a mathematical reference. Callback captures are outputs
as well as inputs; their types and the state boundary come from the loop. -/
namespace ZkcSecurity.Realizations.Gkr.HonestCircuit.Goals
open Zkc.Source Zkc.Source.Structured ZkcExamples.Structured

set_option maxRecDepth 20000

helper_callback layerCallback from GkrSourceBodies.helper33Body
helper_presentation Step inputs [position, values, addWeights, mulWeights, width, left, right]
  outputs [values, addWeights, mulWeights, width, left, right] := layerCallback
helper_presentation Layer inputs [addWeights, mulWeights, below, width]
  outputs [values] := GkrSourceBodies.helper33Body
helper_presentation Traversal inputs [addWeights, mulWeights, inputValues, layers, selector, width, layerIndex]
  outputs [values] := GkrSourceBodies.helper34Body

named_values LayerState [values] := layerCallback_selection.callback.state
named_values LayerCaptures [addWeights, mulWeights, width, left, right] :=
  layerCallback_selection.callback.captures

named_values BlockArguments [source, position, width] := GkrSourceBodies.selectBlockHelper.inputs
named_values BlockResult [values] := GkrSourceBodies.selectBlockHelper.outputs
named_values PowerResult [count] := GkrSourceBodies.helper18Helper.outputs
named_values RepeatResult [values] := GkrSourceBodies.helper25Helper.outputs
named_values PowerArguments [width] := GkrSourceBodies.helper18Helper.inputs
named_values RepeatArguments [source, count] := GkrSourceBodies.helper25Helper.inputs

source_reference stepProcess from_equation Step.equation using [Step.run]
source_reference layerProcess from_equation Layer.equation using [Layer.run]
source_reference valuesProcess from_equation Traversal.equation using [Traversal.run]

structure Bodies (definitions : List CheckedDefinition) : Prop where
  layer : BodyIn definitions GkrSourceBodies.helper33Helper Layer.body
  values : BodyIn definitions GkrSourceBodies.helper34Helper Traversal.body

end ZkcSecurity.Realizations.Gkr.HonestCircuit.Goals
