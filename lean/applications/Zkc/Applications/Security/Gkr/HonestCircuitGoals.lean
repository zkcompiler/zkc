module

public import Zkc.Applications.IR.Structured.GkrGateGoals
public import Zkc.Applications.IR.Structured.GkrSourceLaws
public import Zkc.IR.Source.Structured.HelperCallbacks
meta import Zkc.Tools.IR.StructuredSource.HelperCallbacks
meta import Zkc.Tools.IR.StructuredSource.HelperPresentation
meta import Zkc.Tools.IR.StructuredSource.NamedValues
meta import Zkc.Tools.IR.StructuredSource.ProcessReference

@[expose] public section

/-! Complete circuit helper statements and named rows, selected from the actual
source before choosing a mathematical reference. Callback captures are outputs
as well as inputs; their types and the state boundary come from the loop. -/
namespace ZkcSecurity.Realizations.Gkr.HonestCircuit.Goals
open Zkc.Source Zkc.Source.Structured ZkcExamples.Structured

set_option maxRecDepth 20000

helper_callback layerCallback from GkrSourceBodies.helper64Body
helper_presentation Step inputs [position, values, addWeights, mulWeights, width, left, right]
  outputs [values, addWeights, mulWeights, width, left, right] := layerCallback
helper_presentation Layer inputs [addWeights, mulWeights, below, width]
  outputs [values] := GkrSourceBodies.helper64Body
helper_presentation Traversal inputs [addWeights, mulWeights, inputValues, layers, selector, width, layerIndex]
  outputs [values] := GkrSourceBodies.helper65Body

named_values LayerState [values] := layerCallback_selection.callback.state
named_values LayerCaptures [addWeights, mulWeights, width, left, right] :=
  layerCallback_selection.callback.captures

named_values BlockArguments [source, position, width] := GkrSourceBodies.selectBlockHelper.inputs
named_values BlockResult [values] := GkrSourceBodies.selectBlockHelper.outputs
named_values PowerResult [count] := GkrSourceBodies.helper4Helper.outputs
named_values RepeatResult [values] := GkrSourceBodies.helper60Helper.outputs
named_values PowerArguments [width] := GkrSourceBodies.helper4Helper.inputs
named_values RepeatArguments [source, count] := GkrSourceBodies.helper60Helper.inputs

source_reference stepProcess from_equation Step.equation using [Step.run]
source_reference layerProcess from_equation Layer.equation using [Layer.run]
source_reference valuesProcess from_equation Traversal.equation using [Traversal.run]

structure Bodies (definitions : List CheckedDefinition) : Prop where
  layer : BodyIn definitions GkrSourceBodies.helper64Helper Layer.body
  values : BodyIn definitions GkrSourceBodies.helper65Helper Traversal.body

end ZkcSecurity.Realizations.Gkr.HonestCircuit.Goals
