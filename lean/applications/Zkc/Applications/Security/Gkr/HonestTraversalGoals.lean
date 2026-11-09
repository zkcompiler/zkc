module

public import Zkc.Applications.Security.Gkr.HonestCircuitGoals
meta import Zkc.Tools.IR.StructuredSource.HelperCallbacks
meta import Zkc.Tools.IR.StructuredSource.HelperPresentation
meta import Zkc.Tools.IR.StructuredSource.NamedValues
meta import Zkc.Tools.IR.StructuredSource.ProcessReference

@[expose] public section

/-! The complete backward traversal callback and its named rows come from the
actual helper34 loop. The outer traversal presentation remains in circuit goals. -/
namespace ZkcSecurity.Realizations.Gkr.HonestCircuit.Goals
open Zkc.Source Zkc.Source.Structured ZkcExamples.Structured

set_option maxRecDepth 20000

helper_callback traversalCallback from GkrSourceBodies.helper65Body
helper_presentation TraversalStep
  inputs [iteration, values, current, addWeights, mulWeights, selector, width]
  outputs [values, current, addWeights, mulWeights, selector, width] := traversalCallback

named_values TraversalStepArguments [iteration, values, current, addWeights, mulWeights, selector, width] :=
  traversalCallback_selection.callback.inputs
named_values TraversalState [values, current] := traversalCallback_selection.callback.state
named_values TraversalCaptures [addWeights, mulWeights, selector, width] :=
  traversalCallback_selection.callback.captures

source_reference traversalStepProcess from_equation TraversalStep.equation using [TraversalStep.run]

end ZkcSecurity.Realizations.Gkr.HonestCircuit.Goals
