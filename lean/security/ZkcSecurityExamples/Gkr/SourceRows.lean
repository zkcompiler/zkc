module

public import ZkcExamples.Structured.Generated.Presentations.Gkr
public import ZkcSecurityExamples.Gkr.SourceCalls
public import ZkcSecurity.Bindings.Gkr.Encoding
public import ZkcSecurityExamples.Gkr.HonestProducerRoundAlgorithm
public import Zkc.Source.Structured.InputVisibility
public meta import ZkcTools.StructuredSource.NamedValues

@[expose] public section

/-! Complete named rows from the actual source signatures and callback scopes.
Field labels describe mathematical data; generated schema equations and inverse
laws check every retained coordinate and its order, including private slots. -/
set_option autoImplicit false
namespace ZkcSecurity.Realizations.Gkr.SourceRows
open Zkc.Source Zkc.Source.Structured
open ZkcExamples.Structured Generated.Presentations.Gkr

named_values Inputs [inputs, outputs, add, mul, layers, selector, width, service] := GkrSourceBodies.gkrSignature.inputs
named_values Decision [accepted] := GkrSourceBodies.gkrSignature.outputs
named_values RoundsInputs [add, mul, left, right, pending, claim, count, service] := GkrSourceBodies.roundsSignature.inputs
named_values RoundsResults [point, add, mul, left, right, pending, claim] := GkrSourceBodies.roundsSignature.outputs
named_values InputInputs [inputs, point, claim] := GkrSourceBodies.sourceProtocol80Signature.inputs
named_values InputResults [accepted] := GkrSourceBodies.sourceProtocol80Signature.outputs
named_values RoundState [add, mul, left, right, point, pending, claim] := Rounds.roundSpec.state
named_values RoundCaptures [service] := Rounds.roundSpec.captures
named_values RoundArguments [index, add, mul, left, right, point, pending, claim, service] := .index :: (Rounds.roundSpec.state ++ Rounds.roundSpec.captures)
named_values OutputState [verifierPoint, proverPoint] := Root.outputSpec.state
named_values OutputCaptures [service] := Root.outputSpec.captures
named_values OutputArguments [index, verifierPoint, proverPoint, service] := .index :: (Root.outputSpec.state ++ Root.outputSpec.captures)
named_values LayerState [proverPoint, point, claim] := Root.layerSpec.state
named_values LayerCaptures [inputs, add, mul, layers, selector, width, service] := Root.layerSpec.captures
named_values LayerArguments [index, proverPoint, point, claim, inputs, add, mul, layers, selector, width, service] := .index :: (Root.layerSpec.state ++ Root.layerSpec.captures)
named_values CoefficientState [coefficients] := Root.coefficientSpec.state
named_values CoefficientCaptures [line] := Root.coefficientSpec.captures
named_values CoefficientArguments [index, coefficients, line] := .index :: (Root.coefficientSpec.state ++ Root.coefficientSpec.captures)
named_values ProducerLayerScope [index, point, inputs, add, mul, layers, selector, width, service] := Root.proverLayerPattern.scope
named_values VerifierLayerScope [index, point, claim, inputs, add, mul, layers, selector, width, service] := Root.verifierLayerPattern.scope
named_values SelectBlockInputs [table, position, bits] := GkrSourceBodies.selectBlockHelper.inputs
named_values SelectBlockResults [block] := GkrSourceBodies.selectBlockHelper.outputs
named_values LinePointInputs [start, finish, challenge] := GkrSourceBodies.linePointHelper.inputs
named_values LinePointResults [point] := GkrSourceBodies.linePointHelper.outputs
named_values ValuesBelowInputs [add, mul, inputs, layers, selector, width, index] := GkrSourceBodies.helper34Helper.inputs
named_values ValuesBelowResults [wires] := GkrSourceBodies.helper34Helper.outputs
named_values LayoutInputs [add, mul, point, wires, width] := GkrSourceBodies.helper36Helper.inputs
named_values LayoutResults [add, mul, left, right] := GkrSourceBodies.helper36Helper.outputs
named_values LineCoefficientsInputs [wires, left, right, width] := GkrSourceBodies.helper69Helper.inputs
named_values LineCoefficientsResults [coefficients] := GkrSourceBodies.helper69Helper.outputs
named_values ElementInputs [coefficients, index] := GkrSourceBodies.helper57Helper.inputs
named_values ElementResults [coefficient] := GkrSourceBodies.helper57Helper.outputs
named_values PointClaimInputs [point, claim] := GkrSourceBodies.sourceHelper20Helper.inputs
named_values PointClaimResults [point, claim] := GkrSourceBodies.sourceHelper20Helper.outputs
named_values NextPointClaimInputs [point, claim] := GkrSourceBodies.sourceHelper19Helper.inputs
named_values NextPointClaimResults [point, claim] := GkrSourceBodies.sourceHelper19Helper.outputs
named_values PendingInputs [claim] := GkrSourceBodies.sourceHelper37Helper.inputs
named_values PendingResults [point, claim] := GkrSourceBodies.sourceHelper37Helper.outputs
named_values RepackPendingInputs [point, claim] := GkrSourceBodies.sourceHelper40Helper.inputs
named_values RepackPendingResults [point, claim] := GkrSourceBodies.sourceHelper40Helper.outputs
named_values SplitPendingInputs [point] := GkrSourceBodies.sourceHelper50Helper.inputs
named_values SplitPendingResults [left, right] := GkrSourceBodies.sourceHelper50Helper.outputs
named_values EmptyInputs [] := GkrSourceBodies.emptyHelper.inputs
named_values EmptyResults [vector] := GkrSourceBodies.emptyHelper.outputs
named_values AppendInputs [vector, element] := GkrSourceBodies.appendHelper.inputs
named_values AppendResults [vector] := GkrSourceBodies.appendHelper.outputs
named_values SumInputs [coefficients] := GkrSourceBodies.sumHelper.inputs
named_values SumResults [sum] := GkrSourceBodies.sumHelper.outputs
named_values EvaluateWiringInputs [table, point, left, right] := GkrSourceBodies.evaluateWiringHelper.inputs
named_values EvaluateWiringResults [evaluation] := GkrSourceBodies.evaluateWiringHelper.outputs
named_values EvaluateCoefficientsInputs [coefficients, challenge] := GkrSourceBodies.evaluateCoefficientsHelper.inputs
named_values EvaluateCoefficientsResults [evaluation] := GkrSourceBodies.evaluateCoefficientsHelper.outputs

/-- Named visibility is derived from the complete supplied row and actual
signature scopes, including optional capabilities and absent components. -/
def RoundsInputs.mask {Value : Ty → Type} (role : Nat)
    (view : RoundsInputs.View (Component Value)) :
    RoundsInputs.View (Component Value) :=
  RoundsInputs.project (maskValues role GkrSourceBodies.roundsSignature.inputScopes) view

theorem RoundsInputs.pack_mask {Value : Ty → Type} (role : Nat)
    (view : RoundsInputs.View (Component Value)) :
    RoundsInputs.pack (RoundsInputs.mask role view) =
      maskValues role GkrSourceBodies.roundsSignature.inputScopes (RoundsInputs.pack view) :=
  RoundsInputs.pack_project _ view

/-- Roster transport and named-row projection cover the entire input mask. -/
theorem RoundsInputs.mask_context (model : DomainModel) (ctx : ProtocolContext) (role : Nat)
    (distinct : NormalForm.RosterDistinct ctx role 2)
    (view : RoundsInputs.View (Component model.Value)) :
    maskValues (ctx.roles role) (ctx.mapScopes GkrSourceBodies.roundsSignature.inputScopes)
      (RoundsInputs.pack view) = RoundsInputs.pack (RoundsInputs.mask role view) :=
  (InputVisibility.mask_context (model := model) distinct _ (by decide) _).trans
    (RoundsInputs.pack_mask role view).symm

/-- Output visibility uses the same complete named-row correspondence. -/
def RoundsResults.mask {Value : Ty → Type} (role : Nat)
    (view : RoundsResults.View (Component Value)) :
    RoundsResults.View (Component Value) :=
  RoundsResults.project (maskValues role GkrSourceBodies.roundsSignature.outputScopes) view

theorem RoundsResults.pack_mask {Value : Ty → Type} (role : Nat)
    (view : RoundsResults.View (Component Value)) :
    RoundsResults.pack (RoundsResults.mask role view) =
      maskValues role GkrSourceBodies.roundsSignature.outputScopes (RoundsResults.pack view) :=
  RoundsResults.pack_project _ view

/-- Output transport retains the same roster premise as input transport. -/
theorem RoundsResults.mask_context (model : DomainModel) (ctx : ProtocolContext) (role : Nat)
    (distinct : NormalForm.RosterDistinct ctx role 2)
    (view : RoundsResults.View (Component model.Value)) :
    maskValues (ctx.roles role) (ctx.mapScopes GkrSourceBodies.roundsSignature.outputScopes)
      (RoundsResults.pack view) = RoundsResults.pack (RoundsResults.mask role view) :=
  (InputVisibility.mask_context (model := model) distinct _ (by decide) _).trans
    (RoundsResults.pack_mask role view).symm

/-- Place an independently chosen circuit encoding and output claim in the
complete source row. The verifier capability remains optional; this supplies
no admission, relation or execution proof. -/
abbrev circuitInputs {F G : Type} (encoding : CircuitEncoding F)
    (outputs : List F) (service : Option Nat) :
    Values (Component (assignment F G)) GkrSourceBodies.gkrSignature.inputs :=
  Inputs.pack
    { inputs := some encoding.inputs, outputs := some outputs,
      add := some encoding.add, mul := some encoding.mul,
      layers := some encoding.layers, selector := some encoding.selector,
      width := some encoding.width, service }

/-- The terminal context is projected from the installed typed source call.
The descriptor carries its actual occurrence, signature and role substitution. -/
noncomputable abbrev inputContext (context : ProtocolContext) : ProtocolContext :=
  context.enter SourceCalls.inputCall.site SourceCalls.inputCall.roles

/-- Encode every mathematical round result in the complete source return row.
The validator-only pending claim remains absent from the producer return. -/
def roundsResult {F G : Type} (result : HonestProducerRounds.Result F) :
    Values (Component (assignment F G)) ZkcExamples.Structured.GkrSourceBodies.roundsSignature.outputs :=
  SourceRows.RoundsResults.pack
    { point := result.2.2.2.2, add := result.1, mul := result.2.1,
      left := result.2.2.1, right := result.2.2.2.1, pending := none, claim := none }

end ZkcSecurity.Realizations.Gkr.SourceRows
