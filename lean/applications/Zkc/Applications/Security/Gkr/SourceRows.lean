module

public import Zkc.Applications.IR.Structured.Generated.Presentations.Gkr
public import Zkc.Applications.Security.Gkr.SourceCalls
public import Zkc.Verification.Bindings.Gkr.Encoding
public import Zkc.Applications.Security.Gkr.HonestProducerRoundAlgorithm
public import Zkc.IR.Source.Structured.InputVisibility
public meta import Zkc.Tools.IR.StructuredSource.NamedValues

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
named_values RoundsInputs [add, mul, left, right, custody, pending, claim, count, service] := GkrSourceBodies.roundsSignature.inputs
named_values RoundsResults [point, add, mul, left, right, custody, pending, claim] := GkrSourceBodies.roundsSignature.outputs
named_values InputInputs [inputs, custody, point, claim] := GkrSourceBodies.inputSignature.inputs
named_values InputResults [accepted] := GkrSourceBodies.inputSignature.outputs
named_values RoundState [add, mul, left, right, point, pending, claim] := Rounds.roundSpec.state
named_values RoundCaptures [service] := Rounds.roundSpec.captures
named_values RoundArguments [index, add, mul, left, right, point, pending, claim, service] := .index :: (Rounds.roundSpec.state ++ Rounds.roundSpec.captures)
named_values OutputState [verifierPoint, proverPoint] := Root.outputSpec.state
named_values OutputCaptures [service] := Root.outputSpec.captures
named_values OutputArguments [index, verifierPoint, proverPoint, service] := .index :: (Root.outputSpec.state ++ Root.outputSpec.captures)
named_values LayerState [proverPoint, custody, point, claim] := Root.layerSpec.state
named_values LayerCaptures [inputs, add, mul, layers, selector, width, service] := Root.layerSpec.captures
named_values LayerArguments [index, proverPoint, custody, point, claim, inputs, add, mul, layers, selector, width, service] := .index :: (Root.layerSpec.state ++ Root.layerSpec.captures)
named_values CoefficientState [coefficients] := Root.coefficientSpec.state
named_values CoefficientCaptures [line] := Root.coefficientSpec.captures
named_values CoefficientArguments [index, coefficients, line] := .index :: (Root.coefficientSpec.state ++ Root.coefficientSpec.captures)
named_values ProducerLayerScope [index, point, inputs, add, mul, layers, selector, width, service] := Root.proverLayerPattern.scope
named_values VerifierLayerScope [index, custody, point, claim, inputs, add, mul, layers, selector, width, service] := Root.verifierLayerPattern.scope
named_values SelectBlockInputs [table, position, bits] := GkrSourceBodies.selectBlockHelper.inputs
named_values SelectBlockResults [block] := GkrSourceBodies.selectBlockHelper.outputs
named_values LinePointInputs [start, finish, challenge] := GkrSourceBodies.linePointHelper.inputs
named_values LinePointResults [point] := GkrSourceBodies.linePointHelper.outputs
named_values ValuesBelowInputs [add, mul, inputs, layers, selector, width, index] := GkrSourceBodies.helper65Helper.inputs
named_values ValuesBelowResults [wires] := GkrSourceBodies.helper65Helper.outputs
named_values LayoutInputs [add, mul, point, wires, width] := GkrSourceBodies.helper66Helper.inputs
named_values LayoutResults [add, mul, left, right] := GkrSourceBodies.helper66Helper.outputs
named_values LineCoefficientsInputs [wires, left, right, width] := GkrSourceBodies.helper102Helper.inputs
named_values LineCoefficientsResults [coefficients] := GkrSourceBodies.helper102Helper.outputs
named_values ElementInputs [coefficients, index] := GkrSourceBodies.helper97Helper.inputs
named_values ElementResults [coefficient] := GkrSourceBodies.helper97Helper.outputs
named_values PointClaimInputs [custody, point, claim] := GkrSourceBodies.helper12Helper.inputs
named_values PointClaimResults [custody, retainedPoint, retainedClaim, point, claim] := GkrSourceBodies.helper12Helper.outputs
named_values NextPointClaimInputs [point, claim] := GkrSourceBodies.helper11Helper.inputs
named_values NextPointClaimResults [custody, point, claim] := GkrSourceBodies.helper11Helper.outputs
named_values RefreshInputs [custody, retainedPoint, retainedClaim, point, claim] := GkrSourceBodies.helper37Helper.inputs
named_values RefreshResults [custody, point, claim] := GkrSourceBodies.helper37Helper.outputs
named_values PendingInputs [claim] := GkrSourceBodies.helper20Helper.inputs
named_values PendingResults [custody, point, claim] := GkrSourceBodies.helper20Helper.outputs
named_values RepackPendingInputs [custody, point, claim] := GkrSourceBodies.helper22Helper.inputs
named_values RepackPendingResults [point, claim] := GkrSourceBodies.helper22Helper.outputs
named_values SplitPendingInputs [point] := GkrSourceBodies.helper27Helper.inputs
named_values SplitPendingResults [left, right] := GkrSourceBodies.helper27Helper.outputs
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
      left := result.2.2.1, right := result.2.2.2.1, custody := none, pending := none, claim := none }

end ZkcSecurity.Realizations.Gkr.SourceRows
