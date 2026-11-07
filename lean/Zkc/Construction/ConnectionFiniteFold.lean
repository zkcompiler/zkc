module

public import Zkc.Construction.ConnectionMathSimulation

@[expose] public section

/-! Embedded finite folds use the original program's admitted domain and
lexically closed callbacks. This rule adds only physical tuple encoding and
caller-frame preservation; domain refusals and callback stops remain unchanged. -/
set_option autoImplicit false
namespace Zkc.Construction.ConnectionFiniteFold
open Zkc.Source Zkc.Source.Structured

/-- Resolution fixes the actual domain tree, callback identities and full ABI.
It does not assert that domain admission or any callback returns successfully. -/
theorem encoded (model : DomainModel) (program : Program)
    (domain step predicate : String) (spec : FoldSpec)
    (resolved : Domain.resolveFiniteFold program domain step predicate
      (spec.arguments.map ValueSort.data) (spec.state.map ValueSort.data) = .ok spec)
    (arguments : Values model.Value spec.arguments)
    (inputData : spec.arguments.all Domain.localType = true)
    (outputData : spec.state.all Domain.localType = true) :
    Domain.finiteFold model program domain step predicate (spec.state.map ValueSort.data)
        (Original.encodeHelperResult arguments) =
      (match Domain.closedOutcome
        (Evaluation.denoteFoldOn (Domain.helperTable model program) spec arguments) with
      | .returned results => .returned (Original.encodeHelperResult results)
      | .stopped reason => .stopped reason) := by
  have encoding := Original.encodeHelperResult_eq inputData arguments
  have sorts := Domain.encodeValues_sorts encoding
  have decoded := Domain.decodeValues_encodeValues encoding
  simp only [Domain.finiteFold, sorts, resolved, decoded]
  cases Domain.closedOutcome
      (Evaluation.denoteFoldOn (Domain.helperTable model program) spec arguments) with
  | stopped reason => rfl
  | returned results => simp only [Original.encodeHelperResult_eq outputData results]

/-- Ordered operands and exact nominal sorts connect the physical instruction
to its existing source meaning on every outcome, without an honest-run premise. -/
theorem view (model : DomainModel) (program : Program)
    (domain step predicate : String) (spec : FoldSpec)
    (resolved : Domain.resolveFiniteFold program domain step predicate
      (spec.arguments.map ValueSort.data) (spec.state.map ValueSort.data) = .ok spec)
    (arguments : Values model.Value spec.arguments)
    (inputData : spec.arguments.all Domain.localType = true)
    (outputData : spec.state.all Domain.localType = true)
    (environment : Domain.Environment model.toCarriers) (references : List Nat)
    (read : Domain.read environment references = Domain.encodeValues arguments) :
    Domain.View.finiteFold model program domain step predicate references
        (spec.state.map ValueSort.data) environment =
      ((Evaluation.denoteFoldOn (Domain.helperTable model program) spec arguments).interpret
        (closedLift (I := Domain.effects model.toCarriers))).bind
        (fun results => .done (environment ++ Original.encodeHelperResult results)) := by
  simp only [Domain.View.finiteFold, read, Original.encodeHelperResult_eq inputData arguments,
    encoded model program domain step predicate spec resolved arguments inputData outputData]
  cases computed : Evaluation.denoteFoldOn (Domain.helperTable model program) spec arguments with
  | done results =>
    simp only [Domain.closedOutcome, Domain.View.append,
      Original.encodeHelperResult_sorts outputData results, ↓reduceIte,
      PIR.Process.interpret, PIR.Process.bind]
  | halt reason => rfl
  | call operation _ => exact nomatch operation

/-- The ordinary simulation relation retains every output and the caller's
frame. A separately proved callback or mathematical law can now be reused. -/
noncomputable def simulation (model : DomainModel) (program : Program)
    (domain step predicate : String) (spec : FoldSpec)
    (resolved : Domain.resolveFiniteFold program domain step predicate
      (spec.arguments.map ValueSort.data) (spec.state.map ValueSort.data) = .ok spec)
    (arguments : Values model.Value spec.arguments)
    (inputData : spec.arguments.all Domain.localType = true)
    (outputData : spec.state.all Domain.localType = true)
    (environment : Domain.Environment model.toCarriers) (references : List Nat)
    (read : Domain.read environment references = Domain.encodeValues arguments) :
    Original.Simulation (fun values final => final = environment ++ Original.encodeHelperResult values)
      (fun _ frame => ArtifactBinding.Captures environment frame)
      ((Evaluation.denoteFoldOn (Domain.helperTable model program) spec arguments).interpret
        (closedLift (I := Domain.effects model.toCarriers)))
      (Domain.View.finiteFold model program domain step predicate references
        (spec.state.map ValueSort.data) environment) := by
  rw [view model program domain step predicate spec resolved arguments inputData outputData environment references read]
  cases computed : Evaluation.denoteFoldOn (Domain.helperTable model program) spec arguments with
  | done values => exact .done rfl
  | halt reason => exact .halt reason
  | call operation _ => exact nomatch operation

end Zkc.Construction.ConnectionFiniteFold
