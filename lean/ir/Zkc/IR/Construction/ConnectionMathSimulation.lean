module

public import Zkc.IR.Construction.OriginalFrameRelations
public import Zkc.IR.Construction.ConnectionCalculations

@[expose] public section

/-! Closed-region checkpoint transport for the existing simulation relation.
Prefixing diagnostic frames never changes operand numbering, results, stops,
or the non-checkpoint operation interface. -/
set_option autoImplicit false
namespace Zkc.Construction.Original
open Zkc.Source
variable {carriers : Structured.Carriers} {A B : Type}

theorem captures_prefix (caller : Domain.Environment carriers)
    {captured frame : Domain.Environment carriers}
    (retained : ArtifactBinding.Captures captured frame) :
    ArtifactBinding.Captures (caller ++ captured) (caller ++ frame) := by
  unfold ArtifactBinding.Captures at *
  rw [List.length_append, List.take_append,
    List.take_of_length_le (Nat.le_add_right _ _), Nat.add_sub_cancel_left, retained]

/-- Lexical frame entry preserves an entire simulation, not only successful
returns. Every nested checkpoint retains the caller and the original capture. -/
noncomputable def Simulation.prefixFrames
    {returns : A → B → Prop} {captured : Domain.Environment carriers}
    {source : PIR.Process (Domain.effects carriers) A}
    {target : PIR.Process (Domain.effects carriers) B}
    (certificate : Simulation returns (fun _ frame => ArtifactBinding.Captures captured frame)
      source target) (caller : Domain.Environment carriers) :
    Simulation returns (fun _ frame => ArtifactBinding.Captures (caller ++ captured) frame)
      (source.interpret (Domain.withCallerFrame caller))
      (target.interpret (Domain.withCallerFrame caller)) := by
  induction certificate with
  | done related => exact .done related
  | halt reason => exact .halt reason
  | call operation next ih =>
      cases operation <;> exact .call _ ih
  | checkpoint frame retained next ih =>
      exact .checkpoint (caller ++ frame) (captures_prefix caller retained) ih

/-- A closed mathematical source has no checkpoint or external operation to
rename. Only its independently connected target gains the caller's frame. -/
theorem closed_frame_identity (caller : Domain.Environment carriers)
    (source : PIR.Process Structured.closedInterface A) :
    (source.interpret (Structured.closedLift (I := Domain.effects carriers))).interpret
        (Domain.withCallerFrame caller) =
      source.interpret (Structured.closedLift (I := Domain.effects carriers)) := by
  cases source with
  | done => rfl
  | halt => rfl
  | call operation _ => exact nomatch operation

/-- A nominal calculation has its existing complete source meaning, including
refusal. There is no totality or successful-execution premise. -/
noncomputable def Simulation.mathCalculation (model : Structured.DomainModel)
    (operation : Calculation) (arguments : Values model.Value operation.op.arguments)
    (inputData : operation.op.arguments.all Domain.localType = true)
    (outputData : operation.op.results.all Domain.localType = true)
    (environment : Domain.Environment model.toCarriers) (references : List Nat)
    (read : Domain.read environment references = Domain.encodeValues arguments) :
    Simulation (fun values final => final = environment ++ encodeHelperResult values)
      (fun _ frame => ArtifactBinding.Captures environment frame)
      ((ConnectionCalculations.closedCalculation model operation arguments).interpret
        (Structured.closedLift (I := Domain.effects model.toCarriers)))
      (Domain.View.calculation model operation references (operation.op.results.map ValueSort.data) environment) := by
  rw [ConnectionCalculations.view_calculation model operation arguments inputData outputData
    environment references read]
  cases computed : ConnectionCalculations.closedCalculation model operation arguments with
  | done values => exact .done rfl
  | halt reason => exact .halt reason
  | call operation _ => exact nomatch operation

/-- The construction fold carries closed results with the unchanged source
state. Its routing cannot add observations to a closed computation. -/
theorem foldClosed (routing : Routing) (state : State carriers)
    (source : PIR.Process Structured.closedInterface A) :
    fold routing (source.interpret (Structured.closedLift (I := Structured.Occurrence.signature carriers))) state =
      (source.interpret (Structured.closedLift (I := Domain.effects carriers))).bind
        (fun value => .done (value, state)) := by
  cases source with
  | done => rfl
  | halt => rfl
  | call operation _ => exact nomatch operation

/-- Add the untouched source state to a closed connection. Checkpoint capture
obligations and every stopping reason survive unchanged. -/
noncomputable def Simulation.closedState {returns : A → B → Prop}
    {captured : Domain.Environment carriers} (routing : Routing) (state : State carriers)
    (source : PIR.Process Structured.closedInterface A)
    {target : PIR.Process (Domain.effects carriers) B}
    (certificate : Simulation returns (fun _ frame => ArtifactBinding.Captures captured frame)
      (source.interpret (Structured.closedLift (I := Domain.effects carriers))) target) :
    Simulation (fun result frame => returns result.1 frame ∧ result.2 = state)
      (fun _ frame => ArtifactBinding.Captures captured frame)
      (fold routing (source.interpret (Structured.closedLift (I := Structured.Occurrence.signature carriers))) state)
      target := by
  rw [foldClosed]
  have connected := certificate.bind
    (sourceNext := fun value => .done (value, state)) (targetNext := fun frame => .done frame)
    (returnRelation := fun result frame => returns result.1 frame ∧ result.2 = state)
    (nextLive := fun _ frame => ArtifactBinding.Captures captured frame)
    (fun _ _ retained => retained) (fun _ _ returned => .done ⟨returned, rfl⟩)
  simpa only [PIR.Process.bind_done] using connected

/-- Return selection of a closed arm accounts for its entire declared tuple. -/
def MathReturns {types : List Structured.Ty} (references : List Nat)
    (values : Values carriers.Value types) (frame : Domain.Environment carriers) : Prop :=
  Domain.read frame references = some (encodeHelperResult values)

/-- Closing an arm selects its exact result row and restores the outer frame.
Every internal checkpoint retains that frame, including before a stopped arm. -/
noncomputable def Simulation.closeMathArm {types : List Structured.Ty}
    (source : PIR.Process Structured.closedInterface (Values carriers.Value types))
    (target : PIR.Process (Domain.effects carriers) (Domain.Environment carriers))
    (captures caller : Domain.Environment carriers) (references : List Nat)
    (data : types.all Domain.localType = true)
    (certificate : Simulation (MathReturns references)
      (fun _ frame => ArtifactBinding.Captures captures frame)
      (source.interpret (Structured.closedLift (I := Domain.effects carriers))) target) :
    Simulation (fun values final => final = caller ++ encodeHelperResult values)
      (fun _ frame => ArtifactBinding.Captures caller frame)
      (source.interpret (Structured.closedLift (I := Domain.effects carriers)))
      ((target.interpret (Domain.withCallerFrame caller)).bind fun final =>
        match Domain.read final references with
        | some values => if Domain.sortsMatch (types.map ValueSort.data) values then
            .done (caller ++ values) else .halt .refused
        | none => .halt .refused) := by
  have entered := certificate.prefixFrames caller
  rw [closed_frame_identity] at entered
  have connected := entered.bind
    (sourceNext := fun values => .done values)
    (targetNext := fun final =>
      match Domain.read final references with
      | some values => if Domain.sortsMatch (types.map ValueSort.data) values then
          .done (caller ++ values) else .halt .refused
      | none => .halt .refused)
    (returnRelation := fun values final => final = caller ++ encodeHelperResult values)
    (nextLive := fun _ frame => ArtifactBinding.Captures caller frame)
    (fun _ _ retained => ArtifactBinding.captures_trans
      (ArtifactBinding.captures_append caller captures) retained)
    (fun values final returned => by
      change Domain.read final references = some (encodeHelperResult values) at returned
      simp only [returned, encodeHelperResult_sorts data values, ↓reduceIte]
      exact .done rfl)
  simpa only [PIR.Process.bind_done] using connected

/-- Selection composes the connected closed arms with exact caller/capture
readback. Both arms require evidence; no honest or successful input premise is
introduced, and the unselected process is never evaluated. -/
noncomputable def Simulation.mathBranch (program : Structured.Program)
    {captures results : List Structured.Ty}
    (arguments : Values carriers.Value captures) (condition : Bool)
    (sourceYes sourceNo : PIR.Process Structured.closedInterface (Values carriers.Value results))
    (yesBody noBody : Domain.View.Block carriers)
    (yes no : InstructionRegion)
    (yesInputs : yes.inputs = captures.map ValueSort.data)
    (noInputs : no.inputs = captures.map ValueSort.data)
    (formed : checkMathArms (Domain.mathCallMatches program) (results.map ValueSort.data) yes no = .ok ())
    (captureData : captures.all Domain.localType = true)
    (resultData : results.all Domain.localType = true)
    (environment : Domain.Environment carriers) (selector : Nat) (references : List Nat)
    (selected : environment[selector]? = some (.data (.boolean condition)))
    (read : Domain.read environment references = Domain.encodeValues arguments)
    (yesConnected : Simulation (MathReturns yes.yielded)
      (fun _ frame => ArtifactBinding.Captures (encodeHelperResult arguments) frame)
      (sourceYes.interpret (Structured.closedLift (I := Domain.effects carriers)))
      (yesBody (encodeHelperResult arguments)))
    (noConnected : Simulation (MathReturns no.yielded)
      (fun _ frame => ArtifactBinding.Captures (encodeHelperResult arguments) frame)
      (sourceNo.interpret (Structured.closedLift (I := Domain.effects carriers)))
      (noBody (encodeHelperResult arguments))) :
    Simulation (fun values final => final = environment ++ encodeHelperResult values)
      (fun _ frame => ArtifactBinding.Captures environment frame)
      ((if condition then sourceYes else sourceNo).interpret
        (Structured.closedLift (I := Domain.effects carriers)))
      (Domain.View.mathBranch program selector references (results.map ValueSort.data)
        yes no yesBody noBody environment) := by
  have capturesRead := read.trans (encodeHelperResult_eq captureData arguments)
  have same : yes.inputs = no.inputs := yesInputs.trans noInputs.symm
  simp only [Domain.View.mathBranch, Domain.selectMath, selected, capturesRead,
    same, noInputs, encodeHelperResult_sorts captureData arguments,
    formed, Except.isOk]
  cases condition with
  | false => exact Simulation.closeMathArm sourceNo _ _ _ _ resultData noConnected
  | true => exact Simulation.closeMathArm sourceYes _ _ _ _ resultData yesConnected

end Zkc.Construction.Original
