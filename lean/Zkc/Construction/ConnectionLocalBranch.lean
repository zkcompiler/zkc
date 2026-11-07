module

public import Zkc.Construction.ConnectionMathSimulation

@[expose] public section

/-! Structural connection for a closed local selection. Controller dispatch
uses the same region formation, caller frames and ordered output selection as
the existing evaluator. The source result can carry a common controller
invariant; it need not be a mathematical tuple or a protocol-specific state.
-/
set_option autoImplicit false
namespace Zkc.Construction.ConnectionLocalBranch
open Zkc.Source
variable {carriers : Structured.Carriers} {A : Type}

/-- The entire declared result row is selected from the actual branch frame.
Same-typed permutations are visible to the caller's relation. -/
def Returns (relation : A → Domain.Environment carriers → Prop)
    (declared : List ValueSort) (yielded : List Nat)
    (value : A) (frame : Domain.Environment carriers) : Prop :=
  ∃ results, Domain.read frame yielded = some results ∧
    Domain.sortsMatch declared results = true ∧ relation value results

/-- Enter a closed arm with its caller, select its checked output and restore
that caller. A stopped arm retains both its reason and diagnostic frames. -/
noncomputable def closeArm
    (source : PIR.Process Structured.closedInterface A)
    (target : PIR.Process (Domain.effects carriers) (Domain.Environment carriers))
    (relation : A → Domain.Environment carriers → Prop)
    (captured caller : Domain.Environment carriers)
    (declared : List ValueSort) (yielded : List Nat)
    (certificate : Original.Simulation (Returns relation declared yielded)
      (fun _ frame ↦ ArtifactBinding.Captures captured frame)
      (source.interpret (Structured.closedLift (I := Domain.effects carriers))) target) :
    Original.Simulation
      (fun value final ↦ ∃ results, relation value results ∧ final = caller ++ results)
      (fun _ frame ↦ ArtifactBinding.Captures caller frame)
      (source.interpret (Structured.closedLift (I := Domain.effects carriers)))
      ((target.interpret (Domain.withCallerFrame caller)).bind fun final ↦
        match Domain.read final yielded with
        | some results => if Domain.sortsMatch declared results then
            .done (caller ++ results) else .halt .refused
        | none => .halt .refused) := by
  have entered := certificate.prefixFrames caller
  rw [Original.closed_frame_identity] at entered
  have connected := entered.bind
    (sourceNext := PIR.Process.done)
    (targetNext := fun final ↦ match Domain.read final yielded with
      | some results => if Domain.sortsMatch declared results then
          .done (caller ++ results) else .halt .refused
      | none => .halt .refused)
    (returnRelation := fun value final ↦
      ∃ results, relation value results ∧ final = caller ++ results)
    (nextLive := fun _ frame ↦ ArtifactBinding.Captures caller frame)
    (fun _ _ retained ↦ ArtifactBinding.captures_trans
      (ArtifactBinding.captures_append caller captured) retained)
    (fun value final related ↦ by
      cases read : Domain.read final yielded with
      | none =>
          exfalso
          obtain ⟨results, found, _⟩ := related
          rw [read] at found
          contradiction
      | some results =>
          have properties : Domain.sortsMatch declared results = true ∧
              relation value results := by
            obtain ⟨selected, found, sorts, related⟩ := related
            cases Option.some.inj (read.symm.trans found)
            exact ⟨sorts, related⟩
          simp only [properties.1, ↓reduceIte]
          exact .done ⟨results, properties.2, rfl⟩)
  simpa only [PIR.Process.bind_done] using connected

/-- Actual local dispatch checks both arms before taking the selected one.
Each branch law is installed once over its captured input; common composition
supplies caller preservation, complete output routing and refusal propagation.
No proof of an unused arm's successful execution is required. -/
noncomputable def simulation (program : Structured.Program)
    (sourceYes sourceNo : PIR.Process Structured.closedInterface A)
    (runYes runNo : Domain.View.Block carriers) (yes no : InstructionRegion)
    (relation : A → Domain.Environment carriers → Prop)
    (environment captured : Domain.Environment carriers)
    (condition : Bool) (selector : Nat) (captures : List Nat) (declared : List ValueSort)
    (readSelector : environment[selector]? = some (.data (.boolean condition)))
    (readCaptures : Domain.read environment captures = some captured)
    (sameInputs : yes.inputs = no.inputs)
    (sorts : Domain.sortsMatch yes.inputs captured = true)
    (formed : (checkClosedArms .local (Domain.closedOperationMatches program)
      declared yes no).isOk = true)
    (yesConnected : Original.Simulation (Returns relation declared yes.yielded)
      (fun _ frame ↦ ArtifactBinding.Captures captured frame)
      (sourceYes.interpret (Structured.closedLift (I := Domain.effects carriers)))
      (runYes captured))
    (noConnected : Original.Simulation (Returns relation declared no.yielded)
      (fun _ frame ↦ ArtifactBinding.Captures captured frame)
      (sourceNo.interpret (Structured.closedLift (I := Domain.effects carriers)))
      (runNo captured)) :
    Original.Simulation
      (fun value final ↦ ∃ results, relation value results ∧ final = environment ++ results)
      (fun _ frame ↦ ArtifactBinding.Captures environment frame)
      ((if condition then sourceYes else sourceNo).interpret
        (Structured.closedLift (I := Domain.effects carriers)))
      (Domain.View.localBranch program selector captures declared yes no runYes runNo environment) := by
  unfold Domain.View.localBranch Domain.selectClosed
  rw [readSelector, readCaptures]
  have otherSorts : Domain.sortsMatch no.inputs captured = true := sameInputs ▸ sorts
  simp only [sameInputs, otherSorts, formed, and_self, ↓reduceIte]
  cases condition with
  | false => exact closeArm sourceNo _ relation captured environment declared no.yielded noConnected
  | true => exact closeArm sourceYes _ relation captured environment declared yes.yielded yesConnected

end Zkc.Construction.ConnectionLocalBranch
