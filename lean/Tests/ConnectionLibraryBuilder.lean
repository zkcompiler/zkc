import ZkcTools.ConstructionBindings.LibraryBuilder
import ZkcExamples.Structured.Generated.Bindings.SmallSumcheckInputs
import ZkcExamples.Structured.Generated.Bindings.TwoSumsInputs

/-! Actual admitted callee libraries, assembled without instance indices,
role patterns, per-call maps or authored normalization proofs. Full target
connections are tested separately. -/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
noncomputable section
namespace Tests.ConnectionLibraryBuilder
open Zkc.Source Zkc.Source.Structured NormalForm Zkc.Construction ConnectionLibrary
open Lean Meta Elab Tactic

elab "build_test_library" payload:term:max &"roles" roles:term : tactic => withMainContext do
  Term.withoutErrToSorry <| withoutRecover do
    let payload ← Term.elabTerm payload (some (mkConst ``UnitPayload))
    let roles ← Term.elabTerm roles (some (← mkAppM ``List #[mkConst ``Nat]))
    let (keys, library) ← ZkcTools.ConstructionBindings.LibraryBuilder.propose payload roles
    let goal ← getMainGoal
    let [keysGoal, libraryGoal] ← goal.apply (← mkConstWithFreshMVarLevels ``Sigma.mk)
      { newGoals := .all } | throwError "test-library-shape"
    keysGoal.assign keys
    libraryGoal.assign library
    replaceMainGoal []

private abbrev small := ZkcExamples.Structured.Generated.Bindings.SmallSumcheckInputs.program.payload
private abbrev two := ZkcExamples.Structured.Generated.Bindings.TwoSumsInputs.program.payload

def smallLibrary : Σ keys, Library small keys := by build_test_library small roles [0,1]
def twoLibrary : Σ keys, Library two keys := by build_test_library two roles [0,1]

example : smallLibrary.1.length = 2 := by decide +kernel
example : twoLibrary.1.length = 2 := by decide +kernel
example : twoLibrary.1.map (·.role) = [1,0] := by decide +kernel
example (model : DomainModel) {types : List Ty} (inputs : Values (Component model.Value) types) :
    CalleesHold (Occurrence.table model two) (twoLibrary.2.processes model) inputs :=
  twoLibrary.2.holds model inputs

example : True := by
  fail_if_success
    have refused : Σ keys, Library two keys := by build_test_library two roles [2]
  trivial

#print axioms smallLibrary
#print axioms twoLibrary
end Tests.ConnectionLibraryBuilder
