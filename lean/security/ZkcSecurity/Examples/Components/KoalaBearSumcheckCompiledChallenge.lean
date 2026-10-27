module

public import ZkcSecurity.Examples.Components.KoalaBearSumcheckCompiled
public import ZkcSecurity.FiatShamir.DomainViewReading

@[expose] public section

/-! A checked nominal bridge at the actual constructed root's challenge.
This local association retains every reply and the complete physical frame.
It does not establish the separate whole-root canonical soundness property. -/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000
noncomputable section
namespace ZkcSecurity.Examples.Components.KoalaBearSumcheckCompiledChallenge
open Zkc.Source Zkc.Construction
open ZkcSecurity.FiatShamir.DomainReduction
open ZkcSecurity.Domains.KoalaBearModel (model octicIdentity)
open ZkcSecurity.Examples.Components.KoalaBearSumcheckCompiled

def challenge : Instruction :=
  (artifact.instructions.find? fun instruction => match instruction.operation with
    | .challenge .. => true | _ => false).get (by decide +kernel)

theorem retained : challenge ∈ artifact.instructions :=
  List.mem_of_find?_eq_some (Option.some_get _).symm

def template : Template := match challenge.operation with
  | .challenge _ _ value => value
  | _ => ⟨"", [], []⟩
def state : Nat := challenge.operands[0]?.getD 0
def coordinates : Nat := challenge.operands[1]?.getD 0
def origin : Origin :=
  (Domain.queryOrigin compiled.selection.context artifact.policy.suite octicIdentity template []).get
    (by decide +kernel)

theorem found : Domain.queryOrigin compiled.selection.context artifact.policy.suite
    octicIdentity template [] = some origin := (Option.some_get _).symm

theorem request : origin.request = some (.draw octicIdentity) :=
  Domain.queryOrigin_request _ _ _ _ _ _ found

/-- Existing admitted projection links the retained call occurrence to the
source query under the selected root service. -/
theorem source_origin_link : origin = compiled.selection.context.query
    (KoalaBearSumcheckSource.site "label_6368616c6c656e6765") (.draw octicIdentity) := by
  decide +kernel

def frame (history : Domain.History model.toCarriers) : Domain.Environment model.toCarriers :=
  ((List.replicate (coordinates + 1) (.data (.index 0))).set state
    (.transcript artifact.policy.suite history)).set coordinates (.indices [])

/-- The existing nominal rules discharge the real instruction, with no
uniform-carrier substitution and no premise restricting challenge replies. -/
theorem bridge (history : Domain.History model.toCarriers) :
    Bridge queryInterface (fun _ _ => True) history
      (Domain.step model imported.program compiled.selection.context challenge (frame history))
      (.call (.query history origin) fun raw => .done
        (frame history ++ [.data (.field octicIdentity (fieldReply request raw)),
          .transcript artifact.policy.suite (history ++ [.challenge origin])])) := by
  have actual : Domain.step model imported.program compiled.selection.context challenge (frame history) =
      Domain.View.challenge compiled.selection.context artifact.policy.suite octicIdentity template
        state coordinates [.data (.field octicIdentity), .transcript artifact.policy.suite] (frame history) := by
    kernel_rfl
  rw [actual]
  exact ⟨challenge_reading _ _ _ _ _ _ _ history [] origin (by kernel_rfl) (by kernel_rfl) found request,
    challenge_coherent _ _ _ _ _ _ _ history [] origin (by kernel_rfl) (by kernel_rfl) found request⟩

end ZkcSecurity.Examples.Components.KoalaBearSumcheckCompiledChallenge
