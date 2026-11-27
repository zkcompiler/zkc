import Zkc.Tests.Core.Deployment.Fixtures

/-!
Fail-closed declaration, session, retry, sample, layout, and law-keyed suite refusal regressions
asserting exact `Rule` identifiers across `deploy` and `deployIdeal`.
-/

namespace Zkc.Core.Tests.Deployment

open Zkc.Core

set_option maxRecDepth 16000

private def deployFailsWith (decl : Declaration) (r : Rule) : Bool :=
  match deploy deployEncoder admittedSuite decl with
  | .error errs => errs.any (fun e => decide (e.rule = r))
  | .ok _ => false

private def deployIdealFailsWith (decl : Declaration) (r : Rule) : Bool :=
  match deployIdeal deployEncoder idealServiceKey admittedSuite decl with
  | .error errs => errs.any (fun e => decide (e.rule = r))
  | .ok _ => false

private def twoLawDeployFailsWith (decl : Declaration) (r : Rule) : Bool :=
  match deploy twoLawEncoder admittedTwoLaw decl with
  | .error errs => errs.any (fun e => decide (e.rule = r))
  | .ok _ => false

theorem deploy_fail_closed_declaration_and_session_controls :
    -- Mismatched `kinds.length`
    deployFailsWith { schnorrDecl with kinds := [.online] } .protocol = true ∧
    deployIdealFailsWith { schnorrDecl with kinds := [.online] } .protocol = true ∧
    -- Unsupported non-empty `context`, `grinds`, `commits`, `pins`
    deployFailsWith { schnorrDecl with context := [⟨99⟩] } .protocol = true ∧
    deployFailsWith { schnorrDecl with grinds := [⟨8, []⟩] } .protocol = true ∧
    deployFailsWith { schnorrDecl with commits := [⟨⟨1⟩, ⟨[], []⟩, none, none⟩] } .protocol = true ∧
    deployFailsWith { schnorrDecl with pins := [⟨⟨[], ⟨12⟩⟩, ⟨1⟩, [0]⟩] } .protocol = true ∧
    deployIdealFailsWith { schnorrDecl with context := [⟨99⟩] } .protocol = true ∧
    deployIdealFailsWith { schnorrDecl with grinds := [⟨8, []⟩] } .protocol = true ∧
    deployIdealFailsWith { schnorrDecl with commits := [⟨⟨1⟩, ⟨[], []⟩, none, none⟩] } .protocol = true ∧
    deployIdealFailsWith { schnorrDecl with pins := [⟨⟨[], ⟨12⟩⟩, ⟨1⟩, [0]⟩] } .protocol = true ∧
    -- Empty or non-byte `sessionTag` refused with `Rule.literal`
    deployFailsWith { schnorrDecl with construction := .derived toySuite (some []) } .literal = true ∧
    deployFailsWith { schnorrDecl with construction := .derived toySuite (some [300]) } .literal = true ∧
    deployIdealFailsWith { schnorrDecl with construction := .derived toySuite (some []) } .literal = true ∧
    deployIdealFailsWith { schnorrDecl with construction := .derived toySuite (some [300]) } .literal = true ∧
    -- Interactive declaration validation (`layout`, `samples`, `retry`, online count, `prover`)
    deployFailsWith { interactiveDecl with layout := some ⟨toyLayoutModule, [], []⟩ } .protocol = true ∧
    deployFailsWith { interactiveDecl with samples := some ⟨109⟩ } .protocol = true ∧
    deployFailsWith { interactiveDecl with kinds := [.online, .offline] } .protocol = true ∧
    deployFailsWith { interactiveDecl with prover := some 7 } .protocol = true ∧
    deployFailsWith { interactiveDecl with retry := some (2, ⟨[], ⟨409⟩⟩) } .attempt = true ∧
    -- Authored declaration with `samples` refused
    deployFailsWith { authoredDecl with samples := some ⟨109⟩ } .protocol = true ∧
    -- Missing layout / missing suite slots / non-derived `deployIdeal` / bogus `samples` in `deployIdeal`
    deployFailsWith { schnorrDecl with layout := none } .callee = true ∧
    deployFailsWith { schnorrDecl with construction := .derived toyIdealOnlySuite none } .callee = true ∧
    deployIdealFailsWith interactiveDecl .protocol = true ∧
    deployIdealFailsWith authoredDecl .protocol = true ∧
    deployIdealFailsWith { schnorrDecl with samples := some ⟨9999⟩ } .callee = true ∧
    -- Missing law-specific `SuiteSlot.derive` for `.nonzero` when no fallback `members` entry exists
    twoLawDeployFailsWith { twoLawDecl with construction := .derived twoLawSuiteIncomplete none } .callee = true := by
  decide +kernel

theorem deploy_fail_closed_retry_and_layout_controls :
    -- Retry targeting verifier-owned attempt refused with `Rule.attempt`
    deployFailsWith { schnorrDecl with entry := ⟨208⟩, retry := some (4, ⟨[], ⟨909⟩⟩) } .attempt = true ∧
    deployIdealFailsWith { schnorrDecl with entry := ⟨208⟩, retry := some (4, ⟨[], ⟨909⟩⟩) } .attempt = true ∧
    -- `abort` guard outside the declared retry target refused with `Rule.attempt`
    deployFailsWith { schnorrDecl with entry := ⟨209⟩, retry := some (4, ⟨[], ⟨940⟩⟩) } .attempt = true ∧
    deployIdealFailsWith { schnorrDecl with entry := ⟨209⟩, retry := some (4, ⟨[], ⟨940⟩⟩) } .attempt = true ∧
    -- Retry bound `0` refused with `Rule.attempt`
    deployFailsWith { retrySchnorrDecl with retry := some (0, ⟨[], ⟨409⟩⟩) } .attempt = true ∧
    deployIdealFailsWith { retrySchnorrDecl with retry := some (0, ⟨[], ⟨409⟩⟩) } .attempt = true ∧
    -- Unknown / duplicate / wrong-kind `layout.carry`
    deployFailsWith { schnorrDecl with layout := some ⟨toyLayoutModule, [⟨[], ⟨999⟩⟩], []⟩ } .protocol = true ∧
    deployFailsWith { schnorrDecl with layout := some ⟨toyLayoutModule, [⟨[], ⟨13⟩⟩, ⟨[], ⟨13⟩⟩], []⟩ } .protocol = true ∧
    deployFailsWith { schnorrDecl with layout := some ⟨toyLayoutModule, [⟨[], ⟨12⟩⟩], []⟩ } .protocol = true ∧
    -- Unknown / duplicate / wrong-kind `layout.recover`
    deployFailsWith { schnorrDecl with
      layout := some ⟨toyLayoutModule, [⟨[], ⟨13⟩⟩], [(⟨[], ⟨999⟩⟩, ⟨108⟩)]⟩ } .protocol = true ∧
    deployFailsWith { schnorrDecl with
      layout := some ⟨toyLayoutModule, [⟨[], ⟨13⟩⟩], [(⟨[], ⟨12⟩⟩, ⟨108⟩), (⟨[], ⟨12⟩⟩, ⟨108⟩)]⟩ } .protocol = true ∧
    deployFailsWith { schnorrDecl with
      layout := some ⟨toyLayoutModule, [], [(⟨[], ⟨13⟩⟩, ⟨108⟩)]⟩ } .protocol = true ∧
    -- Compact `recover` refused on non-straight-line `.choose` protocol (streaming accepted in `Behavior`)
    deployFailsWith { branchingStreamingDecl with
      layout := some ⟨toyLayoutModule, [⟨[], ⟨513⟩⟩], [(⟨[], ⟨512⟩⟩, ⟨108⟩)]⟩ } .protocol = true ∧
    -- Nested self-retry detected by `Shape.noNestedAttempt`
    Shape.noNestedAttempt (V := deployVocab) ⟨[], ⟨500⟩⟩ []
      (.attempt ⟨500⟩ [0] (.attempt ⟨500⟩ [0] .nil .nil) .nil) = false := by
  decide +kernel

end Zkc.Core.Tests.Deployment
