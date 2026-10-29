import ZkcTools.ConstructionBindings.Syntax

/-! The proposer caches syntax with implicit dependent indices as well as
explicit operands. A branching term has a linear checked representation;
its ordinary definitional meaning and a second cache use are checked here. -/
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
namespace Tests.ConnectionSyntax
open Zkc.Source Zkc.Source.Structured NormalForm
open Lean Meta Elab Tactic

def branching : Nat → Term [] [] (.field "field")
  | 0 => .field "field" 1
  | n + 1 => .calc (.fieldAdd "field") rfl (.cons (branching n) (.cons (branching n) .nil)) .here

elab "check_cached_syntax" input:term:max &"within" bound:num : tactic => withMainContext do
  let cache ← ZkcTools.ConstructionBindings.Syntax.newCache
  let original ← Term.elabTerm input none
  let proposed ← ZkcTools.ConstructionBindings.Syntax.normalize cache original
  unless proposed.isConst do throwError "syntax fixture did not produce a checked constant"
  let count := (← cache.declarations.get).size
  unless count < bound.getNat do throwError "syntax fixture expanded a branching term"
  let reused ← ZkcTools.ConstructionBindings.Syntax.normalize cache original
  unless reused == proposed do throwError "syntax fixture did not reuse its checked constant"
  let goal ← getMainGoal
  goal.assign (← mkEqRefl proposed)
  replaceMainGoal []

example : branching 10 = branching 10 := by check_cached_syntax (branching 10) within 100

/-- Repeated scope extension exposes the same substitution input at many
uses. Both the term and its computed dependent scope must be shared. -/
def shifted : (depth : Nat) → Term [] (List.replicate depth (.value .index)) (.field "field")
  | 0 => branching 10
  | depth + 1 => (shifted depth).rename .there

example : shifted 10 = shifted 10 := by check_cached_syntax (shifted 10) within 1000

elab "check_backtracked_syntax" : tactic => withMainContext do
  let cache ← ZkcTools.ConstructionBindings.Syntax.newCache
  let first ← Term.elabTerm (← `(shifted 3)) none
  let second ← Term.elabTerm (← `([true, false])) none
  let saved ← saveState
  let abandoned ← ZkcTools.ConstructionBindings.Syntax.normalize cache first
  saved.restore
  let other ← ZkcTools.ConstructionBindings.Syntax.normalize cache second
  unless abandoned != other do throwError "backtracking recycled a cached syntax name"
  let restored ← ZkcTools.ConstructionBindings.Syntax.normalize cache first
  (← getMainGoal).assign (← mkEqRefl restored)
  replaceMainGoal []

example : shifted 3 = shifted 3 := by check_backtracked_syntax

elab "retain_cached_branch" : tactic => withMainContext do
  let cache ← ZkcTools.ConstructionBindings.Syntax.newCache
  let original ← Term.elabTerm (← `(branching 10)) none
  let proposed ← ZkcTools.ConstructionBindings.Syntax.normalize cache original
  (← getMainGoal).assign proposed
  replaceMainGoal []

noncomputable def cachedBranch : Term [] [] (.field "field") := by retain_cached_branch
example : cachedBranch = branching 10 := rfl

end Tests.ConnectionSyntax
