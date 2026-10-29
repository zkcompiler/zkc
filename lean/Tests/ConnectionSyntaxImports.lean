import Tests.ConnectionSyntax

/-! Imported ordinary syntax constants are reused as leaves. Importing this
module does not repeat normalization of the branching source template. -/
set_option autoImplicit false
namespace Tests.ConnectionSyntaxImports
open Lean Meta Elab Tactic

elab "check_imported_syntax" : tactic => withMainContext do
  let cache ← ZkcTools.ConstructionBindings.Syntax.newCache
  let .defnInfo definition ← getConstInfo ``Tests.ConnectionSyntax.cachedBranch
    | throwError "expected the retained syntax definition"
  let value := definition.value
  let normalized ← ZkcTools.ConstructionBindings.Syntax.normalize cache value
  unless value == normalized && (← cache.declarations.get).isEmpty do
    throwError "imported syntax was expanded instead of reused"
  (← getMainGoal).assign (← mkEqRefl normalized)
  replaceMainGoal []

example : Tests.ConnectionSyntax.cachedBranch = Tests.ConnectionSyntax.cachedBranch := by
  check_imported_syntax
end Tests.ConnectionSyntaxImports
