import Tools.Artifact.Identity.Laws

set_option autoImplicit false

namespace Tests.FrontendIdentity
open Lean (Json)
open Tools.Interactive
open Tools.Artifact.Identity

private def agrees (actual : Result Json) (expected : String) : Bool :=
  match actual, Decode.parse expected with
  | .ok a, .ok b => a == b
  | _, _ => false

private def resolved (text : String) : Result Json := do
  return (← resolveBody 8 0 (← Decode.parse text)).json

-- Independent preorder vector: zero-trip nested bodies still consume sites;
-- the terminal instructions and all original SSA spellings remain intact.
example : agrees (resolved
    "[[\"loop\",\"site1\",[\"constant\",\"0\"],[],[],[[\"stop\",\"site0\",\"V\",\"reject\"]],[]],[\"return\",[]]]")
    "[[\"loop\",\"site0\",[\"constant\",\"0\"],[],[],[[\"stop\",\"site1\",\"V\",\"reject\"]],[]],[\"return\",[]]]" = true := by
  native_decide

example : resolveName [("old", "site0"), ("old", "site1")] "old" =
    .error "identity-site-reference" := by native_decide
example : resolveName [("old", "site0")] "missing" =
    .error "identity-site-reference" := by native_decide
example : (resolveBody 0 0 (.arr #[])).isOk = false := by native_decide
example : (normalizeBody [] 0 {} (.arr #[])).isOk = false := by native_decide

-- The explicit carrier requires an origin pair even for ordinary functions.
example : (Explicit.decodeOrigin (.arr #[])).isOk = false := by
  native_decide

private def scopeVector : Result Json := do
  let scope : Scope := ⟨[("public", "v0"), ("coins", "v1"), ("captured", "v2")], 3⟩
  normalizeBody [] 8 scope (← Decode.parse
    "[[\"loop\",\"site0\",[\"constant\",\"0\"],[[\"inner\",\"public\"]],[\"captured\"],[[\"yield\",[\"inner\"]]],[\"result\"]],[\"return\",[\"result\",\"captured\"]]]")

-- Fresh inner binders, outer RHS references, and outer result allocation are
-- independently specified, rather than read back from a normalizer result.
example : agrees scopeVector
    "[[\"loop\",\"site0\",[\"constant\",\"0\"],[[\"v0\",\"v0\"]],[[\"v1\",\"v2\"]],[[\"yield\",[\"v0\"]]],[\"v3\"]],[\"return\",[\"v3\",\"v2\"]]]" = true := by
  native_decide

example : agrees (do
    let body ← Decode.parse "[[\"op\",\"site0\",\"alias\",[],[\"x\"],[\"y\",\"z\"]],[\"return\",[\"y\",\"z\"]]]"
    normalizeBody [⟨"alias", "random.draw", ["bls12-381.fr"], "arkworks/random.draw"⟩]
      8 ⟨[("x", "v0")], 1⟩ body)
    "[[\"op\",\"site0\",[\"operation\",\"random.draw\",[\"bls12-381.fr\"]],[],[\"v0\"],[\"v1\",\"v2\"]],[\"return\",[\"v1\",\"v2\"]]]" = true := by
  native_decide

end Tests.FrontendIdentity
