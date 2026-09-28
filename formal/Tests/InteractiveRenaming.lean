import Tools.Interactive.Projection

set_option autoImplicit false

namespace Tests.InteractiveRenaming
open Tools.Interactive

private def arm (returned : String) : List Instruction :=
  [.op "first" "add" [] ["u", "u"] ["first"],
   .op "second" "add" [] ["first", "first"] ["second"],
   .yield [returned]]

private def function (returned : String) : Function :=
  ⟨"F", [("tag", "Variant"), ("a", "field"), ("b", "field"), ("captured", "field")],
    ["field"], some [.localMatch "match" "tag" ["captured"]
      [("Left", ["u"], arm returned)] ["result"], .ret ["result"]]⟩

-- Renaming is a syntax utility, not type admission. A captured outer v3 must
-- remain distinct from the second local result, also at inner position three.
#guard match normalizeFunction (function "captured"), normalizeFunction (function "second") with
  | .ok left, .ok right => left != right
  | _, _ => false
#guard (normalizeFunction (function "captured")).isOk

end Tests.InteractiveRenaming
