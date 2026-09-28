import Tools.Mathematical.Json
import Tests.Checks

set_option autoImplicit false
namespace Tests.MathematicalJson

private def stringValue (input : String) : Option String :=
  match Tools.Mathematical.Json.parse input with
  | .ok (.string value) => some value
  | _ => none

def run : IO Unit := do
  let checks ← Checks.start
  checks.holds (stringValue "\"\\ud83d\\ude00\"" == some "😀")
    "surrogate pair has its Unicode scalar value"
  checks.holds (stringValue "\"😀\"" == stringValue "\"\\ud83d\\ude00\"")
    "raw and escaped supplementary Unicode agree"
  checks.holds (stringValue "\"\\u0000\"" == some (String.singleton '\x00'))
    "valid escaped NUL stays distinct from invalid Unicode"
  checks.holds (stringValue "\"\\ufffd\"" == some "�")
    "authored replacement character is valid"
  for invalid in ["\"\\ud800\"", "\"\\udc00\"", "\"\\udc00\\ud800\"",
      "\"\\ud800\\u0041\"", "\"\\ud800x\""] do
    checks.holds (!(Tools.Mathematical.Json.parse invalid).isOk)
      s!"refuse invalid surrogate sequence {invalid}"
  checks.finish "mathematical JSON Unicode"

#eval run
end Tests.MathematicalJson
