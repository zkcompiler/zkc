module

public import ZkcTools.StructuredSource.Discovery.Manual

@[expose] public section

namespace ZkcTools.StructuredSource.Discovery.Driver

open Lean Zkc.Source.Structured ZkcTools.StructuredSource.Discovery

/-- Experiment entry point only, outside shipped protocol dispatch. -/
def main (arguments : List String) : IO UInt32 := do
  let source :: armText :: roleText :: output :: rest := arguments
    | throw (IO.userError "usage: SNAPSHOT verifier|joint|manual ROLE_INDEX OUTPUT [MANUAL_DESCRIPTOR]")
  let arm ← match armText with
    | "verifier" => pure Arm.verifier | "joint" => pure Arm.joint | "manual" => pure Arm.manual
    | _ => throw (IO.userError "unknown arm")
  let text ← IO.FS.readFile source
  let program ← match decode text with
    | .ok program => pure program | .error error => throw (IO.userError error)
  let some role := roleText.toNat? | throw (IO.userError "invalid role index")
  let view ← match buildView program arm role with
    | .ok view => pure view | .error error => throw (IO.userError error)
  let outcome ← if arm == .manual then do
      let [descriptor] := rest | throw (IO.userError "manual descriptor required")
      let descriptorText ← IO.FS.readFile descriptor
      match Json.parse descriptorText >>= manualRequest view with
      | .ok result => pure result | .error error => throw (IO.userError error)
    else do
      if !rest.isEmpty then throw (IO.userError "automatic arm cannot read manual descriptors")
      pure (discover view)
  let result := Json.mkObj [("format", toJson "zkc.reference-discovery/0"),
    ("view", viewJson view), ("outcome", outcomeJson outcome)]
  IO.FS.writeFile output (result.compress ++ "\n")
  return 0

end ZkcTools.StructuredSource.Discovery.Driver
