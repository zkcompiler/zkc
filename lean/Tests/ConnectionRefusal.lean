import Lean.Elab.Tactic

/-! Negative controls for a proof-producing method. Resource exhaustion and
unrelated errors are not successful controls. A refusal is not a proof that the
fixed semantic proposition is false. -/
namespace Tests.ConnectionRefusal
meta section
open Lean in
private partial def staticFailureText : MessageData → String
  | .ofFormatWithInfos format => format.fmt.pretty
  | .withContext _ message | .withNamingContext _ message | .ofWidget _ message
  | .nest _ message | .group message | .tagged _ message | .ofOriginatingSyntax _ message =>
      staticFailureText message
  | .compose left right => staticFailureText left ++ staticFailureText right
  | .trace _ message children => staticFailureText message ++
      String.join (children.toList.map staticFailureText)
  | _ => ""

open Lean Elab Tactic in
elab "expect_connection_refusal" label:str " because " expected:str body:tacticSeq : tactic => do
  let trace ← IO.getEnv "ZKC_CONNECTION_CONTROL_TRACE"
  if let some path := trace then
    IO.FS.withFile path .append fun file => file.putStrLn s!"begin: {label.getString}"
  let saved ← saveState
  let failure ← try
    Term.withoutErrToSorry <| withoutRecover <| evalTactic body
    pure none
  catch exception =>
    if exception.isRuntime || exception.isInterrupt then throw exception
    pure (some exception.toMessageData)
  saved.restore
  let some failure := failure | throwError "expected refusal: {label.getString}"
  if failure.hasTag (fun name => (`runtime).isPrefixOf name) then
    throwError "resource exhaustion is not a checked refusal: {label.getString}"
  -- Do not delaborate expression/goal holes: their diagnostic trees can dwarf
  -- the checked proof. Runtime tags and static error text retain refusal causes.
  let text := staticFailureText failure
  for limit in ["maximum number of heartbeats", "deterministic timeout", "recursion depth", "out of memory"] do
    if (text.splitOn limit).length > 1 then
      throwError "resource exhaustion is not a checked refusal: {label.getString}"
  unless (text.splitOn expected.getString).length > 1 do
    throwError "wrong refusal cause for {label.getString}: expected {expected.getString}, got {text}"
  let reason := String.ofList (text.toList.take 700)
  logInfo m!"checked_refusal: {label.getString}; reason={reason}"
  if let some path := trace then
    IO.FS.withFile path .append fun file => file.putStrLn s!"checked: {label.getString}; reason={reason}"

end

end Tests.ConnectionRefusal
