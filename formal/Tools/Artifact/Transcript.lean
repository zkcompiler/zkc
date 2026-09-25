import Tools.Artifact.Codec
import Tools.Interactive.Sampling

set_option autoImplicit false

namespace Tools.Artifact
open Lean (Json)
open Tools.Interactive

/-- Prefix-free duplex frame. Lengths and draw widths are unsigned 64-bit big endian.
The reference constructs the exact bytes independently of the native adapter. -/
def duplexFrame (tag : UInt8) (label payload : ByteArray) : ByteArray :=
  let be (n : Nat) := ByteArray.mk ((little 8 n).data.reverse)
  ByteArray.mk #[tag] ++ be label.size ++ label ++ be payload.size ++ payload

private def duplexRequest (root : ByteArray) (history : Array Json) : Result Json := do
  let absorb (tag : UInt8) (name : String) (data : ByteArray) :=
    Json.arr #[.str "absorb", .str (hex (duplexFrame tag name.toUTF8 data))]
  let mut steps := #[absorb 0 "domain" "zkc.artifact/1".toUTF8,
    absorb 0 "suite" Bindings.spongefishTranscript.toUTF8, absorb 1 "binding" root]
  for action in history do
    match ← Decode.array action with
    | [.str "message", .str origin, .str value] =>
        steps := steps.push (absorb 1 "origin" (← unhex origin))
          |>.push (absorb 1 "value" (← unhex value))
    | [.str "challenge", .str origin] =>
        steps := steps.push (absorb 1 "origin" (← unhex origin))
          |>.push (absorb 2 "challenge" (ByteArray.mk #[0, 0, 0, 0, 0, 0, 0, 64]))
          |>.push (.arr #[.str "squeeze", .str "64"])
    | _ => throw "transcript-history"
  return .arr #[.str "zkc.duplex-request/1", .str Bindings.spongefishTranscript, .arr steps]

/-- Full call sequence, including domain and labels. The external adapter
interprets these calls; it does not choose a domain-separation protocol. -/
def transcriptRequest (root : ByteArray) (history : Array Json) (suite : String := Bindings.transcriptIdentity) : Result Json := do
  ensure (Bindings.transcriptDomain suite) "transcript-domain"
  if suite == Bindings.spongefishTranscript then return ← duplexRequest root history
  let label (s : String) := Json.str (hex s.toUTF8)
  let append (name : String) (value : Json) := Json.arr #[.str "append", label name, value]
  let mut steps := #[append "binding" (.str (hex root))]
  for action in history do
    match ← Decode.array action with
    | [.str "message", origin, value] =>
        steps := steps.push (append "origin" origin) |>.push (append "value" value)
    | [.str "challenge", origin] =>
        steps := steps.push (append "origin" origin) |>.push (.arr #[.str "challenge", label "challenge", .str "64"])
    | [.str "challenge-continuation"] =>
        ensure (suite == Bindings.extensionTranscript) "transcript-history"
        steps := steps.push (.arr #[.str "challenge", label "challenge", .str "64"])
    | [.str "index", origin, bound] =>
        ensure (suite == Bindings.extensionTranscript) "query-suite"
        let n ← Decode.natural bound
        ensure (Sampling.validBound n) "query-bound"
        steps := steps.push (append "origin" origin)
          |>.push (append "query-bound" (.str (hex (little 8 n))))
          |>.push (.arr #[.str "challenge", label "query-index", .str "64"])
    | _ => throw "transcript-history"
  return .arr #[.str "zkc.transcript-request/3", .str suite,
    label "zkc.artifact/1", .arr steps]


end Tools.Artifact
