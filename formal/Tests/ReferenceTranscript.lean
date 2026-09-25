import Tools.Interactive.GenericReference

set_option autoImplicit false

namespace Tests.ReferenceTranscript
open Tools.Interactive
open Lean (Json)

private def location : Reference.Location :=
  Reference.Location.plain "session" "root" "draw" "P"
private def attrs : List String := ["Protocol", "call", "Function", "draw", "V"]

example : (environmentSignature (.explicit [⟨"draw", "transcript.challenge", [Bindings.transcriptIdentity], ""⟩]) "logical" "draw"
    ("bad label" :: attrs.tail)).map (fun _ => ()) = .error "interactive-kernel-parameters" := by native_decide
example : (environmentSignature (.explicit [⟨"draw", "transcript.challenge", [Bindings.transcriptIdentity], ""⟩]) "logical" "draw"
    ("1_.-" :: attrs.tail)).isOk = true := by native_decide

-- Pin complete domain separation, independently of the external replay adapter.
private def expectedRequest : Json :=
    .arr #[.str "zkc.transcript-request/3", .str "merlin3.bls12-381.fr64be/1",
      .str "7a6b632e61727469666163742f31", .arr #[
        .arr #[.str "append", .str "62696e64696e67", .str "01"],
        .arr #[.str "append", .str "6f726967696e", .str "02"],
        .arr #[.str "append", .str "76616c7565", .str "03"],
        .arr #[.str "append", .str "6f726967696e", .str "04"],
        .arr #[.str "challenge", .str "6368616c6c656e6765", .str "64"]]]
example : (Reference.transcriptRequest (ByteArray.mk #[1])
    #[.arr #[.str "message", .str "02", .str "03"], .arr #[.str "challenge", .str "04"]]).map
      (· == expectedRequest) = .ok true := by native_decide

private def initial (budget : Nat) : Reference.State :=
  { resources := [⟨"t", "P", none, budget,
      .transcript Bindings.transcriptIdentity ((ByteArray.mk #[0]) ++ Tools.Artifact.little 8 0) #[], 0, 0⟩] }

private def summary (result : Except Reference.Fault (List Reference.Value) × Reference.State) :
    String × Nat × Nat × Nat :=
  let outcome := match result.1 with
    | .ok _ => "returned"
    | .error error => error.reason ++ ":" ++ error.detail
  match result.2.resources with
  | [r] => (outcome, r.generation, r.budget, match r.payload with
      | .transcript _ _ history => history.size | _ => 999)
  | _ => (outcome, 999, 999, 999)

private def observe (attributes : List String) (budget generation : Nat) :=
  summary ((Reference.transcriptObserve location attributes "t" generation (.boolean true)).run (initial budget))
private def challenge (attributes : List String) (budget generation : Nat) :=
  summary ((Reference.transcriptChallenge location attributes "t" generation).run (initial budget))

-- Invalid origin wins before resource consumption; no history is appended.
example : observe ["bad"] 0 0 = ("refused:transcript-origin", 0, 0, 0) := by native_decide
example : challenge ("a/b" :: attrs.tail) 0 0 =
    ("refused:transcript-origin", 0, 0, 0) := by native_decide
example : observe attrs 0 0 = ("exhausted:resource-budget", 1, 0, 0) := by native_decide
example : challenge attrs 0 0 = ("exhausted:resource-budget", 1, 0, 0) := by native_decide
example : observe attrs 2 1 = ("refused:capability-stale", 0, 2, 0) := by native_decide
example : observe attrs 2 0 = ("returned", 1, 1, 1) := by native_decide
example : challenge attrs 2 0 = ("pending-primitive:exact-request-missing", 1, 1, 1) := by native_decide

-- Session and executing role are intentionally absent from this hash contract.
example : Reference.transcriptOrigin location "challenge" attrs =
    Reference.transcriptOrigin { location with
      session := "different"
      scope := { location.scope with role := "V" } } "challenge" attrs := by native_decide

private def withBytes (bytes : ByteArray) : String := Id.run do
  let action := Reference.transcriptChallenge location attrs "t" 0
  let (_, pending) := action.run (initial 2)
  let some (.arr event) := pending.events.back? | return "missing event"
  let some request := event[1]? | return "missing request"
  let state := { initial 2 with answers := Std.HashMap.ofList [
    (request.compress, .arr #[.str "ok", .str (Tools.Artifact.hex bytes)])] }
  let (result, _) := action.run state
  match result with
  | .ok [.field f, .transcript _ "t" 1] => return toString f.val
  | .ok _ => return "wrong results"
  | .error error => return error.detail

-- Fixed vectors distinguish big-endian reduction from little-endian parsing.
example : withBytes (ByteArray.mk (Array.replicate 63 0 |>.push 1)) = "1" := by native_decide
example : withBytes (ByteArray.mk (#[1] ++ Array.replicate 63 0)) =
    toString ((256^63) % fieldModulus) := by native_decide
example : withBytes (ByteArray.mk (Array.replicate 64 255)) =
    toString ((256^64 - 1) % fieldModulus) := by native_decide
example : withBytes (ByteArray.mk (Array.replicate 63 0)) =
    "transcript-challenge-width" := by native_decide

end Tests.ReferenceTranscript
