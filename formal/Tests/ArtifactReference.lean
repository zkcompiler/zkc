import Tools.Artifact.Main

set_option autoImplicit false

namespace Tests.ArtifactReference
open Tools.Interactive
open Tools.Artifact
open Lean (Json)

-- Nominal admission must never turn an uninstalled field/group into the finite
-- mathematical domain merely because its byte width or kind matches.
private def fieldWire : ByteArray :=
  (magic.push 1) ++ little 32 7
example : (decodeValue "field:bls12-381.fr" fieldWire).isOk = true := by native_decide
example : (decodeValue "field" fieldWire).isOk = false := by native_decide
example : (decodeValue "field:another.fr" fieldWire).isOk = false := by native_decide
example : (decodeValue "group:bls12-381.g1" fieldWire).isOk = false := by native_decide
example : (decodeValue "field" fieldWire).isOk = false := by native_decide

private def source : Source :=
  ⟨.explicit [⟨"selected_draw", "random.draw", ["bls12-381.fr"], ""⟩], [], [], [], []⟩
private def descriptor : Descriptor :=
  ⟨"main", "P", "V", [], "coins", [("ConfiguredDraw", "draw")], 0, .null⟩
private def location : Location := {
  entry := "main", binding := "root", path := [], protocol := "Protocol", role := "V",
  sourceRole := "V", localSite := "step", function := "ConfiguredDraw", operation := "draw" }
private def initial (budget : Nat) : Tools.Artifact.State := {
  cursor := ⟨ByteArray.empty, 0⟩, root := ByteArray.mk #[1], configuration := .null,
  answers := #[], transcriptBudget := budget }

private def drawWith (bytes : ByteArray) : String := Id.run do
  let action := evaluate source descriptor location "selected_draw" [] [.selectedRng 0]
  let (.error pending, _) := action.run (initial 1) | return "missing pending request"
  let state := { initial 1 with answers := #[⟨pending.request,
    .arr #[.str "ok", .str (hex bytes)]⟩] }
  match (action.run state).1 with
  | .ok [.field value, .selectedRng 1] => return toString value.val
  | .error error => return error.detail
  | _ => return "wrong output"

example : drawWith (ByteArray.mk (Array.replicate 63 0 |>.push 1)) = "1" := by native_decide
example : drawWith (ByteArray.mk (#[1] ++ Array.replicate 63 0)) =
    toString ((256^63) % fieldModulus) := by native_decide
example : drawWith (ByteArray.mk (Array.replicate 64 255)) =
    toString ((256^64-1) % fieldModulus) := by native_decide
example : drawWith (ByteArray.mk (Array.replicate 63 0)) = "transcript-challenge-width" := by native_decide

private def ristrettoDescriptor : Descriptor := { descriptor with
  json := .arr #[.str "zkc.construction/1", .str "main", .str "P", .str "V", .arr #[],
    .arr #[], .str "0", .str Bindings.ristrettoTranscript, .str "normalized"] }
private def ristrettoSource : Source := { source with
  environment := .explicit [⟨"selected_draw", "random.draw", [Bindings.ristrettoScalar], ""⟩] }
private def ristrettoAction :=
  evaluate ristrettoSource ristrettoDescriptor location "selected_draw" [] [.ristrettoRng 0]
private def requestFor (suite : String) : Result Json := do
  let origin ← treeBytes location.challenge
  transcriptRequest (initial 1).root #[.arr #[.str "challenge", .str (hex origin)]] suite

-- The exact request carries the suite and framing. An answer for the BLS suite
-- or the legacy protocol cannot satisfy it, even at the identical origin.
private def requestRoute (reply : Option Json) : Bool := Id.run do
  let state := match reply with
    | none => initial 1
    | some request => { initial 1 with answers := #[⟨request,
        .arr #[.str "ok", .str (hex (little 64 1))]⟩] }
  let (result, next) := ristrettoAction.run state
  let .error e := result | return false
  let .ok expected := requestFor Bindings.ristrettoTranscript | return false
  return e.reason == "pending-primitive" && e.detail == "exact-request-missing" &&
    e.request == expected && next.requests == #[expected] && next.usedAnswers.isEmpty &&
    next.draws == 1 && next.history.size == 1 && next.events.size == 1
example : requestRoute none = true := by native_decide
example : requestRoute (requestFor Bindings.transcriptIdentity).toOption = true := by native_decide
example : requestRoute (some (.arr #[.str "zkc.transcript-request/1",
    .str "arkworks.bls12-381/1", .str "01", .arr #[]])) = true := by native_decide

private def ristrettoBytes (bytes : ByteArray) : String × Nat × Nat := Id.run do
  let .ok request := requestFor Bindings.ristrettoTranscript | return ("bad-request", 0, 0)
  let (result, next) := ristrettoAction.run { initial 1 with
    answers := #[⟨request, .arr #[.str "ok", .str (hex bytes)]⟩] }
  let output := match result with
    | .ok [.arithmetic .ristretto (.field x), .ristrettoRng 1] => toString x.val
    | .error error => error.reason ++ ":" ++ error.detail
    | _ => "wrong-output"
  return (output, next.draws, next.history.size)
example : ristrettoBytes (little 64 1) = ("1", 1, 1) := by native_decide
example : ristrettoBytes (ByteArray.mk (Array.replicate 63 0 |>.push 1)) =
    (toString ((256^63) % Bindings.ristrettoModulus), 1, 1) := by native_decide
example : ristrettoBytes (ByteArray.mk (Array.replicate 64 255)) =
    (toString ((256^64 - 1) % Bindings.ristrettoModulus), 1, 1) := by native_decide
example : ristrettoBytes (little 63 1) = ("refused:transcript-challenge-width", 1, 1) := by native_decide

-- A retired source tag cannot enter the current artifact interpreter.
example : (artifactSource (.arr #[.str "zkc.protocol/2", .str "arkworks.bls12-381/1",
    .arr #[], .arr #[], .arr #[], .arr #[]])).isOk = false := by native_decide

-- Opaque group calculations stay public primitive requests. No scalar model or
-- fabricated algebraic oracle supplies a group result to this test.
private def groupPending : Bool :=
  let groupSource := { source with environment := .explicit [
    ⟨"generator", "curve.generator", [Bindings.ristrettoGroup], ""⟩] }
  let (result, next) := (evaluate groupSource ristrettoDescriptor location "generator" [] []).run (initial 1)
  match result with
  | .error e => e.reason == "pending-primitive" && e.request ==
      .arr #[.str "zkc.public-primitive/1", .arr #[], .str "curve.generator",
        .arr #[.str Bindings.ristrettoGroup], .arr #[], .arr #[]] && next.requests == #[e.request]
  | _ => false
example : groupPending = true := by native_decide

-- Failed transcript transitions retain the preceding request, but cannot append
-- a successful challenge/history event. Native resource generations are tested
-- separately by the resource reference; this artifact observation omits them.
private def stopped : String × Nat × Nat :=
  let (result, state) := (evaluate source descriptor location "selected_draw" [] [.selectedRng 0]).run (initial 0)
  (match result with | .error e => e.reason | _ => "returned", state.events.size, state.history.size)
example : stopped = ("exhausted", 1, 0) := by native_decide

-- Absorbed origins retain their established contract while typed operation
-- observations include explicit static arguments.
example : ((location.challenge.getArr?).toOption.map (·[0]!) == some (.str "zkc.logical-origin/1")) = true := by native_decide
example : (((location.request "random.draw" [] ["bls12-381.fr"]).getArr?).toOption.map (·[0]!) ==
    some (.str "zkc.logical-origin/2")) = true := by native_decide

-- Structural setup fixtures deliberately contain no valid curve points. These
-- controls exercise metadata/coverage only; the public service checks real keys.
private def keyWire (tail : UInt8 := 0) : ByteArray :=
  ("ZKCAR006".toUTF8.push 1) ++ little 8 1 ++
    ByteArray.mk ((Array.replicate 64 (7 : UInt8) ++ Array.replicate 191 0).push tail)
private def commitmentWire : ByteArray :=
  (magic.push 6) ++ ("ZKCAR006".toUTF8.push 2) ++ little 8 1 ++
    ByteArray.mk (Array.replicate 64 7 ++ Array.replicate 48 0)
private def setup : SetupConfiguration := { keys := [("a", .verifierKey keyWire)] }

example : (checkSetup setup "a" (.publicBytes "commitment" commitmentWire)).isOk = true := by native_decide
example : ((List.range 72).all fun i =>
    !(checkSetup setup "a" (.publicBytes "commitment"
      (commitmentWire.set! (15+i) (commitmentWire[15+i]! ^^^ 1)))).isOk) = true := by native_decide
example : (checkSetup setup "absent" (.publicBytes "commitment" commitmentWire)).isOk = false := by native_decide

private def fixture (count : Nat) : Source × Instance × Protocol := Id.run do
  let definition : Protocol := ⟨"Policy", ["P", "V"], [],
    [⟨"payload", "P", "commitment:multilinear.kzg.bls12-381/1"⟩,
     ⟨"a", "V", "verifier_key:multilinear.kzg.bls12-381/1"⟩,
     ⟨"b", "V", "verifier_key:multilinear.kzg.bls12-381/1"⟩], [], [],
    some [.loop "visits" (.constant count) [] ["payload"]
      [.message "commit" "commit" "P" "V" "payload" "received", .yield []] [], .ret []]⟩
  let binding : Instance := ⟨"policy", "Policy", [], [], [("P", "P"), ("V", "V")]⟩
  return (⟨.explicit [], [], [definition], [binding], [("main", "policy")]⟩, binding, definition)

private def sites (count : Nat) : Result (List ReceiveSite) :=
  let (source, binding, _) := fixture count
  receiveSites source binding
example : sites 0 = .ok [] := by native_decide
example : sites 1 = .ok [("policy", "V", "commit")] := by native_decide
example : sites 7 = sites 1 := by native_decide

private def strings (xs : List String) : Json := .arr (xs.map Json.str).toArray
private def inputPolicy : Json := strings ["P", "payload", "a"]
private def receivePolicy : Json := strings ["policy", "V", "commit", "a"]
private def configuration (tail : UInt8) (inputs receives : List Json) : Json :=
  .arr #[.str "zkc.public-configuration/1",
    .arr #[strings ["a", "verifier_key:multilinear.kzg.bls12-381/1", hex keyWire],
            strings ["b", "verifier_key:multilinear.kzg.bls12-381/1", hex (keyWire tail)]],
    .arr inputs.toArray, .arr receives.toArray]
private def configured (count : Nat) (json : Json) : Result Unit := do
  let (source, binding, definition) := fixture count
  let _ ← decodeConfiguration source descriptor binding definition json

example : configured 0 (configuration 0 [inputPolicy] []) = .ok () := by native_decide
example : configured 1 (configuration 0 [inputPolicy] [receivePolicy]) = .ok () := by native_decide
example : configured 0 (configuration 1 [inputPolicy] []) =
    .error "artifact-conflicting-verifier-keys" := by native_decide
example : configured 0 (configuration 0 [inputPolicy] [receivePolicy]) =
    .error "artifact-receive-site-or-duplicate" := by native_decide
example : configured 1 (configuration 0 [inputPolicy] []) =
    .error "artifact-receive-coverage" := by native_decide
example : configured 1 (configuration 0 [inputPolicy] [receivePolicy, receivePolicy]) =
    .error "artifact-receive-site-or-duplicate" := by native_decide
example : configured 0 (configuration 0 [inputPolicy, inputPolicy] []) =
    .error "artifact-input-setup-port-or-duplicate" := by native_decide
example : configured 0 (configuration 0 [strings ["P", "payload", "unknown"]] []) =
    .error "unbound:unknown" := by native_decide

private def readFailure (bytes : ByteArray) : String × Nat × Nat :=
  let state := { initial 1 with cursor := ⟨bytes, 0⟩ }
  let (result, state) := (readMessage source "field:bls12-381.fr" ("root", "V", "message")).run state
  (match result with | .error e => e.detail | _ => "accepted", state.cursor.position, state.history.size)
example : readFailure (little 8 1 ++ ByteArray.mk #[0]) = ("wire-header", 9, 0) := by native_decide
example : readFailure (little 8 2 ++ ByteArray.mk #[0]) = ("proof-truncated", 8, 0) := by native_decide
example : readFailure (little 8 (2^64-1)) = ("proof-message-limit", 8, 0) := by native_decide

-- The input/reply reader uses the same carrier-only preflight with a larger
-- byte ceiling, so exponent expansion cannot reach JSON parsing.
example : Decode.preflight "[1e999999]" byteLimit = .error "non-array-json-token" := by native_decide
example : Decode.preflight "[{}]" byteLimit = .error "non-array-json-token" := by native_decide
example : Decode.preflight "[true]" byteLimit = .error "non-array-json-token" := by native_decide
example : Decode.preflight "[\"1e999999\"]" byteLimit = .ok () := by native_decide
example : Decode.preflight "[]" 1 = .error "byte-limit" := by native_decide

end Tests.ArtifactReference
