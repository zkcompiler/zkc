import Zkc.Tests.Frontend.Protocols
import Zkc.Core.ProofIdentity

/-!
# Schemes

- Without the reference, on programs in memory with a library that binds the suite
  `suite.merlin3.bls12-381.fr64be/0`: a derived Schnorr scheme is constructed, its constructed
  program admitted and projected, and its honest proof accepted; a scheme whose roles both send,
  whose prover draws, whose `prover` line contradicts the protocol, whose protocol has three roles,
  or that neither sends nor draws without a `prover` line, is refused (SC3); an input that the
  verifier holds alone is refused (SC4); a draw of a group is refused (SC5); a draw of `bool`, a
  `context` line, a suite in source and `construction interactive` wait.
- With the reference: `scheme Proof = Schnorr<G1>` of `examples/schnorr_example.zkc` with
  `construction derived(Merlin3Bls12381)`. The constructed program is admitted (elaborated again,
  and its functions and protocols pass the check of facts) and projected; the suite's rows that
  each role applies, with their labels, are the schedule of the README. For the statement
  `(G, 7·G)`, the witness 7 and a fixed nonce, the proof is the bytes committed here, and the
  bytes that the independent replay `scripts/replay_derived_schnorr.py` computes: a `python3`
  that does not run, or a replay that fails, fails the suite.
  The honest proof is accepted; on the statement validated once, the proof with each byte
  changed, each proper prefix and the proof with one more byte are not, each stopping the
  verifier `reject`, never `undefined`. A proof
  from the sampler's seed is accepted, and one for a wrong witness is not. Every scheme of
  `examples/` is constructed and admitted, or waits; the derived OR proof of `Or<G1>` and the
  derived Sumcheck proof of `Sumcheck<Fr, 10>` are accepted when honest, and not for another
  statement, a wrong witness or a changed byte.
-/

namespace Zkc.Tests.Frontend

open Zkc.Frontend
open Zkc.Frontend.Syntax
open Zkc.Core.Concrete (Datum)

/-! ## Programs in memory -/

/-- The library of the programs in memory, with the interface of suites and the suites of the
catalogue. -/
def schemeLibrary : Array (String × String) := nameLibrary ++ #[
  ("zkc::construction", "module zkc::construction
pub interface Suite:
    type Challenge: Field
"),
  ("zkc::suites", "module zkc::suites
use zkc::construction::{Suite}
use zkc::fields::{Fr}
pub module Merlin3Bls12381: Suite = primitive(\"suite.merlin3.bls12-381.fr64be/0\")
pub module InSource: Suite:
    type Challenge = Fr
")]

/-- A program in memory with a scheme over a protocol: the header, then the protocol and the
scheme given. -/
def schemeProgram (body : String) : String := "module t
use zkc::fields::{Fr, G1}
use zkc::suites::{Merlin3Bls12381, InSource}
" ++ body

def schnorrSource : String := "
pub protocol Schnorr<G: PrimeOrderGroup> roles(P, V)(
    base: G @(P, V),
    point: G @(P, V),
    scalar: G::Scalar @P
):
    nonce @P <- sample G::Scalar
    commitment <- send base * nonce to V
    challenge <- draw G::Scalar from V to P
    response <- send nonce + challenge * scalar to V
    guard @V base * response == commitment + point * challenge
"

/-- The schemes of a program in memory, after its names, instances and bodies are accepted. -/
def checkSchemeProgram (label : String) (text : String) : TestM (Option SchemeCheck) := do
  let input : SourceInput := { name := label, parsed := parseString label text }
  let nameCheck := Id.run (checkNames #[input] (memoryLoader schemeLibrary))
  if let some first := nameCheck.refusals[0]? then
    failure s!"{label}: the names do not resolve: {first.render}"
    return none
  let check := checkTyping (checkInstances nameCheck #[label]) #[label]
  if let some first := check.refusals[0]? then
    failure s!"{label}: {first.render}"
    return none
  return some (checkSchemes check)

/-- The scheme of a name in a check of schemes. -/
def findScheme (check : SchemeCheck) (name : String) : Option SchemeReport :=
  check.reports.find? (·.name == name)

def outcomeText : SchemeOutcome → String
  | .constructed _ => "constructed"
  | .refusedByCore reason _ => s!"refused by the core: {reason}"
  | .waiting reason => s!"waiting for {reason}"
  | .refused refusal => s!"refused: {(refusal.toRefusal Renderer.plain).render}"
  | .defect message => s!"not constructed: {message}"
  | .exhausted exhaustion => s!"not checked: {exhaustion.describe}"

/-- A scheme of a program in memory is refused by a rule, with a message that contains a text. -/
def expectSchemeRefused (label body rule text : String) : TestM Unit := do
  let some check ← checkSchemeProgram label (schemeProgram body) | return
  match check.refusals[0]? with
  | some refusal =>
    expectTrue (refusal.rule == rule && (refusal.message.splitOn text).length > 1)
      s!"{label}: refused by {refusal.rule}: {refusal.message}; expected {rule} with `{text}`"
  | none =>
    failure s!"{label}: not refused; {(check.reports.map fun report => outcomeText report.outcome).toList}"

/-- A scheme of a program in memory waits, for a reason that contains a text. -/
def expectSchemeWaits (label body text : String) : TestM Unit := do
  let some check ← checkSchemeProgram label (schemeProgram body) | return
  if let some refusal := check.refusals[0]? then
    failure s!"{label}: refused: {refusal.render}"
    return
  let first : Option SchemeReport := check.reports[0]?
  match first with
  | some { outcome := .waiting reason, .. } =>
    expectTrue ((reason.splitOn text).length > 1) s!"{label}: waits for {reason}; expected `{text}`"
  | some report => failure s!"{label}: {outcomeText report.outcome}"
  | none => failure s!"{label}: no scheme"

/-- The statement `(G, s·G)`. -/
def schnorrStatement (s : Nat) : List Datum :=
  [Datum.ofPoint Zkc.Core.Concrete.generator, Datum.ofPoint (Zkc.Core.Concrete.scalePoint Zkc.Core.Concrete.generator s)]

/-- The completed result of one scheme of a check, as the tool proves and verifies it: no error
reported, no check incomplete, and the scheme constructed, its constructed program admitted and
projected; or a failure that says what is missing. -/
def completeScheme (label : String) (check : SchemeCheck) (name : String) :
    TestM (Option (Completed Constructed)) := do
  match (check.session.admitSchemes (some #[name])).complete with
  | .ok completed => return some completed
  | .error missing =>
    failure s!"{label}: {name} is not complete: {"; ".intercalate missing.toList}"
    return none

/-- How a verifier's run on a proof ends, as a test reads it: accepted, stopped with a reason, or
not run. -/
def verdict (completed : Completed Constructed) (name : String) (statement : List Datum)
    (proof : List Nat) : Except String (Zkc.Core.Execute.Outcome (List Datum)) :=
  completed.verify name statement proof

def isAccepted : Except String (Zkc.Core.Execute.Outcome (List Datum)) → Bool
  | .ok (.returned _) => true
  | _ => false

/-- The verifier on the proof with each byte changed, on each proper prefix and on the proof with
one more byte, the statement validated once: none is accepted, and each stops the verifier with
a reason other than `undefined`. The number of runs. -/
def expectProofsRefused (label : String) (completed : Completed Constructed) (name : String)
    (statement : List Datum) (proof : List Nat) : TestM Nat := do
  let verifier ← match completed.verifier name statement with
    | .ok verifier => pure verifier
    | .error message => do failure s!"{label}: the statement is not taken: {message}"; return 0
  let mut runs := 0
  let variants : List (String × List Nat) :=
    ((List.range proof.length).map fun index =>
      (s!"byte {index} changed", proof.take index ++ [(proof.getD index 0 + 1) % 256] ++ proof.drop (index + 1))) ++
    ((List.range proof.length).map fun length => (s!"the prefix of {length} bytes", proof.take length)) ++
    [("one more byte", proof ++ [0])]
  for (what, bytes) in variants do
    runs := runs + 1
    match verifier.verify bytes with
    | .ok (.stopped reason) =>
      expectTrue (reason != .undefined) s!"{label}: the proof with {what} stops the verifier `undefined`"
    | .ok (.returned _) => failure s!"{label}: the proof with {what} is accepted"
    | .ok other => failure s!"{label}: the proof with {what}: {describeRole other}"
    | .error message => failure s!"{label}: the proof with {what} is not run: {message}"
  return runs

/-! ### The programs of the scheme tests -/

def derivedProgram : String := schnorrSource ++ "
scheme Proof = Schnorr<G1>:
    construction derived(Merlin3Bls12381)
"

def bothSendProgram : String := "
protocol Echo roles(P, V)(x: Fr @P, y: Fr @V):
    a <- send x to V
    b <- send y to P
scheme S = Echo:
    construction derived(Merlin3Bls12381)
"

def senderDrawsProgram : String := "
protocol SendDraw roles(P, V)(x: Fr @P):
    a <- send x to V
    c <- draw Fr from P to V
scheme S = SendDraw:
    construction derived(Merlin3Bls12381)
"

def contradictingProgram : String := schnorrSource ++ "
scheme S = Schnorr<G1>:
    prover V
    construction derived(Merlin3Bls12381)
"

def threeRolesProgram : String := "
protocol Three roles(P, V, W)(x: Fr @P):
    a <- send x to V
scheme S = Three:
    construction derived(Merlin3Bls12381)
"

def quietProgram : String := "
protocol Quiet roles(P, V)(x: Fr @(P, V)):
    guard @V x == x
scheme S = Quiet:
    construction derived(Merlin3Bls12381)
"

def quietProverProgram : String := "
protocol Quiet roles(P, V)(x: Fr @(P, V)):
    guard @V x == x
scheme S = Quiet:
    prover P
    construction derived(Merlin3Bls12381)
"

def aloneProgram : String := "
protocol Alone roles(P, V)(x: Fr @P, y: Fr @V):
    a <- send x to V
    guard @V a == y
scheme S = Alone:
    construction derived(Merlin3Bls12381)
"

def drawGroupProgram : String := "
protocol DrawGroup roles(P, V)(x: Fr @P):
    a <- send x to V
    c <- draw G1 from V to P
scheme S = DrawGroup:
    construction derived(Merlin3Bls12381)
"

def drawBoolProgram : String := "
protocol DrawBool roles(P, V)(x: Fr @P):
    a <- send x to V
    c <- draw bool from V to P
scheme S = DrawBool:
    construction derived(Merlin3Bls12381)
"

def contextProgram : String := schnorrSource ++ "
scheme S = Schnorr<G1>:
    context message: [byte]
    construction derived(Merlin3Bls12381)
"

def inSourceProgram : String := schnorrSource ++ "
scheme S = Schnorr<G1>:
    construction derived(InSource)
"

def interactiveProgram : String := schnorrSource ++ "
scheme S = Schnorr<G1>:
    construction interactive
"

def schemeSuite : TestM Unit := do
  -- the derived Schnorr scheme in memory
  if let some check ← checkSchemeProgram "derived" (schemeProgram derivedProgram) then
    match findScheme check "Proof" with
    | some { outcome := .constructed scheme, .. } =>
      expectTrue (scheme.projected matches .ok 2) "derived: the constructed program is not projected"
      expectTrue (scheme.roles[scheme.prover]? == some "P" && scheme.roles[scheme.verifier]? == some "V")
        "derived: the prover is not P, or the verifier is not V"
      expectTrue (scheme.statement == #[0, 1] && scheme.witness == #[2])
        s!"derived: the statement is {scheme.statement}, the witness {scheme.witness}"
      if let some completed ← completeScheme "derived" check "Proof" then
        match completed.prove "Proof" (schnorrStatement 5) [.number 5] with
        | .ok proof =>
          expectTrue (proof.length == 80) s!"derived: a proof of {proof.length} bytes"
          expectTrue (isAccepted (verdict completed "Proof" (schnorrStatement 5) proof))
            "derived: the honest proof is not accepted"
          expectTrue (!isAccepted (verdict completed "Proof" (schnorrStatement 6) proof))
            "derived: the proof is accepted for another statement"
        | .error message => failure s!"derived: no proof: {message}"
    | some report => failure s!"derived: {outcomeText report.outcome}"
    | none => failure "derived: no scheme Proof"
  -- the rules of the prover and the verifier (SC3)
  expectSchemeRefused "both send" bothSendProgram "SC3" "only the prover sends"
  expectSchemeRefused "the sender draws" senderDrawsProgram "SC3"
    "the role that sends is the prover and the role that draws is the verifier"
  expectSchemeRefused "a contradicting prover line" contradictingProgram "SC3" "contradicts the protocol"
  expectSchemeRefused "three online roles" threeRolesProgram "SC3" "exactly two roles are online"
  expectSchemeRefused "neither sends nor draws" quietProgram "SC3" "write `prover P`"
  -- the statement (SC4)
  expectSchemeRefused "an input of the verifier alone" aloneProgram "SC4" "is held by V alone"
  -- the laws drawn (SC5)
  expectSchemeRefused "a draw of a group" drawGroupProgram "SC5" "decodes its challenge field"
  expectSchemeWaits "a draw of bool" drawBoolProgram "the decoders of the suite"
  -- what waits
  expectSchemeWaits "a context line" contextProgram "`context` line"
  expectSchemeWaits "a suite in source" inSourceProgram "written in source"
  expectSchemeWaits "an interactive construction" interactiveProgram "`interactive`"
  -- a scheme whose roles neither send nor draw, with its prover written
  if let some check ← checkSchemeProgram "quiet" (schemeProgram quietProverProgram) then
    match findScheme check "S" with
    | some { outcome := .constructed _, .. } =>
      if let some completed ← completeScheme "quiet" check "S" then
        match completed.prove "S" [.number 3] [] with
        | .ok proof =>
          expectTrue proof.isEmpty s!"quiet: a proof of {proof.length} bytes"
          expectTrue (isAccepted (verdict completed "S" [.number 3] proof))
            "quiet: the empty proof is not accepted"
          expectTrue (!isAccepted (verdict completed "S" [.number 3] [0]))
            "quiet: a proof of one byte is accepted"
        | .error message => failure s!"quiet: no proof: {message}"
    | some report => failure s!"quiet: {outcomeText report.outcome}"
    | none => failure "quiet: no scheme"

/-! ## The derived Schnorr scheme of the reference -/

/-- A fixed nonce for the comparison of whole proofs, of no other meaning. -/
def fixedNonce : Nat := 0x6b1a34d0f1e2c3b4a5968778695a4b3c2d1e0f00112233445566778899aabbcc

/-- The proof identity of `scheme Proof = Schnorr<G1>` as this frontend emits it, and the proof for
the statement `(G, 7·G)`, the witness 7 and the nonce `fixedNonce`, as the independent replay
computes it: the commitment compressed, then the response in 32 bytes, least significant first.
Both change when the emitted package or declaration changes. -/
def expectedIdentity : String := "469f7f83fc0a89026c989a6215b6f78d1d591612f76339c222dc26bf3889b916"
def expectedProof : String :=
  "8b184d6db8f4acee23c5313a2dd693139f84632c254dbeb2d45fca042ef64cb42679076ed3230b71b4784dd8d3d5192c" ++
  "7ed36654d912be4ed32dfab0f5edbf0ea059cfc3389151f2f7e6555696adbb35"

/-- The suite's rows that a role applies in the entry of a constructed program, in order, each
with the label written before it: `start`, `absorb` and `derive`. -/
partial def suiteSchedule (package : Zkc.Core.Raw.Package) (role : Nat) : List (String × List Nat) :=
  let names := package.operations.map (·.identity.name.toString)
  let rec walk : Zkc.Core.Raw.ProtocolRegion → Option (List Nat) → List (String × List Nat)
    | .step (.at owner (.literal (.nominal _ data))) next, label =>
      if owner == role then walk next (some data) else walk next label
    | .step (.at owner (.op row _)) next, label =>
      let name := names.getD row ""
      let member := (name.splitOn "/0.").getLast?.getD ""
      if owner == role && (member == "start" || member == "absorb" || member == "derive") then
        (member, label.getD []) :: walk next none
      else walk next label
    | .step _ next, label => walk next label
    | .block _ body next, label => walk body label ++ walk next none
    | _, _ => []
  match package.protocols.getLast? with
  | some entry => walk entry.body none
  | none => []

/-- The proof that `scripts/replay_derived_schnorr.py` computes; an error with the reason when
`python3` does not run it. -/
def replayProof (identity : String) (nonce : Nat) : IO (Except String String) := do
  let script : System.FilePath := "scripts" / "replay_derived_schnorr.py"
  unless ← script.pathExists do return .error s!"{script} is not found from the working directory"
  try
    -- whether Python runs at all: a process that cannot be started exits with 255
    let probe ← IO.Process.output { cmd := "python3", args := #["-I", "-c", "pass"] }
    if probe.exitCode != 0 then return .error s!"python3 does not run: {probe.stderr.trimAscii}"
    let output ← IO.Process.output { cmd := "python3", args := #["-I", script.toString, "--identity", identity,
      "--base", "1", "--point", "7", "--witness", "7", "--nonce", toString nonce] }
    if output.exitCode != 0 then return .ok s!"exit {output.exitCode}: {output.stderr.trimAscii}"
    return .ok output.stdout.trimAscii.toString
  catch error => return .error s!"python3 does not run: {error}"

def derivedSchnorrSuite (repository : Repository) : TestM Unit := do
  let load ← cachedLoader #[repository.libraries, repository.examples, repository.examples / "support"]
  let path := repository.examples / "schnorr_example.zkc"
  let input : SourceInput := { name := path.toString, parsed := parseString path.toString (← IO.FS.readFile path) }
  let nameCheck ← checkNames #[input] fun names => (load names : IO _)
  if let some first := nameCheck.refusals[0]? then
    failure s!"schnorr_example: the names do not resolve: {first.render}"
    return
  let check := checkTyping (checkInstances nameCheck #[path.toString]) #[path.toString]
  if let some first := check.refusals[0]? then
    failure s!"schnorr_example: {first.render}"
    return
  let schemes := checkSchemes check
  if let some first := schemes.refusals[0]? then
    failure s!"schnorr_example: {first.render}"
    return
  -- the scheme `Signature` waits for its lines
  match findScheme schemes "Signature" with
  | some { outcome := .waiting _, .. } => pass
  | some report => failure s!"schnorr_example: Signature: {outcomeText report.outcome}"
  | none => failure "schnorr_example: no scheme Signature"
  let some { outcome := .constructed scheme, .. } := findScheme schemes "Proof"
    | failure s!"schnorr_example: Proof is not constructed: {((findScheme schemes "Proof").map fun report => outcomeText report.outcome).getD "no scheme"}"
  -- admitted and projected
  expectTrue (scheme.projected matches .ok 2) "schnorr_example: the constructed program is not projected"
  -- the declaration prints and reads back
  let printed := (Zkc.Core.Raw.printDeclaration scheme.declaration).render
  match Zkc.Core.Raw.parseDeclaration printed with
  | .ok again =>
    expectTrue ((Zkc.Core.Raw.printDeclaration again).render == printed) "schnorr_example: the declaration does not read back"
  | .error message => failure s!"schnorr_example: the printed declaration does not read: {message}"
  -- the schedule of each role: the start from the identity, the statement at positions 0 and 1,
  -- the commitment (site 1), the challenge (site 2) and the response (site 3) of definition 0,
  -- with the transcript roles P = 0 and V = 1
  let identity := Zkc.Core.Concrete.hex scheme.identity
  expectTrue (identity == expectedIdentity) s!"schnorr_example: the proof identity is {identity}"
  let schedule : List (String × List Nat) := [("start", scheme.identity), ("absorb", [0, 0]), ("absorb", [0, 1]),
    ("absorb", [1, 0, 1, 0, 1]), ("derive", [1, 0, 2, 0, 1]), ("absorb", [1, 0, 3, 0, 1])]
  for role in [scheme.prover, scheme.verifier] do
    let found := suiteSchedule scheme.constructed role
    expectTrue (found == schedule) s!"schnorr_example: the schedule of {scheme.roles.getD role "?"} is {found}"
  -- the proof for a fixed nonce
  let statement := schnorrStatement 7
  let some completed ← completeScheme "schnorr_example" schemes "Proof" | return
  match completed.prove "Proof" statement [.number 7] (law := some fun _ _ => .number fixedNonce) with
  | .error message => failure s!"schnorr_example: no proof: {message}"
  | .ok proof =>
    let hex := Zkc.Core.Concrete.hex proof
    expectTrue (hex == expectedProof) s!"schnorr_example: the proof for the fixed nonce is {hex}"
    match ← replayProof identity fixedNonce with
    | .ok replayed =>
      expectTrue (replayed == hex) s!"schnorr_example: the independent replay gives {replayed}"
      if replayed == hex then note "the independent replay of the derived Schnorr proof gives the same bytes"
    | .error reason => failure s!"the independent replay of the derived Schnorr proof did not run: {reason}"
    expectTrue (isAccepted (verdict completed "Proof" statement proof))
      "schnorr_example: the honest proof is not accepted"
    let runs ← expectProofsRefused "schnorr_example" completed "Proof" statement proof
    note s!"derived Schnorr: a proof of {proof.length} bytes; {runs} changed, shortened and extended proofs, none accepted"
  -- a proof from the sampler's seed, and one for a wrong witness
  match completed.prove "Proof" statement [.number 7] [3] with
  | .ok proof =>
    expectTrue (isAccepted (verdict completed "Proof" statement proof))
      "schnorr_example: the proof of seed 3 is not accepted"
  | .error message => failure s!"schnorr_example: no proof from the seed: {message}"
  match completed.prove "Proof" statement [.number 8] [3] with
  | .ok proof =>
    expectTrue (!isAccepted (verdict completed "Proof" statement proof))
      "schnorr_example: a proof for a wrong witness is accepted"
  | .error message => failure s!"schnorr_example: no proof for a wrong witness: {message}"

/-- The proof of a constructed scheme on a statement and a witness, accepted; with the statement
changed (when given) and with its first and last byte changed, not accepted, and no run stopping
`undefined`. -/
def expectSchemeRuns (label : String) (completed : Completed Constructed) (name : String)
    (statement witness : List Datum) (otherStatement : Option (List Datum)) : TestM Unit := do
  let verifier ← match completed.verifier name statement with
    | .ok verifier => pure verifier
    | .error message => do failure s!"{label}: the statement is not taken: {message}"; return
  match completed.prove name statement witness [4] with
  | .error message => failure s!"{label}: no proof: {message}"
  | .ok proof =>
    expectTrue (isAccepted (verifier.verify proof))
      s!"{label}: the honest proof is not accepted"
    if let some other := otherStatement then
      expectTrue (!isAccepted (verdict completed name other proof))
        s!"{label}: the proof is accepted for another statement"
    for index in [0, proof.length - 1] do
      let changed := proof.take index ++ [(proof.getD index 0 + 1) % 256] ++ proof.drop (index + 1)
      match verifier.verify changed with
      | .ok (.stopped reason) => expectTrue (reason != .undefined) s!"{label}: byte {index} changed stops `undefined`"
      | other => failure s!"{label}: the proof with byte {index} changed: {match other with
          | .ok outcome => describeRole outcome | .error message => message}"
    note s!"{label}: a proof of {proof.length} bytes, accepted; changed, not accepted"

/-- The schemes of the programs of the reference: each constructed program is admitted and
projected, and the rest wait; none is refused. The derived OR proof and the derived Sumcheck
proof run. -/
def referenceSchemeSuite (repository : Repository) : TestM Unit := do
  let load ← cachedLoader #[repository.libraries, repository.examples, repository.examples / "support"]
  let mut constructed : Array String := #[]
  let mut notCopies : Array String := #[]
  let mut waiting := 0
  for stem in ["schnorr_example", "sumcheck_example", "gkr_example", "variants_example", "chaum_pedersen",
      "fragments", "inner_product", "fri_example", "spot_check", "product_check_example", "mldsa_signature"] do
    let path := repository.examples / s!"{stem}.zkc"
    let input : SourceInput := { name := path.toString, parsed := parseString path.toString (← IO.FS.readFile path) }
    let nameCheck ← checkNames #[input] fun names => (load names : IO _)
    if let some first := nameCheck.refusals[0]? then
      failure s!"{stem}: the names do not resolve: {first.render}"
      continue
    let check := checkTyping (checkInstances nameCheck #[path.toString]) #[path.toString]
    let schemes := checkSchemes check
    if let some first := schemes.refusals[0]? then failure s!"{stem}: {first.render}"
    for report in schemes.reports do
      match report.outcome with
      | .constructed scheme =>
        constructed := constructed.push report.description
        expectTrue (scheme.projected matches .ok 2) s!"{stem}: {report.description} is not projected"
        -- What the Fiat–Shamir step returns is admitted without the check of copies. Whether it
        -- would pass that check is recorded here: the step threads the prover's and the
        -- verifier's transcript states without declaring them copies of one value.
        let passesCopies := match Zkc.Core.elaborate scheme.construction.derivedAdmitted.package with
          | .ok typed => typed.program.protocols.coherent
          | .error _ => false
        unless passesCopies do notCopies := notCopies.push report.description
        let point (s : Nat) : Datum := Datum.ofPoint (Zkc.Core.Concrete.scalePoint Zkc.Core.Concrete.generator s)
        if report.description == "scheme OrProof = Or<G1>" then
          let some completed ← completeScheme stem schemes report.name | continue
          -- the prover knows the logarithm 13 of x0; x1 is 5·G
          expectSchemeRuns report.description completed report.name [point 1, point 13, point 5]
            [.sequence [.number 0, .number 13]] (some [point 1, point 13, point 6])
          let wrong := completed.prove report.name [point 1, point 13, point 5]
            [.sequence [.number 1, .number 13]] [4]
          let refused := match wrong with
            | .ok proof => !isAccepted (verdict completed report.name [point 1, point 13, point 5] proof)
            | .error _ => false
          expectTrue refused s!"{report.description}: a proof with a wrong witness is accepted, or none is made"
        if report.description == "scheme Proof = Sumcheck<Fr, 10>" then
          let some completed ← completeScheme stem schemes report.name | continue
          let values := (List.range (2 ^ 10)).map fun i => (i * i + 3 * i + 7) % fr
          let claim := values.foldl (· + ·) 0 % fr
          expectSchemeRuns report.description completed report.name [numbers values, .number claim] []
            (some [numbers values, .number ((claim + 1) % fr)])
      | .waiting _ => waiting := waiting + 1
      | other => failure s!"{stem}: {report.description}: {outcomeText other}"
  note s!"schemes of examples/: {constructed.size} constructed and admitted ({", ".intercalate constructed.toList}), {waiting} waiting"
  -- A known defect of the step: a callee that derives a coin at both roles and returns it under
  -- an agreement. When the step declares its threaded states copies, this list becomes empty.
  expectTrue (notCopies == #["scheme Proof = Sumcheck<Fr, 10>"])
    s!"what the Fiat–Shamir step returns does not pass the check of copies for {notCopies.toList}; expected for the derived Sumcheck only"
  note s!"  after the Fiat–Shamir step the check of copies would refuse: {", ".intercalate notCopies.toList}"

end Zkc.Tests.Frontend
