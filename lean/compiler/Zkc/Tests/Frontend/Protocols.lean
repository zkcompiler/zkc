import Zkc.Tests.Frontend.ProtocolCases
import Zkc.Tests.Frontend.Running

/-!
# Protocol bodies

- Without the reference: the programs of `ProtocolCases`; and protocols typed, emitted, admitted,
  projected and run by the core's executor: interactive Schnorr over `bls12-381.g1`, honest and
  with each message changed, all roles together and the verifier alone against messages given to
  it; a loop with a run-time count, a loop that collects, a choice on a condition, a choice on an
  alternative, a stepped loop.
- With the reference: interactive Schnorr of `examples/schnorr.zkc` at BLS12-381's G1 and the
  Chaum–Pedersen protocol of `examples/chaum_pedersen.zkc` at the instance its scheme names, run
  the same way; the OR proof of `examples/sigma_or.zkc` at G1 with each alternative of its
  witness, with a wrong witness and with its commitments changed; `Sumcheck<n>` of `examples/sumcheck.zkc` over `bls12-381.fr` and `koala-bear` at
  the sizes 0, 1, 2, 3 and 10, honest with the claim that the test computes, with a false claim,
  and with the first round message or challenge changed on the way.

No run of a role stops `undefined` or `incomplete`, reaches the limit of the run, or fails to
run; a role whose peer stopped waits for a message that is never sent.
-/

namespace Zkc.Tests.Frontend

open Zkc.Frontend
open Zkc.Frontend.Syntax
open Zkc.Core.Concrete (Datum)

def protocolCaseSuite : TestM Unit := do
  let blocks := readBlocks protocolCases
  let mut roots := 0
  for block in blocks do
    checkTypingBlock block
    if let .ok (check, _) := typeBlock block then roots := roots + (checkedProtocols check).1
  note s!"{blocks.size} programs for the typing of protocol bodies; {roots} packages of protocol roots admitted with the check of facts of their protocols"

/-- The root of a check by its description, written as the tool writes it, with or without the
words of a default instance. -/
def findRoot (check : TypingCheck) (root : String) : Option PackageReport :=
  check.packages.find? fun report =>
    report.description == root || report.description == s!"default instance `{root}`"

/-- How a role of a run ends, as a test states it: `blocked` when it waits for a message that no
role sends, because a peer stopped. -/
inductive RoleExpected where
  | returned (outputs : List Datum)
  | stopped (reason : PIR.Stop)
  | blocked

/-- Whether a role failed because it waits for a message that is never sent. The core's outcome
says so in the message of a failure only. -/
def waitsForever : Zkc.Core.Execute.Outcome (List Datum) → Bool
  | .failed message => message == "waits for a message that is never sent"
  | _ => false

def RoleExpected.matches : RoleExpected → Zkc.Core.Execute.Outcome (List Datum) → Bool
  | .returned outputs, .returned found => outputs == found
  | .stopped reason, .stopped found => reason == found
  | .blocked, outcome => waitsForever outcome
  | _, _ => false

/-- How a role of a run ends, as a line. -/
def describeRole (outcome : Zkc.Core.Execute.Outcome (List Datum)) : String :=
  outcome.describe reprStr

/-- The protocol of a root of a check, with its inputs validated once; or a failure that says
why it does not run. -/
def protocolInputs (label : String) (check : TypingCheck) (root : String) (inputs : List Datum) :
    TestM (Option ProtocolInputs) := do
  match completeRoot check root with
  | .error missing =>
    failure s!"{label}: {root} is not run: {missing}"
    return none
  | .ok completed =>
    match completed.protocolInputs root inputs with
    | .ok prepared => return some prepared
    | .error message =>
      failure s!"{label}: {root} does not run: {message}"
      return none

/-- Runs a protocol on inputs validated once and compares the outcome of each role named; a role
that stops `undefined` or `incomplete`, reaches the limit, or does not run fails. A role that
waits for a message that is never sent, because a peer stopped, does not run to its end, and is
no failure by itself. -/
def expectRunOn (label root : String) (prepared : ProtocolInputs)
    (expected : List (String × RoleExpected)) (seed : List Nat := [1])
    (selected : Option (List Nat) := none) (messages : Messages := [])
    (change : Option Running.Change := none) : TestM Unit := do
  match prepared.run seed selected messages change with
  | .error message => failure s!"{label}: {root} does not run: {message}"
  | .ok runs =>
    for run in runs do
      match run.outcome with
      | .stopped .undefined | .stopped .incomplete | .limit _ =>
        failure s!"{label}: {root}: {run.role} {describeRole run.outcome}"
      | .failed message =>
        unless waitsForever run.outcome do
          failure s!"{label}: {root}: {run.role} does not run: {message}"
      | _ => pure ()
    for (role, expectation) in expected do
      match runs.find? (·.role == role) with
      | none => failure s!"{label}: {root} has no run of {role}"
      | some run =>
        expectTrue (expectation.matches run.outcome)
          s!"{label}: {root}: {role} {describeRole run.outcome}"

/-- Runs a protocol root on inputs and compares the outcome of each role named: see
`expectRunOn`. -/
def expectProtocolRun (label : String) (check : TypingCheck) (root : String) (inputs : List Datum)
    (expected : List (String × RoleExpected)) (seed : List Nat := [1])
    (selected : Option (List Nat) := none) (messages : Messages := [])
    (change : Option Running.Change := none) : TestM Unit := do
  let some prepared ← protocolInputs label check root inputs | return
  expectRunOn label root prepared expected seed selected messages change

def protocolProgram : String := "module running
type G = primitive(\"bls12-381.g1\")
type F = primitive(\"bls12-381.fr\")
def multiple(g: G, s: F) -> G: g * s
protocol Schnorr roles(P, V)(base: G @(P, V), point: G @(P, V), scalar: G::Scalar @P):
    nonce @P <- sample G::Scalar
    commitment <- send base * nonce to V
    challenge <- draw G::Scalar from V to P
    response <- send nonce + challenge * scalar to V
    guard @V base * response == commitment + point * challenge
protocol Counted roles(P, V)(n: index<4> @(P, V), a: F @P) -> total: F @V:
    mut s: F @V = 0
    for i in 0..n:
        m <- send a to V
        s := s + m
    return s
protocol Collected roles(P, V)(a: F @P) -> last: F @V:
    mut s = a
    for i in 0..3 collect (sent = m):
        m <- send s to V
        s := s + 1
    return sent[2]
protocol Chosen roles(P, V)(b: bool @(P, V), a: F @P) -> got: F @V:
    mut got: F @V = 0
    if b:
        m <- send a to V
        got := m
    return got
enum Choice:
    Add(F)
    Keep
protocol Matched roles(P, V)(e: Choice @(P, V), a: F @P) -> got: F @V:
    mut got: F @V = 0
    match e:
        case Choice::Add(x):
            m <- send a + x to V
            got := m
        case Choice::Keep:
            ()
    return got
protocol Drawn roles(P, V)() -> got: (bool, [nonzero<F>; 3]) @(P, V):
    c <- draw (bool, [nonzero<F>; 3]) from V to P
    return c
type E = primitive(\"koala-bear.ext4\")
protocol UnitOfExtension roles(P, V)() -> value: nonzero<E> @P:
    unit @P <- sample nonzero<E>
    return unit
protocol Doubling roles(P, V)(a: [F; 1] @P) -> last: [F; 4] @V:
    mut s = a
    for i in 0..3 collect (sent = m):
        m <- send s to V
        s := s ++ s
    return sent.2
"

/-- The program of the protocols run without the reference, typed. -/
def protocolCheck : TestM (Option TypingCheck) := do
  let input : SourceInput := { name := "running", parsed := parseString "running" protocolProgram }
  let nameCheck := Id.run (checkNames #[input] (memoryLoader nameLibrary))
  if let some first := nameCheck.refusals[0]? then
    failure s!"protocols: the names do not resolve: {first.render}"
    return none
  let check := checkTyping (checkInstances nameCheck #["running"]) #["running"]
  if let some first := check.refusals[0]? then
    failure s!"protocols: {first.render}"
    return none
  checkPackages "protocols" check
  return some check

/-- `s` times the generator of G1, from the function `multiple` of the program. -/
def generatorMultiple (check : TypingCheck) (s : Nat) : Option Datum := do
  let completed ← (completeRoot check "multiple").toOption
  match completed.runFunction "multiple" [numbers [generatorX, generatorY], .number s] with
  | .returned [point] => some point
  | _ => none

/-- Interactive Schnorr, at a root of a check whose protocol is the package's only protocol:
the honest run returns at both roles; with the commitment, the challenge or the response changed
the verifier stops `reject`; the verifier alone accepts the messages of an honest prover and
refuses a wrong response; a wrong scalar is refused. The sites are those of the text: the sample
is 0, the commitment 1, the challenge 2, the response 3. -/
def schnorrRuns (label : String) (check : TypingCheck) (root : String) (points : TypingCheck) :
    TestM Unit := do
  let base := numbers [generatorX, generatorY]
  let scalar := 7
  let some point := generatorMultiple points scalar
    | failure s!"{label}: no multiple of the generator"
  let inputs := [base, point, .number scalar]
  let accepted : List (String × RoleExpected) := [("P", .returned []), ("V", .returned [])]
  let rejected : List (String × RoleExpected) := [("P", .returned []), ("V", .stopped .reject)]
  -- the inputs validated once, for every run on them
  let some prepared ← protocolInputs label check root inputs | return
  expectRunOn label root prepared accepted
  expectRunOn s!"{label}, another seed" root prepared accepted (seed := [2, 3])
  -- a scalar that is not the logarithm of the point
  expectProtocolRun s!"{label}, a wrong scalar" check root [base, point, .number (scalar + 1)] rejected
  -- each message changed on the way: a point for the commitment, one more for the scalars
  let plusOne : Datum → Datum := fun datum => .number ((datum.toNat + 1) % fr)
  expectRunOn s!"{label}, the commitment changed" root prepared rejected
    (change := some { site := 1, change := fun _ => base })
  expectRunOn s!"{label}, the challenge changed" root prepared rejected
    (change := some { site := 2, change := plusOne })
  expectRunOn s!"{label}, the response changed" root prepared rejected
    (change := some { site := 3, change := plusOne })
  -- the verifier alone, against the messages of a prover whose nonce is 5
  let nonce := 5
  let some commitment := generatorMultiple points nonce
    | failure s!"{label}: no multiple of the generator"
  let seed := [4]
  let challenge := (Zkc.Core.Execute.coin seed { path := [], definition := 0, number := 2 } 0).toNat
  let response := (nonce + challenge * scalar) % fr
  expectRunOn s!"{label}, the verifier alone" root prepared [("V", .returned [])]
    (seed := seed) (selected := some [1]) (messages := [(1, commitment), (3, .number response)])
  expectRunOn s!"{label}, the verifier alone, a wrong response" root prepared
    [("V", .stopped .reject)] (seed := seed) (selected := some [1])
    (messages := [(1, commitment), (3, .number ((response + 1) % fr))])

def protocolRunSuite : TestM Unit := do
  let some check ← protocolCheck | return
  let label := "protocols"
  schnorrRuns label check "Schnorr" check
  -- a loop with a run-time count: the verifier adds what it receives, once per iteration
  for n in [0, 1, 3] do
    expectProtocolRun label check "Counted" [.number n, .number 5]
      [("P", .returned []), ("V", .returned [.number (5 * n)])]
  -- a loop that collects: the last of three values sent
  expectProtocolRun label check "Collected" [.number 10] [("P", .returned []), ("V", .returned [.number 12])]
  -- a choice of both roles on a condition they both hold
  expectProtocolRun label check "Chosen" [Datum.ofBool true, .number 9]
    [("P", .returned []), ("V", .returned [.number 9])]
  expectProtocolRun label check "Chosen" [Datum.ofBool false, .number 9]
    [("P", .returned []), ("V", .returned [.number 0])]
  -- a choice of both roles on the alternative of a value they both hold
  expectProtocolRun label check "Matched" [.sequence [.number 0, .number 5], .number 9]
    [("P", .returned []), ("V", .returned [.number 14])]
  expectProtocolRun label check "Matched" [.sequence [.number 1, .sequence []], .number 9]
    [("P", .returned []), ("V", .returned [.number 0])]
  -- a stepped loop: its iterations in sequence, each send a site of its own
  expectProtocolRun label check "Doubling" [numbers [7]]
    [("P", .returned []), ("V", .returned [numbers [7, 7, 7, 7]])]
  -- a law that is a tuple with a collection in it: one draw, sampled component by component, the
  -- same value at the owner and the receiver
  let outcome : Except String (Array RoleRun) := do
    (← completeRoot check "Drawn").runProtocol "Drawn" []
  match outcome with
  | .ok runs =>
    let outcomes : List (Zkc.Core.Execute.Outcome (List Datum)) := runs.toList.map (·.outcome)
    match outcomes with
    | [.returned [prover], .returned [verifier]] =>
      let shaped := match verifier with
        | .sequence [flag, .sequence units] =>
          flag.toNat < 2 && units.length == 3 && units.all fun unit => 0 < unit.toNat && unit.toNat < fr
        | _ => false
      expectTrue (prover == verifier && shaped)
        s!"{label}: the draw of a tuple gives {reprStr prover} and {reprStr verifier}"
    | outcomes => failure s!"{label}: the draw of a tuple ends {outcomes.map describeRole}"
  | .error message => failure s!"{label}: the draw of a tuple does not run: {message}"
  -- a sample of the units of an extension is a value of its type: four coefficients of the base
  -- field, not all zero
  for seed in [1, 2, 3] do
    let outcome : Except String (Array RoleRun) := do
      (← completeRoot check "UnitOfExtension").runProtocol "UnitOfExtension" [] (seed := [seed])
    match outcome with
    | .ok runs =>
      let outcomes : List (Zkc.Core.Execute.Outcome (List Datum)) := runs.toList.map (·.outcome)
      match outcomes with
      | [.returned [.sequence coefficients], .returned []] =>
        expectTrue (coefficients.length == 4 && coefficients.all (·.toNat < 2130706433) &&
            coefficients.any (·.toNat != 0))
          s!"{label}: a unit of an extension under the seed {seed} is {reprStr coefficients}"
      | outcomes =>
        failure s!"{label}: a sample of a unit of an extension ends {outcomes.map describeRole}"
    | .error message => failure s!"{label}: a sample of a unit of an extension does not run: {message}"

/-! ## Over the reference -/

/-- A worked program of the reference, typed with the library. -/
def referenceProgram (repository : Repository) (stem : String) : TestM (Option TypingCheck) := do
  let load ← cachedLoader #[repository.libraries]
  let path := repository.examples / s!"{stem}.zkc"
  let input : SourceInput := { name := path.toString, parsed := parseString path.toString (← IO.FS.readFile path) }
  let nameCheck ← checkNames #[input] fun names => (load names : IO _)
  if let some first := nameCheck.refusals[0]? then
    failure s!"{stem}: the names do not resolve: {first.render}"
    return none
  let check := checkTyping (checkInstances nameCheck #[path.toString]) #[path.toString]
  if let some first := check.refusals[0]? then
    failure s!"{stem}: {first.render}"
    return none
  return some check

/-- The definition of a package whose name starts with a prefix, and the core site of a named
site of it. -/
def namedSite (package : Zkc.Core.Raw.Package) (definitionPrefix site : String) : Option (Nat × Nat) := do
  let names ← package.names
  let definition ← names.protocols.findIdx? (·.startsWith definitionPrefix)
  let sites ← names.sites[definition]?
  let number ← sites.findIdx? (· == site)
  return (definition, number)

def referenceProtocolSuite (repository : Repository) : TestM Unit := do
  let some points ← protocolCheck | return
  -- interactive Schnorr at G1, the default instance of the public protocol
  if let some check ← referenceProgram repository "schnorr" then
    match findRoot check "Schnorr<bls12-381.g1>" with
    | some report =>
      expectTrue (report.outcome matches .admitted _)
        s!"schnorr: the package of {report.description} is not admitted"
      schnorrRuns "schnorr" check "Schnorr<bls12-381.g1>" points
    | none => failure s!"schnorr: no root Schnorr<bls12-381.g1>"
  -- Chaum–Pedersen at the instance that its scheme names: u = g * x and v = h * x
  if let some check ← referenceProgram repository "chaum_pedersen" then
    let some report := check.packages.find? (·.description.startsWith "ChaumPedersen")
      | failure "chaum_pedersen: no root of the protocol"
    expectTrue (report.outcome matches .admitted _)
      s!"chaum_pedersen: the package of {report.description} is not admitted"
    let x := 11
    let g := numbers [generatorX, generatorY]
    match generatorMultiple points 3, generatorMultiple points x, generatorMultiple points (3 * x) with
    | some h, some u, some v =>
      let accepted : List (String × RoleExpected) := [("P", .returned []), ("V", .returned [])]
      expectProtocolRun "chaum_pedersen" check report.description [g, h, u, v, .number x] accepted
      expectProtocolRun "chaum_pedersen, another logarithm" check report.description
        [g, h, u, g, .number x] [("P", .returned []), ("V", .stopped .reject)]
    | _, _, _ => failure "chaum_pedersen: no multiple of the generator"
  -- the OR proof of `sigma_or` at G1: an honest run with each alternative of the witness, and
  -- one with the commitments changed on the way
  if let some check ← referenceProgram repository "sigma_or" then
    let root := "Or<bls12-381.g1>"
    let w := 13
    let g := numbers [generatorX, generatorY]
    match generatorMultiple points w, generatorMultiple points 5, findRoot check root with
    | some known, some other, some report =>
      let accepted : List (String × RoleExpected) := [("P", .returned []), ("V", .returned [])]
      -- the prover knows the logarithm of x0, or of x1
      let some left ← protocolInputs "sigma_or" check root
          [g, known, other, .sequence [.number 0, .number w]]
        | return
      expectRunOn "sigma_or, the left alternative" root left accepted
      expectProtocolRun "sigma_or, the right alternative" check root
        [g, other, known, .sequence [.number 1, .number w]] accepted
      -- a witness of neither point
      expectProtocolRun "sigma_or, a wrong witness" check root
        [g, other, other, .sequence [.number 0, .number w]] [("P", .returned []), ("V", .stopped .reject)]
      match report.package?.bind (namedSite · "Or" "commitments") with
      | some (_, site) =>
        expectRunOn "sigma_or, the commitments changed" root left [("V", .stopped .reject)]
          (change := some { site, change := fun
            | .sequence [_, second] => .sequence [g, second]
            | datum => datum })
      | none => failure "sigma_or: no site `commitments`"
    | _, _, _ => failure s!"sigma_or: no root {root}, or no multiple of the generator"

/-! ## Sumcheck over the reference -/

/-- A module that instantiates `Sumcheck` of `examples/sumcheck.zkc` over a field at sizes. -/
def sumcheckWrapper (field path : String) (sizes : List Nat) : String :=
  s!"module sumcheck_runs
use sumcheck<{field}>::\{Sumcheck}
use {path}::\{{field}}
" ++ String.join (sizes.map fun n => s!"// instantiate: Sumcheck<{n}>\n")

/-- `Sumcheck<n>` over a field of order `order`, run on a table of `2^n` values: the honest run
with the true claim, the sum of the table computed here, returns at both roles; a false claim and
the first round message changed on the way stop the verifier `reject`; so does the first challenge
changed on the way to the prover, except in a run of one round, where no message of the prover
follows it. -/
def sumcheckRuns (label : String) (check : TypingCheck) (fieldName : String) (order n : Nat) :
    TestM Unit := do
  let root := s!"Sumcheck<{fieldName}, {n}>"
  let some report := findRoot check root
    | failure s!"{label}: no root {root}; the roots are {check.packages.map (·.description)}"
  let some package := report.package?
    | failure s!"{label}: {root} is not emitted"
  let values := (List.range (2 ^ n)).map fun i => (i * i + 3 * i + 7) % order
  let claim := values.foldl (· + ·) 0 % order
  let inputs := [numbers values, .number claim]
  let label := s!"{label}, {root}"
  let some prepared ← protocolInputs label check root inputs | return
  -- the honest run, under two seeds
  expectRunOn label root prepared [("P", .returned []), ("V", .returned [])]
  expectRunOn s!"{label}, another seed" root prepared [("P", .returned []), ("V", .returned [])]
    (seed := [5, 6])
  -- a false claim
  let falseClaim := [numbers values, .number ((claim + 1) % order)]
  expectProtocolRun s!"{label}, a false claim" check root falseClaim [("V", .stopped .reject)]
  if n == 0 then return
  -- the round message of the first round, and the challenge of the first round, changed: the
  -- sites of `Reduce` under the application of `Sumcheck` at its site 0
  let some (definition, roundSite) := namedSite package "Reduce" "round.0"
    | failure s!"{label}: no site `round.0` of `Reduce`"
  let some (_, challengeSite) := namedSite package "Reduce" "challenge.0"
    | failure s!"{label}: no site `challenge.0` of `Reduce`"
  let plusOne : Datum → Datum := fun
    | .sequence (first :: rest) => .sequence (.number ((first.toNat + 1) % order) :: rest)
    | datum => .number ((datum.toNat + 1) % order)
  expectRunOn s!"{label}, the first round message changed" root prepared [("V", .stopped .reject)]
    (change := some { site := roundSite, change := plusOne, definition := some definition, path := [0] })
  -- a challenge reaches the prover only; when it is the last, no message of the prover follows it,
  -- and the verifier, which reads its own copy, accepts
  let afterChallenge : RoleExpected := if n == 1 then .returned [] else .stopped .reject
  expectRunOn s!"{label}, the first challenge changed" root prepared [("V", afterChallenge)]
    (change := some { site := challengeSite, change := plusOne, definition := some definition, path := [0] })

/-- The sizes at which `Sumcheck` runs in the tests. -/
def sumcheckSizes : List Nat := [0, 1, 2, 3, 10]

def sumcheckRunSuite (repository : Repository) : TestM Unit := do
  let load ← cachedLoader #[repository.libraries, repository.examples]
  for (field, path, name, order) in [("Fr", "zkc::curves::bls12_381", "Fr", fr),
      ("KoalaBear", "zkc::fields", "KoalaBear", koalaBear)] do
    let label := s!"sumcheck over {field}"
    let input : SourceInput :=
      { name := label, parsed := parseString label (sumcheckWrapper field path sumcheckSizes) }
    let nameCheck ← checkNames #[input] fun names => (load names : IO _)
    if let some first := nameCheck.refusals[0]? then
      failure s!"{label}: the names do not resolve: {first.render}"
      continue
    let check := checkTyping (checkInstances nameCheck #[label]) #[label]
    if let some first := check.refusals[0]? then
      failure s!"{label}: {first.render}"
      continue
    checkPackages label check
    for n in sumcheckSizes do sumcheckRuns label check name order n

end Zkc.Tests.Frontend
