import Zkc.Tests.Core.Check
import Zkc.Core.RunComparison
import Zkc.Core.UninterpretedRows
import Zkc.Core.Mutation

/-! Checks of the valid data by type, of the comparison of two packages by runs and of the
mutants of a package, on four packages that the frontend emitted:

- `guarded.json`: a protocol of two roles over `bls12-381.fr`, a send and a guard at both roles;
- `relay.json`: a protocol of three roles, two sends and a guard of the third role;
- `redeem.json`: a function that takes a linear record apart;
- `two_draws.json`: a protocol whose verifier draws two challenges and returns them.

The checks: every draw under seeds 0 to 5 of the types of the inputs of the first three, and of
collections, tuples, variants and records built over them, is a value that validation accepts;
the boundary draws come first; each package compared with itself is alike under five seeds; the
protocol of two draws with the numbers of its two sites exchanged is alike with the original
when the key of each site follows the exchange (as the frontend's table of sites gives it, by
the event of the source), and different when the key is the new number; the
relay with the literal that its second role adds changed is different, and the first seed that
shows it is a boundary draw; the mutants of the two protocols are admitted by the core, those of
the protocol of two roles (its addition replaced by the vocabulary's subtraction and
multiplication) are told apart, and so are some of the relay's (the function, which only takes
a field, has none); a root whose run would be too long is not run. Elsewhere coins are keyed by the
site's numbers in the package, which is enough for a package compared with itself or with a
change of it that keeps its sites. -/

set_option autoImplicit false

open Zkc.Source Zkc.Core Zkc.Core.Vocabulary Zkc.Core.Concrete

namespace RunComparisonChecks

def check (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError s!"run comparison: {label}")

def fail {α : Type} (message : String) : IO α := throw (IO.userError s!"run comparison: {message}")

/-- The order of `bls12-381.fr`. -/
def fr : Nat := 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001

def readPackage (path : String) : IO Raw.Package := do
  match Raw.parsePackage (← IO.FS.readFile path) with
  | .ok package => pure package
  | .error message => fail message

/-- The key of a site by the package's own numbers. -/
def ownKey (site : Site) : Option (List Nat) :=
  some (site.path ++ [site.definition, site.number])

def sideOf (package : Raw.Package) : IO RunComparison.Side :=
  match elaborate package with
  | .ok typed => pure { package, typed, key := ownKey }
  | .error refusal => fail (reprStr refusal)

/-- The types whose draws are checked: the inputs of the newest protocol or function of a
package, and composites of them and of the core's own types. -/
def typesOf (package : Raw.Package) : List Ty :=
  let ports := match package.protocols.getLast?, package.functions.getLast? with
    | some protocol, _ => protocol.inputs.map Located.type
    | none, some function => function.inputs
    | none, none => []
  let field : Ty := .nominal 0
  ports ++ [.bool, .nat, .fin 7, .seq field (some 3), .seq .bool none, .tuple [field, .fin 2],
    .variant 0 [field, .tuple []], .seq (.seq (.fin 3) none) (some 2)]

/-- Whether a draw is a value that validation accepts. -/
def drawValid (types : Array CatalogueRow) (seed : Nat) (type : Ty) : Bool :=
  match ValidData.value table types (.ofSeed seed [7]) type 0 with
  | .ok (datum, _) => validInput table types type datum
  | .error _ => false

def drawsOf (name : String) (package : Raw.Package) : IO Unit := do
  let types := package.types.toArray
  for type in typesOf package do
    for seed in List.range 6 do
      check s!"{name}: the draw of seed {seed} at {reprStr type} is a value" (drawValid types seed type)

def isAlike : RunComparison.Verdict → Bool
  | .agree _ => true
  | _ => false

def isDifferent : RunComparison.Verdict → Bool
  | .differ .. => true
  | _ => false

def isIncomplete : RunComparison.Verdict → Bool
  | .incomplete _ => true
  | _ => false

/-- A protocol of two roles over `bls12-381.fr` with the row of its addition: the first role
holds the input, and nobody returns anything. -/
def silent (body : Raw.ProtocolRegion) : Raw.Package :=
  ⟨[⟨Name.ofString "bls12-381.fr", []⟩], [], [],
    [⟨⟨Name.ofString "field.add", [.type (.nominal 0)]⟩,
      ⟨[.nominal 0, .nominal 0], [.nominal 0], .pure⟩⟩], [],
    [⟨false, 2, [⟨.nominal 0, 0⟩], [], [], body⟩], none⟩

/-- The first role sends its input. -/
def sendsInput : Raw.Package := silent (.step (.exchange 0 1 0 0) (.ret []))

/-- The first role sends its input added to itself. Both roles end as in `sendsInput`. -/
def sendsDouble : Raw.Package :=
  silent (.step (.at 0 (.op 0 [0, 0])) (.step (.exchange 0 1 0 1) (.ret [])))

/-- The text of a package with the sites `a` and `b` of its draws, samples and applications
exchanged: the same protocol, its sites numbered otherwise. -/
partial def exchangeSites (a b : Nat) : Zkc.Json → Zkc.Json
  | .arr items =>
    let position := match items[0]? with
      | some (.str "draw") | some (.str "apply") => some 3
      | some (.str "sample") => some 2
      | _ => none
    let items := items.map (exchangeSites a b)
    let exchange : Zkc.Json → Zkc.Json
      | .num n => .num (if n == a then b else if n == b then a else n)
      | other => other
    .arr (match position with
      | some index => items.modify index exchange
      | none => items)
  | other => other

def renumbered (path : String) (a b : Nat) : IO Raw.Package := do
  match Zkc.Json.parse (← IO.FS.readFile path) with
  | .ok json =>
    match Raw.parsePackage (Zkc.Json.render (exchangeSites a b json)) with
    | .ok package => pure package
    | .error message => fail message
  | .error message => fail message

/-- A package whose functions each start with a loop of 2^21 iterations of nothing. -/
def looped (package : Raw.Package) : Raw.Package :=
  let loopFirst (function : Raw.Function) : Raw.Function :=
    { function with body := function.body.map (.step (.loop (.static (2 ^ 21)) [] [] [] (.ret [])) ·) }
  { package with functions := package.functions.map loopFirst }

#eval show IO Unit from do
  let guarded ← readPackage (package_file "fixtures/differential/guarded.json")
  let relay ← readPackage (package_file "fixtures/differential/relay.json")
  let redeem ← readPackage (package_file "fixtures/differential/redeem.json")
  -- draws
  drawsOf "guarded" guarded
  drawsOf "relay" relay
  drawsOf "redeem" redeem
  let types := guarded.types.toArray
  match ValidData.inputs table types (.ofSeed 2 []) [.nominal 0, .fin 5] with
  | .ok data => check "the third boundary draw is the largest" (data == [.number (fr - 1), .number 4])
  | .error reason => fail reason
  check "index<0> has no draw" (!drawValid types 0 (.fin 0))
  -- comparisons with itself
  let guardedSide ← sideOf guarded
  let relaySide ← sideOf relay
  let seeds := List.range 5
  check "guarded is alike with itself" (isAlike (RunComparison.compareProtocols RunComparison.arithmetic guardedSide guardedSide seeds))
  check "relay is alike with itself" (isAlike (RunComparison.compareProtocols RunComparison.arithmetic relaySide relaySide seeds))
  check "redeem is alike with itself" (isAlike (RunComparison.compareFunctions RunComparison.arithmetic redeem redeem seeds))
  -- the two draws of a protocol with their sites exchanged: alike when the key of a site
  -- follows the exchange, different when it does not
  let twoDraws ← sideOf (← readPackage (package_file "fixtures/differential/two_draws.json"))
  let exchanged ← renumbered (package_file "fixtures/differential/two_draws.json") 0 1
  check "the exchanged package differs in its text"
    (Zkc.Json.render (Raw.printPackage exchanged) != Zkc.Json.render (Raw.printPackage twoDraws.package))
  let back (site : Site) : Site :=
    { site with number := if site.number == 0 then 1 else if site.number == 1 then 0 else site.number }
  let followed : RunComparison.Side :=
    { (← sideOf exchanged) with key := fun site => ownKey (back site) }
  check "two draws renumbered, keyed by the draws, are alike"
    (isAlike (RunComparison.compareProtocols RunComparison.arithmetic twoDraws followed (List.range 16)))
  check "two draws renumbered, keyed by the new numbers, are different"
    (isDifferent (RunComparison.compareProtocols RunComparison.arithmetic twoDraws (← sideOf exchanged) (List.range 16)))
  -- the relay with the literal 3 that its second role adds changed to 4
  let changed := (Mutation.candidates relay).filter (·.description.endsWith "the first number one more")
  let some mutant := changed[1]? | fail "no changed literal in the relay"
  match RunComparison.compareProtocols RunComparison.arithmetic relaySide (← sideOf mutant.package) seeds with
  | .differ seed _ _ _ _ => check "the first seed that shows the change is a boundary draw" (seed < 3)
  | _ => fail "the changed relay is not told apart"
  -- mutants
  check "redeem, which only takes a field, has no mutant" (Mutation.candidates redeem).isEmpty
  -- the addition of the guarded protocol is commutative: its mutants replace it by the
  -- subtraction and the multiplication of the vocabulary, added to the table
  let guardedMutants := Mutation.mutants guarded 40
  check "guarded has two mutants, each with a row added"
    (guardedMutants.length == 2 &&
      guardedMutants.all (·.package.operations.length == guarded.operations.length + 1))
  for mutant in guardedMutants do
    check s!"guarded: the mutant {mutant.description} is told apart"
      (isDifferent (RunComparison.compareProtocols RunComparison.arithmetic guardedSide (← sideOf mutant.package) (List.range 4)))
  let mutants := Mutation.mutants relay 40
  check "relay has mutants" (!mutants.isEmpty)
  for mutant in mutants ++ guardedMutants do
    check s!"the mutant {mutant.description} is admitted" (Mutation.admitted mutant.package)
  let mut killed := 0
  for mutant in Mutation.mutants relay 40 do
    if isDifferent (RunComparison.compareProtocols RunComparison.arithmetic relaySide (← sideOf mutant.package) (List.range 4)) then
      killed := killed + 1
  check "the runs tell apart some mutants of the relay" (killed > 0)
  -- no seed: nothing was observed
  check "without a seed the comparison is incomplete"
    (isIncomplete (RunComparison.compareProtocols RunComparison.arithmetic guardedSide guardedSide []))
  -- two programs whose roles end alike and send different values: the ends do not tell them
  -- apart, and what the first role sent does, from the first seed whose input is not zero
  match RunComparison.compareProtocols RunComparison.arithmetic (← sideOf sendsInput) (← sideOf sendsDouble) seeds with
  | .differ seed _ role left right =>
    check s!"a value sent differs at the role that sends it: seed {seed}, role {reprStr role}: {left}; {right}"
      (seed == 1 && role == some 0 && left == "event 0: sent 1 at the site of key [0, 0]" &&
        right == "event 0: sent 2 at the site of key [0, 0]")
  | _ => fail "two programs that send different values are not told apart"
  check "a program that sends agrees with itself"
    (isAlike (RunComparison.compareProtocols RunComparison.arithmetic (← sideOf sendsInput) (← sideOf sendsInput) seeds))
  -- a limit is no end: two runs that both reach it are no agreement
  let reached : RunComparison.Shown := { did := [], ended := .limit 7 }
  let returned : RunComparison.Shown := { did := [(.sent, some [0], .number 1)], ended := .returned [] }
  let other : RunComparison.Shown := { did := [(.sent, some [0], .number 2)], ended := .returned [] }
  check "two runs at the limit are no agreement"
    (match RunComparison.compareShown [reached] [reached] with | .limit 7 => true | _ => false)
  check "a run cut short by the limit shows fewer things, which is no difference"
    (match RunComparison.compareShown [returned] [reached] with | .limit 7 => true | _ => false)
  check "a difference at a position that both runs have is a difference under a limit too"
    (match RunComparison.compareShown [returned, reached] [other, reached] with
      | .differ (some 0) _ _ => true | _ => false)
  -- over seeds: a limit under one seed does not end the comparison, and leaves it incomplete
  -- when no later seed shows a difference
  let underSeed (differs : Bool) (seed : Nat) : Except String (List Datum × RunComparison.Seen) :=
    .ok ([], if seed == 0 then .limit 7 else if differs && seed == 2 then .differ none "a" "b"
      else .agree)
  check "a limit under the first seed and agreement after it is incomplete"
    (match RunComparison.overSeeds [0, 1, 2] (underSeed false) with
      | .incomplete (.limit 0 7) => true | _ => false)
  check "a limit under the first seed and a difference under a later one is a difference"
    (match RunComparison.overSeeds [0, 1, 2] (underSeed true) with
      | .differ 2 .. => true | _ => false)
  -- under uninterpreted rows: every row runs and terms are compared
  let terms := UninterpretedRows.provider
  check "guarded agrees with itself under uninterpreted rows"
    (isAlike (RunComparison.compareProtocols terms guardedSide guardedSide seeds))
  check "relay agrees with itself under uninterpreted rows"
    (isAlike (RunComparison.compareProtocols terms relaySide relaySide seeds))
  check "redeem agrees with itself under uninterpreted rows"
    (isAlike (RunComparison.compareFunctions terms redeem redeem seeds))
  match RunComparison.compareProtocols terms (← sideOf sendsInput) (← sideOf sendsDouble) seeds with
  | .differ seed _ role _ _ =>
    check "under uninterpreted rows a sum sent in place of its operand differs under the first seed"
      (seed == 0 && role == some 0)
  | _ => fail "two programs that send different terms are not told apart"
  for mutant in guardedMutants do
    check s!"guarded: the mutant {mutant.description} is told apart under uninterpreted rows"
      (isDifferent (RunComparison.compareProtocols terms guardedSide (← sideOf mutant.package) (List.range 4)))
  check "a constructed scheme is not run under uninterpreted rows" terms.scheme.isNone
  -- a run that would be too long is not run
  check "a run of 2^21 iterations is too long" (RunComparison.tooLarge? (looped redeem)).isSome
  check "the relay is not too long" (RunComparison.tooLarge? relay).isNone

end RunComparisonChecks
