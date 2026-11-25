import Zkc.Tests.Frontend.TypingReference

namespace Zkc.Tests.Frontend
open Zkc.Frontend

/-- Replace one member header in the imported interface, keeping its other members and imports. -/
private structure HeaderChange where
  library : String
  original : String
  replacement : String

private def memberSession (repository : Repository) (text : String)
    (change : Option HeaderChange := none) : IO Driver.Session := do
  let load ← cachedLoader #[repository.libraries]
  Driver.Session.start.compile #[⟨"caller", Syntax.parseString "caller" text⟩] fun names => do
    if let some header := change then
      let relative := "/".intercalate names.toList ++ ".zkc"
      if relative == header.library then
        let path := repository.libraries / relative
        let text ← IO.FS.readFile path
        unless (text.splitOn header.original).length == 2 do
          throw (IO.userError s!"expected one occurrence of `{header.original}` in {path}")
        return some ⟨path.toString, Syntax.parseString path.toString (text.replace header.original header.replacement)⟩
    load names

/-- The callers of the suite, each a module `caller`. -/
private def callers : List (String × String) := [
  ("generic", "module caller\nuse zkc::algebra::{Pairing}\nuse zkc::curves::bls12_381::{Bls12381, G1, G2, Gt}\ndef apply_pair<E: Pairing>(a: E::G1, b: E::G2) -> E::Target: E::pair(a, b)\ndef evaluate(a: G1, b: G2) -> Gt: apply_pair<Bls12381>(a, b)\n"),
  ("hash-arity", "module caller\nuse zkc::hash::{Sha256}\ndef evaluate(input: [byte]) -> [byte; 32]: Sha256::hash(input, false)\n"),
  ("hash", "module caller\nuse zkc::hash::{Sha256}\ndef evaluate(input: [byte]) -> [byte; 32]: Sha256::hash(input)\n"),
  ("pair-arity", "module caller\nuse zkc::curves::bls12_381::{Bls12381, G1, G2, Gt}\ndef evaluate(a: G1, b: G2) -> Gt: Bls12381::pair(a, b, false)\n"),
  ("pair-static", "module caller\nuse zkc::curves::bls12_381::{Bls12381, G1, G2, Gt}\ndef evaluate(a: G1, b: G2) -> Gt: Bls12381::pair<7>(a, b)\n"),
  ("pair", "module caller\nuse zkc::curves::bls12_381::{Bls12381, G1, G2, Gt}\ndef evaluate(a: G1, b: G2) -> Gt: Bls12381::pair(a, b)\n"),
  ("shake", "module caller\nuse zkc::hash::{Shake128}\ndef written(input: [byte]) -> [byte; 5]: Shake128::output<count = 5>(input)\ndef inferred(input: [byte]) -> [byte; 7]: Shake128::output(input)\n")]

private def caller (name : String) : String := (callers.lookup name).getD ""

/-- A concrete call reaches the requested standard operation; the generic caller may reach it
through another stored definition. -/
private def expectRow (session : Driver.Session) (root : String) (row : Zkc.Vocabulary.RowKey) :
    TestM Unit := do
  let .ok roots := (session.admitRoots (some #[root])).complete
    | failure s!"{root}: {session.renderDiagnostics}"
  let some p := roots.find? root | failure s!"missing {root}"
  expectTrue (p.bindings.rows.isEmpty && p.named.definitions.any fun
    | .fn _ _ _ _ _ _ body _ => body.operations.any fun
      | .row (.inl found) => found == row
      | _ => false
    | _ => false) s!"{root}: missing standard row or unexpected project binding"

/-- Distinct types and modules from different files can have the same last name. -/
private def checkQualifiedOwners : TestM Unit := do
  let declarations := "pub module Box: UnitM:\n    nat dummy = 0\npub struct Item:\n    x: bool\n"
  for (bound, argument) in [("T", "Item"), ("H: UnitM", "Box")] do
    let source := "module caller\nuse left\nuse right\nuse common::{UnitM}\n" ++
      s!"interface I<{bound}>:\n    type Pick\n" ++
      s!"module M: I<left::{argument}> + I<right::{argument}>:\n    type Pick = bool\n"
    let session ← Driver.Session.start.compile #[⟨"caller", Syntax.parseString "caller" source⟩] fun path => do
      let #[file] := path | return none
      let text := if file == "common" then "module common\npub interface UnitM\n"
        else s!"module {file}\n" ++ "use common::{UnitM}\n" ++ declarations
      return some ⟨file, Syntax.parseString file text⟩
    let refused := (session.diagnostics.find? (·.isError)).any fun diag =>
      let message := diag.render session.state.env.renderer
      diag.rule == "SP8" && diag.span.startLine == 7 &&
        [s!"I<left::{argument}>::Pick", s!"I<right::{argument}>::Pick"].all (message.contains ·)
    expectTrue refused s!"qualified {argument}: {session.renderDiagnostics}"

/-- A nested module and a file module can have the same qualified path. Keep the
applications in the refusal even when their interface or their argument renders identically. -/
private def checkOwnerLocations : TestM Unit := do
  let leafText := "module a::b\npub struct T:\n    pub q: bool\npub type Leaf = T\n" ++
    "pub interface Pick:\n    def choose(x: bool) -> bool\n"
  let leaf : SourceInput := ⟨"leaf.zkc", Syntax.parseString "leaf.zkc" leafText⟩
  let direct := "module a\nuse a::b::{Pick}\npub module b:\n" ++
    "    pub interface Pick:\n        def choose(x: bool) -> bool\n" ++
    "module M: b::Pick + Pick:\n    def choose(x): x\n"
  let argument := "module a\nuse a::b::{Leaf}\npub module b:\n" ++
    "    pub struct T:\n        pub p: bool\n" ++
    "interface I<T>:\n    def pick(x: bool) -> bool\n" ++
    "module M: I<b::T> + I<Leaf>:\n    def pick(x): x\n"
  for (source, line, left, right) in [(direct, 6, "b::Pick", "Pick"), (argument, 8, "I<b::T>", "I<Leaf>")] do
    let outer : SourceInput := ⟨"outer.zkc", Syntax.parseString "outer.zkc" source⟩
    for files in [#[outer, leaf], #[leaf, outer]] do
      let session ← Driver.Session.start.compile files fun _ => pure none
      let first := session.diagnostics.find? (·.isError)
      let correct := first.any fun diag =>
        let refusal := diag.toRefusal session.state.env.renderer
        diag.rule == "SP8" && diag.span.file == "outer.zkc" && diag.span.startLine.toNat == line &&
          refusal.message.contains s!"from `{left}` at outer.zkc:{line}:11" &&
          refusal.message.contains s!"from `{right}` at outer.zkc:{line}:21"
      expectTrue correct s!"two written origins for {left} and {right}: {session.renderDiagnostics}"

/-- Calls through one bound, through the module and through a projection. Each module
header is checked in both orders, whether the body is used or not. -/
private def checkMemberBindings (repository : Repository) : TestM Unit := do
  let programs : List (String × String × String × String × String × List String) := [
    ("module caller\ninterface A:\n    def copy<n: nat>(x: bool) -> bool\ninterface B:\n    def copy<n: nat>(x: bool) -> bool where (2 <= n)\n", "A", "B", ":", "copy", [
      "    def copy(x): x\ndef byA<H: A>(x: bool) -> bool: H::copy<n = 1>(x)\ndef evaluate(x: bool) -> bool: byA<M>(x)\n",
      "    def copy(x): x\ndef byB<H: B>(x: bool) -> bool: H::copy<n = 1>(x)\ndef evaluate(x: bool) -> bool: byB<M>(x)\n",
      "    def copy(x): x\ndef evaluate(x: bool) -> bool: M::copy<n = 1>(x)\n",
      "    def copy(x): x\ndef useIt<H: A>(x: bool) -> bool: H::copy<n = 1>(x)\ndef evaluate(x: bool) -> bool: useIt<M>(x)\n",
      "    def copy(x): x\ndef useIt<H: A>(x: bool) -> bool: H::copy<n = 2>(x)\ndef evaluate(x: bool) -> bool: useIt<M>(x)\n",
      "    def copy(x): x\ndef useIt<H: B>(x: bool) -> bool: H::copy<n = 1>(x)\ndef evaluate(x: bool) -> bool: useIt<M>(x)\n",
      "    def copy(x): x\ndef useIt<H: B>(x: bool) -> bool: H::copy<n = 2>(x)\ndef evaluate(x: bool) -> bool: useIt<M>(x)\n"]),
    ("module caller\nuse zkc::algebra::{Group}\nuse zkc::curves::bls12_381::{G1}\ninterface Carrier:\n    type Element: Group\nmodule Points: Carrier:\n    type Element = G1\ninterface A:\n    def copy<T: Group>(x: T) -> T\ninterface B:\n    def copy<T: Group>(x: T) -> T where (2 <= T::Order)\n", "A", "B", ":", "copy", [
      "    def copy(x): x\ndef selected<H: B, C: Carrier>(x: C::Element) -> C::Element: H::copy(x)\ndef evaluate(x: G1) -> G1: selected<M, Points>(x)\n"]),
    ("module caller\nuse zkc::algebra::{Group}\nuse zkc::curves::bls12_381::{G1}\ninterface Carrier:\n    type Element: Group\nmodule Points: Carrier:\n    type Element = G1\ninterface A:\n    def copy<T: Group>(x: T) -> T\ninterface B:\n    def copy<T: Group>(x: T) -> T where (T::Order <= 2)\n", "A", "B", ":", "copy", [
      "    def copy(x): x\ndef selected<H: B, C: Carrier>(x: C::Element) -> C::Element: H::copy(x)\ndef evaluate(x: G1) -> G1: selected<M, Points>(x)\n"]),
    ("module caller\ninterface A:\n    def copy(x: bool) -> bool\ninterface B:\n    def copy(x: nat) -> nat\n", "A", "B", ":", "copy", [
      "    def copy(x): true\ndef call<H: B>(x: nat) -> nat: H::copy(x)\ndef evaluate(x: nat) -> nat: call<M>(x)\n",
      "    def copy(x): true\ndef evaluate(x: bool) -> bool: x\n",
      "    def copy(x): x\ndef evaluate(x: bool) -> bool: x\n"]),
    ("module caller\ninterface I<n: nat>:\n    def copy(x: [byte; n]) -> [byte; n]\n", "I<1>", "I<2>", ":", "copy", [
      "    def copy(x): x\ndef select<H: I<1>>(x: [byte; 1]) -> [byte; 1]: H::copy(x)\ndef evaluate(x: [byte; 1]) -> [byte; 1]: select<M>(x)\n",
      "    def copy(x): x\ndef select<H: I<2>>(x: [byte; 2]) -> [byte; 2]: H::copy(x)\ndef evaluate(x: [byte; 2]) -> [byte; 2]: select<M>(x)\n"]),
    ("module caller\ninterface A:\n    def width<n: nat>(x: bool) -> nat\ninterface B:\n    def width<n: nat>(x: bool) -> nat\n", "A", "B", ":", "width", [
      "    def width(x): 7\ndef readWidth<H: B>(x: bool) -> nat: H::width<n = 7>(x)\ndef evaluate(x: bool) -> nat: readWidth<M>(x)\n",
      "    def width(x): n\ndef readWidth<H: A>(x: bool) -> nat: H::width<n = 7>(x)\ndef evaluate(x: bool) -> nat: readWidth<M>(x)\n",
      "    def width(x): n\ndef readWidth<H: B>(x: bool) -> nat: H::width<n = 7>(x)\ndef evaluate(x: bool) -> nat: readWidth<M>(x)\n"]),
    ("module caller\ninterface A:\n    def copy(x: bool) -> bool\ninterface B:\n    def copy(x: bool) -> bool\n", "A", "B", ":", "copy", [
      "    def copy(x): x\ndef one<H: A>(x: bool) -> bool: H::copy(x)\ndef two<H: B>(x: bool) -> bool: H::copy(x)\ndef evaluate(x: bool) -> (bool, bool): (one<M>(x), two<M>(x))\n"]),
    ("module caller\ninterface I<minimum: nat>:\n    def copy<n: nat>(x: bool) -> bool where (minimum <= n)\n", "I<1>", "I<2>", ":", "copy", [
      "    def copy(x): x\ndef select<H: I<1>>(x: bool) -> bool: H::copy<n = 1>(x)\ndef evaluate(x: bool) -> bool: select<M>(x)\n",
      "    def copy(x): x\ndef select<H: I<1>>(x: bool) -> bool: H::copy<n = 2>(x)\ndef evaluate(x: bool) -> bool: select<M>(x)\n",
      "    def copy(x): x\ndef select<H: I<2>>(x: bool) -> bool: H::copy<n = 1>(x)\ndef evaluate(x: bool) -> bool: select<M>(x)\n",
      "    def copy(x): x\ndef select<H: I<2>>(x: bool) -> bool: H::copy<n = 2>(x)\ndef evaluate(x: bool) -> bool: select<M>(x)\n"]),
    ("module caller\nuse zkc::algebra::{Group}\nuse zkc::curves::bls12_381::{G1}\ninterface A:\n    def eq<T: Group>(a: T, b: T) -> bool\ninterface B:\n    def eq<T: Group>(a: T, b: T) -> bool\n    def other(x: bool) -> bool\n", "A", "B", " = primitive(\"group.equal\")", "eq", [
      "def choose<H: A>(a: G1, b: G1) -> bool: H::eq<G1>(a,b)\ndef evaluate(a: G1, b: G1) -> bool: choose<M>(a,b)\n",
      "def choose<H: B>(a: G1, b: G1) -> bool: H::eq<G1>(a,b)\ndef evaluate(a: G1, b: G1) -> bool: choose<M>(a,b)\n"]),
    ("module caller\ninterface A:\n    def pick<n: nat>(a: bool, b: bool) -> bool where (2 <= n)\ninterface B:\n    def pick<n: nat>(a: bool, b: bool) -> bool where (2 <= n)\n", "A", "B", ":", "pick", [
      "    def pick(a, b): a\ndef choose<H: B>(a: bool, b: bool) -> bool: H::pick<n = 2>(b = b, a = a)\ndef evaluate(a: bool, b: bool) -> bool: choose<M>(a, b)\n",
      "    def pick(a, b): b\ndef choose<H: B>(a: bool, b: bool) -> bool: H::pick<n = 2>(b = b, a = a)\ndef evaluate(a: bool, b: bool) -> bool: choose<M>(a, b)\n"]),
    ("module caller\ninterface A:\n    def pick(x: bool) -> bool\ninterface B:\n    def pick(x: bool) -> bool\n    def other(x: bool) -> bool\n", "A", "B", " = primitive(\"example.project\")", "pick", [
      "def choose<H: A>(x: bool) -> bool: H::pick(x)\ndef evaluate(x: bool) -> bool: choose<M>(x)\n",
      "def choose<H: B>(x: bool) -> bool: H::pick(x)\ndef evaluate(x: bool) -> bool: choose<M>(x)\n",
      "def first(x: bool) -> bool = primitive(\"example.project\")\ndef second(x: bool) -> bool = primitive(\"example.project.pick\")\ndef choose<H: A>(x: bool) -> (bool, bool, bool): (H::pick(x), first(x), second(x))\ndef evaluate(x: bool) -> (bool, bool, bool): choose<M>(x)\n",
      "def first(x: bool) -> bool = primitive(\"example.project\")\ndef second(x: bool) -> bool = primitive(\"example.project.pick\")\ndef choose<H: B>(x: bool) -> (bool, bool, bool): (H::pick(x), first(x), second(x))\ndef evaluate(x: bool) -> (bool, bool, bool): choose<M>(x)\n"])]
  for (interfaces, left, right, implementation, name, callers) in programs do
    let line := (interfaces.splitOn "\n").length
    for bound in [s!"{left} + {right}", s!"{right} + {left}"] do
      for caller in callers do
        let text := interfaces ++ s!"module M: {bound}" ++ implementation ++ "\n" ++ caller
        let session ← memberSession repository text
        let first := session.diagnostics.find? (·.isError)
        let atBinding := first.any fun d =>
          let message := d.render session.state.env.renderer
          d.rule == "SP8" && d.span.startLine.toNat == line &&
            message.contains s!"{left}::{name}" && message.contains s!"{right}::{name}"
        expectTrue (atBinding && !(session.admitRoots (some #["evaluate"])).complete.isOk)
          s!"{text}expected SP8 at M, got {session.renderDiagnostics}"

/-- In the opaque typing the argument of N contains a stand-in or a fresh type.
At concrete values the two applications can coincide or give a collision. -/
private def checkConcreteApplications (repository : Repository) : TestM Unit := do
  let cases : List (String × String × String × String × String) := [
    ("module caller\ninterface Carrier:\n    type Element\nmodule Bits: Carrier:\n    type Element = bool\nmodule Naturals: Carrier:\n    type Element = nat\ninterface I<U>:\n    def keep(x: bool) -> bool\nmodule N<U>: I<U> + I<[bool; 2]>:\n    def keep(x): x\ndef pick<C: Carrier>(x: bool) -> bool: N<U = [C::Element; 2]>::keep(x)\n", "Bits", "Naturals", "I<[nat; 2]>::keep", "I<[bool; 2]>::keep"),
    ("module caller\ninterface K\ninterface I<H: K>:\n    def keep(x: bool) -> bool\nmodule P: K:\n    nat dummy = 0\nmodule Other: K:\n    nat dummy = 0\nmodule N<X: K>: I<X> + I<P>:\n    def keep(x): x\ndef pick<H: K>(x: bool) -> bool: N<X = H>::keep(x)\n", "P", "Other", "I<Other>::keep", "I<P>::keep")]
  for (source, same, different, left, right) in cases do
    let root (argument : String) := source ++ s!"def evaluate(x: bool) -> bool: pick<{argument}>(x)\n"
    let equal ← memberSession repository (root same)
    let distinct ← memberSession repository (root different)
    let error := distinct.diagnostics.find? (·.isError)
    let atBinding := error.any fun d =>
      let message := d.render distinct.state.env.renderer
      d.rule == "SP8" && message.contains "module `N`" && message.contains left && message.contains right
    expectTrue (!equal.hasErrors && (equal.admitRoots (some #["evaluate"])).complete.isOk &&
      atBinding && !(distinct.admitRoots (some #["evaluate"])).complete.isOk)
      s!"{same} and {different}: {equal.renderDiagnostics} / {distinct.renderDiagnostics}"

/-- Members of two disjoint interfaces retain their respective project operations at emission. -/
private def checkDisjointRows (repository : Repository) : TestM Unit := do
  let source := "module disjoint
interface A:
    def first(x: bool) -> bool
interface B:
    def middle(x: bool) -> bool
    def last(x: bool) -> bool
module Ops: A + B = primitive(\"project.ops\")
def one(x: bool) -> bool = primitive(\"project.ops\")
def two(x: bool) -> bool = primitive(\"project.ops.middle\")
def three(x: bool) -> bool = primitive(\"project.ops.last\")
def apply<H: A + B>(x: bool) -> (bool, bool, bool): (H::first(one(x)), H::middle(two(x)), H::last(three(x)))
def evaluate(x: bool) -> (bool, bool, bool): apply<Ops>(x)
"
  let expected := ["project.ops", "project.ops", "project.ops.middle", "project.ops.middle",
    "project.ops.last", "project.ops.last"]
  for header in ["A + B", "B + A"] do
    let session ← memberSession repository (source.replace "Ops: A + B" ("Ops: " ++ header))
    let .ok roots := (session.admitRoots (some #["evaluate"])).complete
      | failure s!"disjoint interfaces {header}: {session.renderDiagnostics}"
    let some p := roots.find? "evaluate" | failure "missing evaluate"
    let rows := p.named.definitions.flatMap fun
      | .fn _ _ _ _ _ _ body _ => body.operations.filterMap fun
        | .row (.inr key) => some key.name
        | _ => none
      | _ => []
    expectTrue (rows == expected) s!"disjoint interfaces {header}: expected {expected}, got {rows}"

/-- SP7 checks the eligibility of a default before reporting competing member owners.
An explicit request for those arguments must still be checked. -/
private def checkDefaultConditions (repository : Repository) : TestM Unit := do
  let source (condition : String) := "module caller\n" ++
    s!"interface I<n: nat> where ({condition}):\n    nat Height\n    type T\n" ++
    "pub module M<n: nat>: I<n> + I<1>:\n    nat Height = 1\n    type T = bool\n"
  let root := "def evaluate(x: M<1>::T) -> bool: x\n"
  for condition in ["n == 1", "Self::Height == n"] do
    let session ← memberSession repository (source condition ++ root)
    let skipped := session.state.table.requestedIds.any fun id =>
      let e := session.state.table.entryAt! id
      session.state.program.nameOf e.key.declaration == "M" && e.key.arguments == #[.natural 0] &&
        (e.state matches .skipped)
    expectTrue (skipped && !session.hasErrors && (session.admitRoots (some #["evaluate"])).complete.isOk)
      s!"ineligible default under {condition}: {session.renderDiagnostics}"
    let demanded := source condition ++ "def via<H: I<1>>(x: bool) -> bool: x\n" ++
      "def evaluate(x: bool) -> bool: via<M<0>>(x)\n"
    let explicit ← memberSession repository demanded
    expectTrue ((explicit.diagnostics.find? (·.isError)).any (·.rule == "SP8") &&
      !(explicit.admitRoots (some #["evaluate"])).complete.isOk)
      s!"explicit colliding instance under {condition}: {explicit.renderDiagnostics}"
  let eligible ← memberSession repository (source "Self::Height == 1" ++ root)
  expectTrue ((eligible.diagnostics.find? (·.isError)).any (·.rule == "SP8") &&
    !(eligible.admitRoots (some #["evaluate"])).complete.isOk)
    s!"eligible colliding default: {eligible.renderDiagnostics}"

/-- A default needs only the values read by its interface predicates. An unprovided
primitive member can wait while a different predicate already decides the candidate. -/
private def checkEligibilityReads (repository : Repository) : TestM Unit := do
  let header := "module caller\ninterface Unknown:\n    nat Limit\n" ++
    "module External: Unknown = primitive(\"project.external\")\n"
  for (condition, outcome) in [("n <= 1", "SP8"), ("Self::Known == 1", "SP8"),
      ("n == 1", "skipped"), ("Self::Known == 2", "skipped"), ("Self::Height == n", "waits")] do
    let source := header ++ s!"interface I<n: nat> where ({condition}):\n    nat Height\n    nat Known\n" ++
      "pub module M<n: nat>: I<n> + I<1> where (n == 0):\n" ++
      "    nat Height = External::Limit\n    nat Known = 1\ndef evaluate(x: bool) -> bool: x\n"
    let session ← memberSession repository source
    let state := session.state
    let observed := state.table.requestedIds.any fun id =>
      let entry := state.table.entryAt! id
      state.program.nameOf entry.key.declaration == "M" && entry.key.arguments == #[.natural 0] &&
        match outcome with
        | "skipped" => (entry.state matches .skipped)
        | "waits" => (entry.state matches .done (.data (.waits _ true)))
        | _ => (entry.state matches .failed)
    let error := session.diagnostics.find? (·.isError)
    expectTrue (observed && (if outcome == "SP8" then error.any (·.rule == "SP8")
      else error.isNone && (session.admitRoots (some #["evaluate"])).complete.isOk))
      s!"eligibility of {condition}: {session.renderDiagnostics}"

/-- Default argument inference selects the first fully formed implementation. A skipped
or waiting candidate cannot supply a module by its header alone. -/
private def checkInferredModule (repository : Repository) : TestM Unit := do
  let intro := "module caller\ninterface Unknown:\n    nat Limit\n" ++
    "module External: Unknown = primitive(\"project.external\")\n" ++
    "interface I<n: nat> where (Self::Height == n):\n    nat Height\n"
  let good := "module Good: I<0>:\n    nat Height = 0\n"
  let choose := "pub def choose<H: I<0>>(x: bool) -> bool: x\ndef evaluate(x: bool) -> bool: x\n"
  for value in ["1", "External::Limit"] do
    let candidate := "module M<n: nat>: I<n> + I<1> where (n == 0):\n    nat Height = " ++ value ++ "\n"
    for body in [candidate ++ good, good ++ candidate, candidate] do
      let session ← memberSession repository (intro ++ body ++ choose)
      let state := session.state
      let chosen := state.table.requestedIds.filterMap fun id => do
        let entry := state.table.entryAt! id
        guard (state.program.nameOf entry.key.declaration == "choose" && entry.key.opaqueFor.isNone)
        let #[.module receiver] := entry.key.arguments | none
        return state.program.nameOf (← state.table.allocatedKey? receiver).declaration
      let expected := if body == candidate then #[] else #["Good"]
      expectTrue (chosen == expected && (session.admitRoots none).complete.isOk)
        s!"inferred module at {value}: expected {expected}, got {chosen}: {session.renderDiagnostics}"

/-- A module can implement the right interface at different values, or require a sort
that the inferred argument does not have. Neither candidate belongs to this search. -/
private def checkCandidateBounds (repository : Repository) : TestM Unit := do
  let intro := "module caller\ninterface I<n: nat>:\n    nat Height\n" ++
    "module Wrong<k: nat>: I<1> + I<2>:\n    nat Height = 7\nmodule Good: I<0>:\n    nat Height = 0\n"
  let first := "pub def choose<H: I<0>>(x: bool) -> bool: x\n"
  let matching := "pub def again<H: I<1>>(x: bool) -> bool: x\n"
  let root := "def evaluate(x: bool) -> bool: x\n"
  let filtered ← memberSession repository (intro ++ first ++ root)
  expectTrue ((filtered.admitRoots none).complete.isOk &&
    filtered.state.results.packageReports.any (·.description.contains "choose<Good>"))
    s!"wrong interface arguments: {filtered.renderDiagnostics}"
  for searches in [first ++ matching, matching ++ first] do
    let session ← memberSession repository (intro ++ searches ++ root)
    expectTrue ((session.diagnostics.find? (·.isError)).any (·.rule == "SP8"))
      s!"matching application should report the collision: {session.renderDiagnostics}"
  let sorts := "module caller\nuse zkc::algebra::{PrimeField}\ninterface I<T>:\n    def ok(x: bool) -> bool\n" ++
    "module NeedsField<T: PrimeField>: I<T>:\n    def ok(x): x\nmodule Good: I<bool>:\n    def ok(x): x\n" ++
    "pub def choose<H: I<bool>>(x: bool) -> bool: x\n"
  let session ← memberSession repository (sorts ++ root)
  expectTrue ((session.admitRoots none).complete.isOk &&
    session.state.results.packageReports.any (·.description.contains "choose<Good>"))
    s!"inferred argument outside the candidate's sort: {session.renderDiagnostics}"
  let intro := "module caller\nuse zkc::algebra::{PrimeField}\ninterface NeedsField<T: PrimeField>\n" ++
    "interface Unknown:\n    nat Limit\nmodule External: Unknown = primitive(\"project.external\")\n" ++
    "interface I<n: nat>:\n    nat Height\n"
  let good := "module Good: I<0>:\n    nat Height = 0\n"
  for height in ["0", "External::Limit"] do
    for extra in ["", " + I<1>"] do
      let wrong := "module M<n: nat>: NeedsField<bool> + I<n>" ++ extra ++ ":\n    nat Height = " ++ height ++ "\n"
      for declarations in [wrong ++ good, good ++ wrong] do
        let session ← memberSession repository (intro ++ declarations ++ first ++ root)
        expectTrue ((session.admitRoots none).complete.isOk && !session.hasErrors &&
          session.state.results.packageReports.any (·.description.contains "choose<Good>"))
          s!"a bound on an applied interface must skip this candidate: {session.renderDiagnostics}"
  let explicit := intro ++ "module M<n: nat>: NeedsField<bool> + I<n>:\n    nat Height = 0\n" ++
    first ++ "def evaluate(x: bool) -> bool: choose<M<0>>(x)\n"
  let session ← memberSession repository explicit
  expectTrue ((session.diagnostics.find? (·.isError)).any (·.rule == "SP3"))
    s!"an explicitly requested module must discharge the interface bound: {session.renderDiagnostics}"

/-- The members of an otherwise valid candidate with different interface arguments used to
allocate definition numbers before the next candidate was selected. Pin the emitted key of that
selection, including when a member's type instantiates another declaration. -/
private def checkCandidatePackageKeys (repository : Repository) : TestM Unit := do
  let intro := "module caller\ninterface I<n: nat>:\n    nat Height\n" ++
    "module Wrong<k: nat>: I<1>:\n    nat Height = 7\nmodule Good: I<0>:\n    nat Height = 0\n"
  let computed := "module caller\ntype Alias<T> = T\ninterface I<n: nat>:\n    type Value\n    nat Height\n" ++
    "module Wrong<k: nat>: I<1>:\n    type Value = Alias<bool>\n    nat Height = 7\n" ++
    "module Good: I<0>:\n    type Value = bool\n    nat Height = 0\n"
  let root := "pub def choose<H: I<0>>(x: bool) -> bool: x\ndef evaluate(x: bool) -> bool: x\n"
  for (declarations, stored) in [(intro, "stored5"), (computed, "stored8")] do
    let session ← memberSession repository (declarations ++ root)
    let .ok roots := (session.admitRoots none).complete | failure s!"{session.renderDiagnostics}"
    let some package := roots.find? "default instance `choose<Good>`" | failure "missing chosen candidate"
    expectTrue ((Written.package package.toSourcePackage).text.contains s!"def {stored} : Definition")
      s!"skipping the first candidate changed the emitted key of choose<Good>, expected {stored}"

/-- A generated protocol view can require a function of the provisional receiver through
the opaque view of a generic parameter. An unrelated unavailable natural has no bearing. -/
private def checkGeneratedEligibility (repository : Repository) : TestM Unit := do
  let intro := "module caller\ninterface Unknown:\n    nat Limit\n" ++
    "module External: Unknown = primitive(\"project.external\")\ninterface Callable:\n    def ok(x: bool) -> bool\n" ++
    "protocol Echo<H: Callable> roles(P, V)(x: bool @(P, V)):\n    guard @V H::ok(x)\n" ++
    "interface I<n: nat> where (Echo<Self>::Run == Echo<Self>::Run):\n    nat Height\n"
  for value in ["1", "External::Limit"] do
    let source := intro ++ "pub module M<n: nat>: Callable + I<n> + I<1> where (n == 0):\n" ++
      s!"    def ok(x): x\n    nat Height = {value}\ndef evaluate(x: bool) -> bool: x\n"
    let session ← memberSession repository source
    expectTrue ((session.diagnostics.find? (·.isError)).any (·.rule == "SP8"))
      s!"eligibility through a protocol view at {value}: {session.renderDiagnostics}"

/-- A single-owner candidate can also close other queries through its provisional Self.
A later explicit dependency must recompute them after a skip or wait. -/
private def checkSingleOwnerDependencies (repository : Repository) : TestM Unit := do
  let head := "module caller\ninterface Unknown:\n    nat Limit\n" ++
    "module External: Unknown = primitive(\"project.external\")\n"
  for gate in ["Self::Height", "Self::Gate::Limit"] do
    let intro := head ++ s!"interface I<n: nat> where (Memo<n> == Memo<n>, {gate} == n):\n" ++
      "    nat Height\n    module Gate: Unknown\ntype Buffer<H: I<0>> = [bool; H::Height]\n" ++
      "struct Memo<n: nat>:\n    entries: Buffer<M<n>>\n"
    let owner := "pub module M<n: nat>: I<n> where (n == 0):\n    nat Height = 1\n    module Gate = External\n"
    let useSite := "pub def force<k: nat>(b: Memo<0>) -> bool: b.entries[0]\n"
    for body in [owner ++ useSite, useSite ++ owner] do
      let session ← memberSession repository (intro ++ body)
      expectTrue ((session.diagnostics.find? (·.isError)).any (·.rule == "NL1") &&
        !(session.admitRoots none).complete.isOk)
        s!"a transitive request after {gate}: {session.renderDiagnostics}"

/-- A wait from testing an ineligible or as-yet undecided default cannot satisfy a
later demand for a module with two member owners. Exercise both request orders. -/
private def checkWaitingDefault (repository : Repository) : TestM Unit := do
  let intro := "module caller\ninterface I<n: nat> where (Self::Height == n):\n    nat Height\n"
  let owner := "pub module M<n: nat>: I<n> + I<1> = primitive(\"project.unknown\")\n"
  let useSite := "struct Box<H: I<0>>:\n    flag: bool\n" ++
    "pub def force<k: nat>(b: Box<M<0>>) -> bool: b.flag\n"
  let alone ← memberSession repository (intro ++ owner ++ "def evaluate() -> bool: true\n")
  expectTrue (!alone.hasErrors && (alone.admitRoots (some #["evaluate"])).complete.isOk)
    s!"independent root while a default waits: {alone.renderDiagnostics}"
  for body in [owner ++ useSite, useSite ++ owner] do
    let conflict ← memberSession repository (intro ++ body)
    let refused := (conflict.diagnostics.find? (·.isError)).any fun d =>
      let message := d.render conflict.state.env.renderer
      d.rule == "SP8" && message.contains "I<0>::Height" && message.contains "I<1>::Height"
    expectTrue (refused && !(conflict.admitRoots none).complete.isOk)
      s!"demand after default wait: {conflict.renderDiagnostics}"
    let equal ← memberSession repository (intro ++ body.replace "I<n> + I<1>" "I<n> + I<n + 0>")
    expectTrue (!equal.hasErrors && (equal.admitRoots none).complete.isOk)
      s!"equal owners with an unavailable value: {equal.renderDiagnostics}"

/-- A skipped or waiting default can compute Memo and its field type through its
provisional Self. A later consumer must request both again. An independent function
keeps the definition numbers emitted for each declaration order. -/
private def checkDefaultDependencies (repository : Repository) : TestM Unit := do
  let external := "interface Unknown:\n    nat Limit\nmodule External: Unknown = primitive(\"review.unbound\")\n"
  for waits in [false, true] do
    let gate := if waits then "    module Gate: Unknown\n" else ""
    let value := if waits then "    module Gate = External\n" else ""
    let condition := if waits then "Self::Gate::Limit" else "Self::Height"
    let intro := "module caller\n" ++ (if waits then external else "") ++
      s!"interface I<n: nat> where (Memo<n> == Memo<n>, {condition} == n):\n    nat Height\n" ++ gate ++
      "type Buffer<H: I<1>> = [bool; H::Height]\nstruct Memo<n: nat>:\n    entries: Buffer<M<n>>\n"
    let owner := "pub module M<n: nat>: I<n> + I<1> where (n == 0):\n    nat Height = 1\n" ++ value
    for ownerFirst in [true, false] do
      let program (useSite : String) := intro ++ (if ownerFirst then owner ++ useSite else useSite ++ owner)
      let consumer ← memberSession repository (program "pub def force<k: nat>(b: Memo<0>) -> bool: b.entries[0]\n")
      let first := consumer.diagnostics.find? (·.isError)
      expectTrue (first.any (·.rule == "SP8") && !(consumer.admitRoots none).complete.isOk)
        s!"transitive demand, waiting={waits}, owner first={ownerFirst}: {consumer.renderDiagnostics}"
      let independent ← memberSession repository (program "pub def force<k: nat>(b: bool) -> bool: b\n")
      let roots := independent.state.results.packageReports.filterMap fun report =>
        if report.outcome matches .admitted _ then some report.root else none
      let firstId := (if ownerFirst then 7 else 0) + (if waits then 1 else 0)
      expectTrue ((independent.admitRoots none).complete.isOk && roots == (Array.range 4).map (firstId + ·))
        s!"independent roots after a default probe: {roots}, {independent.renderDiagnostics}"

/-- Project-binding reports discovered while checking a default reach the CLI. -/
private def checkDefaultReports (repository : Repository) : TestM Unit := do
  let source := "module caller\nuse support::{Ext}\n" ++
    "interface I<n: nat> where (Ext == Ext, Self::Height == n):\n    nat Height\n" ++
    "pub module M<n: nat>: I<n> + I<1> where (n == 0):\n    nat Height = 1\n" ++
    "def evaluate(x: bool) -> bool: x\n"
  let support := "module support\npub type Ext = primitive(\"project.observed\")\n"
  let load ← cachedLoader #[repository.libraries]
  let session ← Driver.Session.start.compile #[⟨"caller", Syntax.parseString "caller" source⟩] fun path => do
    if path == #["support"] then return some ⟨"support", Syntax.parseString "support" support⟩
    load path
  let reports := session.state.results.reports.filter (·.contains "project.observed")
  expectTrue (reports.size == 1 && (session.admitRoots (some #["evaluate"])).complete.isOk)
    s!"project binding seen by a skipped default: {reports}, {session.renderDiagnostics}"

/-- An empty collect can first request a record whose id was reserved before its
body was typed apart. Reconstruct the record in the restored state. -/
private def checkReservedCollect (repository : Repository) : TestM Unit := do
  let source := "module caller\nstruct Safe<n: nat>:\n    flag: bool\n" ++
    "interface I<n: nat> where (Safe<n> == Safe<n>, Self::Height == n):\n    nat Height\n" ++
    "pub module M<n: nat>: I<n> + I<1> where (n == 0):\n    nat Height = 1\n" ++
    "pub def force<k: nat>() -> bool:\n    for i in 0..0 collect (ys = Safe<0>{flag = true}):\n" ++
    "        x = false\n    return true\n"
  let session ← memberSession repository source
  let some (_, decl) := session.state.program.declarations.zipIdx.find? (fun (d, _) => d.name.any (·.text == "Safe"))
    | failure "missing Safe"
  let results := session.state.results
  let actual := (results.instance? {declaration := decl, arguments := #[.natural 0]}).bind results.content?
  expectTrue (actual.isSome && (session.admitRoots none).complete.isOk)
    s!"the collected type has a signature in the restored state: {session.renderDiagnostics}"

/-- A probe can fill an older reservation and create new ones. Only a real request
gets an entry and a place in the traversal order, even when its number is older. -/
private def checkReservedRequests : TestM Unit := do
  let empty : SignatureTable String Nat := default
  let (base, first, _) := empty.intern "present" default none
  let base := base.setState first (.done 11)
  let trialFrame : ChainFrame := { subject := .ofText "trial", span := { (default : Syntax.Span) with startLine := 1 } }
  let (trial, early, _) := base.intern "early" trialFrame (some ⟨.signature, first⟩)
  let trial := (trial.setState early (.done 22)).addRequest first ⟨.signature, early⟩
  let saved := base.reserveNewKeys trial
  expectTrue (saved.allocatedCount == 2 && saved.allocatedKey? early == some "early" &&
    saved.requestedIds == #[first] && saved.find? "early" == none && (saved.entryAt? early).isNone &&
    saved.result? "present" == some 11 && (saved.entryAt? first).any (·.requests.isEmpty))
    "rollback retains only the allocation from a new trial request"
  let (retried, retriedEarly, freshRetry) := saved.intern "early" trialFrame none
  let unchanged := saved.reserveNewKeys retried
  expectTrue (freshRetry && retriedEarly == early &&
    unchanged.requestedIds == #[first] && (unchanged.entryAt? early).isNone)
    "rollback discards requests even when the trial allocates no new keys"
  let (nested, late, _) := retried.intern "late" trialFrame none
  let saved := saved.reserveNewKeys (retried.reserveNewKeys nested)
  let (saved, actualLate, freshLate) := saved.intern "late" default none
  let requester := some (⟨.signature, actualLate⟩ : QueryRef)
  let actualFrame : ChainFrame := { subject := .ofText "actual", span := { (default : Syntax.Span) with startLine := 2 } }
  let (final, actualEarly, freshEarly) := saved.intern "early" actualFrame requester
  let (final, same, freshAgain) := final.intern "early" trialFrame none
  expectTrue (saved.find? "early" == none && saved.allocatedCount == 3 &&
    actualEarly == early && actualLate == late && freshLate && freshEarly && same == early && !freshAgain &&
    final.requestedIds == #[first, late, early] &&
    (final.entryAt? early).any (fun entry => entry.requestedBy == requester &&
      entry.requested.span.startLine == 2 && (entry.state matches .inProgress) && entry.requests.isEmpty) &&
    (final.result? "early").isNone) "real requests reuse stable numbers and determine request order and frames"

/-- Evaluating a member precondition can instantiate an otherwise unused alias. The check
returns no emitted value, so it must not shift the keys of the member body or a following call. -/
private def checkMemberConditionBytes (repository : Repository) : TestM Unit := do
  let source := "module caller\ntype Identity<T> = T\ninterface I:\n" ++
    "    def copy<T, n: nat>(x: T) -> T where (n == 9, T == T)\nmodule M: I:\n    def copy(x): x\n" ++
    "def twice<T>(x: T) -> T: M::copy<T, 9>(M::copy<T, 9>(x))\ndef evaluate(x: bool) -> bool: twice(x)\n"
  let package (text : String) : TestM String := do
    let session ← memberSession repository text
    let .ok roots := (session.admitRoots (some #["evaluate"])).complete
      | do failure s!"{session.renderDiagnostics}"; return ""
    let some root := roots.find? "evaluate" | do failure "missing evaluate"; return ""
    return (Written.package root.toSourcePackage).text
  let plain ← package source
  let throughAlias ← package (source.replace "T == T" "Identity<T> == T")
  expectTrue (plain == throughAlias) "a member precondition changed the emitted package"

/-- A third declaration of the same name leaves one diagnostic naming the first two owners. -/
private def checkCollisionWitness (repository : Repository) : TestM Unit := do
  let source := "module caller\ninterface A:\n    type T\ninterface B:\n    type T\n" ++
    "interface C:\n    type T\nmodule M: A + B + C:\n    type T = bool\ndef evaluate() -> bool: true\n"
  let session ← memberSession repository source
  let errors := session.diagnostics.filter (·.isError)
  let firstPair := errors[0]?.any fun d =>
    let message := d.render session.state.env.renderer
    d.rule == "SP8" && d.span.startLine == 8 && message.contains "A::T" && message.contains "B::T" &&
      !message.contains "C::T"
  expectTrue (errors.size == 1 && firstPair) s!"three declarations of T: {session.renderDiagnostics}"

def memberRowSuite (repository : Repository) : TestM Unit := do
  checkQualifiedOwners
  checkOwnerLocations
  checkReservedRequests
  checkMemberConditionBytes repository
  checkEligibilityReads repository
  checkInferredModule repository
  checkCandidateBounds repository
  checkCandidatePackageKeys repository
  checkGeneratedEligibility repository
  checkSingleOwnerDependencies repository
  checkWaitingDefault repository
  checkDefaultDependencies repository
  checkDefaultReports repository
  checkReservedCollect repository
  checkDefaultConditions repository
  checkDisjointRows repository
  checkConcreteApplications repository
  checkCollisionWitness repository
  checkMemberBindings repository
  let cases : List (String × String × Nat × List String) := [
    ("type members", "module caller\ninterface A:\n    type T\ninterface B:\n    type T\nmodule M: A + B:\n    type T = bool\ndef evaluate(x: bool) -> bool: x\n", 6, ["A::T", "B::T"]),
    ("natural members", "module caller\ninterface A:\n    nat N\ninterface B:\n    nat N\nmodule M: B + A:\n    nat N = 0\ndef evaluate(x: bool) -> bool: x\n", 6, ["B::N", "A::N"]),
    ("function and law", "module caller\ninterface A:\n    def ok(x: bool) -> bool\ninterface B:\n    law ok(x: bool): x == x\nmodule M: A + B:\n    def ok(x): x\ndef evaluate(x: bool) -> bool: x\n", 6, ["A::ok", "B::ok"]),
    ("module members", "module caller\ninterface K\nmodule UnitModule: K:\n    nat dummy = 0\ninterface A:\n    module Child: K\ninterface B:\n    module Child: K\nmodule M: A + B:\n    module Child = UnitModule\ndef evaluate(x: bool) -> bool: x\n", 9, ["A::Child", "B::Child"]),
    ("different applications", "module caller\ninterface I<n: nat>:\n    type T\nmodule M: I<1> + I<2>:\n    type T = bool\ndef evaluate(x: bool) -> bool: x\n", 4, ["I<1>::T", "I<2>::T"]),
    ("default application", "module caller\ninterface I<n: nat>:\n    type T\npub module M<n: nat>: I<n> + I<2>:\n    type T = bool\ndef evaluate(x: bool) -> bool: x\n", 4, ["I<0>::T", "I<2>::T"]),
    ("protocol member", "module caller\ninterface Signals<n: nat>:\n    protocol Test roles(P, V)(x: bool @(P, V))\nmodule Relay: Signals<1> + Signals<2>:\n    protocol Test roles(P, V)(x: bool @(P, V)):\n        guard @V x\nprotocol Client roles(P, V)(x: bool @(P, V)):\n    Relay::Test(x)\ndef evaluate() -> bool: true\n", 4, ["Signals<1>::Test", "Signals<2>::Test"])]
  for (label, source, line, names) in cases do
    let session ← memberSession repository source
    let errors := session.diagnostics.filter (·.isError)
    let admitted := (session.admitRoots (some #["evaluate"])).complete.isOk
    let matchesFirst := errors[0]?.any fun d => d.rule == "SP8" && d.span.startLine.toNat == line &&
      names.all ((d.render session.state.env.renderer).contains ·)
    expectTrue (!admitted && matchesFirst)
      s!"{label}: expected SP8 {names} at line {line}, admitted={admitted}: {session.renderDiagnostics}"
  expectRow (← memberSession repository (caller "generic")) "evaluate" .pair
  let shake ← memberSession repository (caller "shake")
  expectRow shake "written" (.hash (.shake128 5))
  expectRow shake "inferred" (.hash (.shake128 7))
  let pair := "def pair(a: G1, b: G2) -> Target"
  let hash := "def hash(input: [byte]) -> [byte; Size]"
  let algebra (s : String) : Option HeaderChange := some ⟨"zkc/algebra.zkc", pair, s⟩
  let hashes (s : String) : Option HeaderChange := some ⟨"zkc/hash.zkc", hash, s⟩
  -- a function added to the interface leaves the row of the member that was there
  expectRow (← memberSession repository (caller "hash")
    (hashes (hash ++ "\n    spec def helper(x: bool) -> bool"))) "evaluate" (.hash .sha256)
  let cases : List (String × Option HeaderChange × String × List String) := [
    ("pair-static", none, "SP5", ["pair"]),
    ("pair-static", algebra "def pair<n: nat>(a: G1, b: G2) -> Target", "SP8", ["pairing.pair", "static arguments"]),
    ("pair", algebra ("spec " ++ pair), "SX2", ["pair"]),
    ("pair", algebra "def pair(a: G1, b: G2) -> G1", "SP8", ["pairing.pair", "takes", "gives"]),
    ("pair-arity", algebra "def pair(a: G1, b: G2, flag: bool) -> Target", "SP8", ["pairing.pair", "takes", "gives"]),
    ("hash", hashes "def hash(input: [byte]) -> bool", "SP8", ["hash.sha256", "takes", "gives"]),
    ("hash-arity", hashes "def hash(input: [byte], flag: bool) -> [byte; Size]", "SP8", ["hash.sha256", "takes", "gives"])]
  for (file, change, rule, words) in cases do
    let session ← memberSession repository (caller file) change
    let errors := session.diagnostics.filter fun d => d.isError && d.span.file == "caller"
    let refused := errors.any fun d => d.rule == rule &&
      words.all ((d.render session.state.env.renderer).contains ·)
    expectTrue (refused && ((session.admitRoots (some #["evaluate"])).complete matches .error _))
      s!"{file}: expected {rule} ({words}) at the caller; got {session.renderDiagnostics}"

end Zkc.Tests.Frontend
