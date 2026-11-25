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

def memberRowSuite (repository : Repository) : TestM Unit := do
  checkMemberBindings repository
  let cases : List (String × String × String × Nat × List String) := [
    ("type members", "module caller\ninterface A:\n    type T\ninterface B:\n    type T\nmodule M: A + B:\n    type T = bool\ndef evaluate(x: bool) -> bool: x\n", "SP8", 6, ["A::T", "B::T"]),
    ("natural members", "module caller\ninterface A:\n    nat N\ninterface B:\n    nat N\nmodule M: B + A:\n    nat N = 0\ndef evaluate(x: bool) -> bool: x\n", "SP8", 6, ["B::N", "A::N"]),
    ("function and law", "module caller\ninterface A:\n    def ok(x: bool) -> bool\ninterface B:\n    law ok(x: bool): x == x\nmodule M: A + B:\n    def ok(x): x\ndef evaluate(x: bool) -> bool: x\n", "SP8", 6, ["A::ok", "B::ok"]),
    ("module members", "module caller\ninterface K\nmodule UnitModule: K:\n    nat dummy = 0\ninterface A:\n    module Child: K\ninterface B:\n    module Child: K\nmodule M: A + B:\n    module Child = UnitModule\ndef evaluate(x: bool) -> bool: x\n", "SP8", 9, ["A::Child", "B::Child"]),
    ("written bound", "module caller\ninterface A:\n    type T\ninterface B:\n    type T\ndef unused<H: A + B>(x: bool) -> bool: x\ndef evaluate(x: bool) -> bool: x\n", "SP3", 6, ["A::T", "B::T"]),
    ("different applications", "module caller\ninterface I<n: nat>:\n    type T\nmodule M: I<1> + I<2>:\n    type T = bool\ndef evaluate(x: bool) -> bool: x\n", "SP8", 4, ["I<1>::T", "I<2>::T"]),
    ("closed bound", "module caller\ninterface I<n: nat>:\n    type T\ndef unused<H: I<1> + I<2>>(x: bool) -> bool: x\ndef evaluate(x: bool) -> bool: x\n", "SP3", 4, ["I<1>::T", "I<2>::T"]),
    ("empty interface", "module caller\ninterface I<n: nat>\nmodule M: I<1> + I<2>:\n    nat dummy = 0\ndef evaluate(x: bool) -> bool: x\n", "", 0, []),
    ("same application", "module caller\ninterface I<n: nat>:\n    type T\nmodule M: I<2> + I<1 + 1>:\n    type T = bool\ndef evaluate(x: bool) -> bool: x\n", "", 0, []),
    ("default application", "module caller\ninterface I<n: nat>:\n    type T\npub module M<n: nat>: I<n> + I<2>:\n    type T = bool\ndef evaluate(x: bool) -> bool: x\n", "SP8", 4, ["I<0>::T", "I<2>::T"]),
    ("shared requirement", "module caller\ninterface C<k: nat>:\n    def keep(x: bool) -> bool\ninterface A<n: nat> where (Self: C<n>)\ninterface B<m: nat> where (Self: C<m>)\nmodule M: A<1> + B<1> + C<1>:\n    def keep(x): x\ndef evaluate(x: bool) -> bool: x\n", "", 0, []),
    ("inherited collision", "module caller\ninterface C<k: nat>:\n    def keep(x: bool) -> bool\ninterface A<n: nat> where (Self: C<n>)\ninterface B<m: nat> where (Self: C<m>)\nmodule M: A<1> + B<2> + C<1>:\n    def keep(x): x\ndef evaluate(x: bool) -> bool: x\n", "SP8", 6, ["C<1>::keep", "C<2>::keep"]),
    ("opaque use", "module caller\ninterface C<k: nat>:\n    def keep(x: bool) -> bool\ninterface A<n: nat> where (Self: C<n>)\ninterface B<m: nat> where (Self: C<m>)\ndef choose<n: nat, m: nat, H: A<n> + B<m>>(x: bool) -> bool: H::keep(x)\ndef evaluate(x: bool) -> bool: x\n", "", 0, []),
    ("inherited expression", "module caller\ninterface C<k: nat>:\n    def keep(x: bool) -> bool\ninterface A<k: nat> where (Self: C<k + 1>)\ninterface B<k: nat> where (Self: C<k + 1>)\ndef choose<n: nat, m: nat, H: A<n> + B<m>>(x: bool) -> bool: H::keep(x)\ndef evaluate(x: bool) -> bool: x\n", "", 0, []),
    ("opaque bound unused", "module caller\ninterface C<k: nat>:\n    def keep(x: bool) -> bool\ninterface A<n: nat> where (Self: C<n>)\ninterface B<m: nat> where (Self: C<m>)\ndef choose<n: nat, m: nat, H: A<n> + B<m>>(x: bool) -> bool: x\ndef evaluate(x: bool) -> bool: x\n", "", 0, []),
    ("same open application", "module caller\ninterface C<k: nat>:\n    def keep(x: bool) -> bool\ninterface A<n: nat> where (Self: C<n>)\ninterface B<m: nat> where (Self: C<m>)\nmodule M: A<1> + B<1> + C<1>:\n    def keep(x): x\ndef choose<n: nat, H: A<n> + B<n>>(x: bool) -> bool: H::keep(x)\ndef use_it(x: bool) -> bool: choose<1, M>(x)\ndef evaluate(x: bool) -> bool: x\n", "", 0, []),
    ("different inherited declarations", "module caller\ninterface C<k: nat>:\n    type T\ninterface D<k: nat>:\n    type T\ninterface A<n: nat> where (Self: C<n>)\ninterface B<m: nat> where (Self: D<m>)\ndef unused<n: nat, m: nat, H: A<n> + B<m>>(x: bool) -> bool: x\ndef evaluate(x: bool) -> bool: x\n", "SP3", 8, ["C::T", "D::T"]),
    ("closed inherited applications", "module caller\ninterface C<k: nat>:\n    type T\ninterface A<n: nat> where (Self: C<1>)\ninterface B<m: nat> where (Self: C<2>)\ndef unused<n: nat, m: nat, H: A<n> + B<m>>(x: bool) -> bool: x\ndef evaluate(x: bool) -> bool: x\n", "SP3", 6, ["C<1>::T", "C<2>::T"]),
    ("equal projected types", "module caller\ninterface K:\n    type T\ninterface C<T>:\n    def keep(x: bool) -> bool\ninterface A<T> where (Self: C<T>)\ninterface B<T> where (Self: C<T>)\nmodule P: K:\n    type T = bool\nmodule Q: K:\n    type T = bool\nmodule M: A<bool> + B<bool> + C<bool>:\n    def keep(x): x\ndef choose<U: K, V: K, H: A<U::T> + B<V::T>>(x: bool) -> bool: H::keep(x)\ndef evaluate(x: bool) -> bool: choose<P, Q, M>(x)\n", "", 0, []),
    ("other uses stay opaque", "module caller\ninterface K:\n    type T\ninterface C<T>:\n    def keep(x: bool) -> bool\ninterface A<T> where (Self: C<T>)\ninterface B<T> where (Self: C<T>)\nmodule P: K:\n    type T = bool\nmodule Q: K:\n    type T = bool\nmodule M: A<bool> + B<bool> + C<bool>:\n    def keep(x): x\ndef choose<U: K, V: K, H: A<U::T> + B<V::T>>(x: bool, y: U::T) -> bool: H::keep(x) and y\ndef evaluate(x: bool) -> bool: choose<P, Q, M>(x, x)\n", "SP12", 14, ["U::T", "opaque"]),
    ("prior error", "module caller\ndef earlier(x: bool) -> bool: unknown_name\ninterface A:\n    type T\ninterface B:\n    type T\nmodule M: A + B:\n    type T = bool\ndef evaluate(x: bool) -> bool: x\n", "NL3", 2, ["unknown_name"])]
  for (label, source, rule, line, names) in cases do
    let session ← memberSession repository source
    let errors := session.diagnostics.filter (·.isError)
    let admitted := (session.admitRoots (some #["evaluate"])).complete.isOk
    let matchesFirst := errors[0]?.any fun d => d.rule == rule && d.span.startLine.toNat == line &&
      names.all ((d.render session.state.env.renderer).contains ·)
    expectTrue (if rule.isEmpty then admitted && errors.isEmpty else !admitted && matchesFirst)
      s!"{label}: expected {rule} {names} at line {line}, admitted={admitted}: {session.renderDiagnostics}"
  -- The module supplied for H fixes the arguments of the inherited member.
  for increment in [0, 1] do
    let expression := if increment == 0 then "k" else "k + 1"
    let interfaces := "module caller\ninterface C<k: nat>:\n    def keep(x: bool) -> bool\n" ++
      s!"interface A<k: nat> where (Self: C<{expression}>)\n" ++
      s!"interface B<k: nat> where (Self: C<{expression}>)\n"
    for m in [1, 2] do
      let source := interfaces ++ s!"module M: A<1> + B<{m}> + C<{1 + increment}>:\n    def keep(x): x\n" ++
        "def choose<n: nat, m: nat, H: A<n> + B<m>>(x: bool) -> bool: H::keep(x)\n" ++
        s!"def evaluate(x: bool) -> bool: choose<n = 1, m = {m}, H = M>(x)\n"
      let session ← memberSession repository source
      let admitted := (session.admitRoots (some #["evaluate"])).complete
      if m == 1 then
        let calls := (admitted.toOption.bind (·.find? "evaluate")).any fun root =>
          (root.named.definitions.filter fun
            | .fn _ _ _ _ _ _ body _ => body.operations.any (fun op => op matches .call _)
            | _ => false).length == 2
        expectTrue (calls && !session.hasErrors) s!"missing call through H: {session.renderDiagnostics}"
      else
        let atModule := (session.diagnostics.find? (·.isError)).any fun d =>
          let message := d.render session.state.env.renderer
          d.rule == "SP8" && d.span.startLine == 6 &&
            [s!"C<{1 + increment}>::keep", s!"C<{2 + increment}>::keep"].all (message.contains ·)
        expectTrue (atModule && !admitted.isOk) s!"expected SP8 at M: {session.renderDiagnostics}"
  for bound in ["A + B", "B + A"] do
    let source := "module caller\ninterface A:\n    def copy(x: bool) -> bool\n" ++
      "interface B:\n    def copy(x: nat) -> nat\n" ++
      s!"module M: {bound}:\n    def copy(x): true\n" ++
      "def call<H: B>(x: nat) -> nat: H::copy(x)\ndef evaluate(x: nat) -> nat: call<M>(x)\n"
    let session ← memberSession repository source
    let errors := session.diagnostics.filter fun d => d.isError && d.span.file == "caller"
    let atModule := errors[0]?.any fun d => d.rule == "SP8" && d.span.startLine == 6 &&
      ["A::copy", "B::copy"].all ((d.render session.state.env.renderer).contains ·)
    expectTrue (atModule && ((session.admitRoots (some #["evaluate"])).complete matches .error _))
      s!"{bound}: expected both declarations at M; got {session.renderDiagnostics}"
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
