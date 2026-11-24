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

/-- Conditions on the interface member apply to a call through either implementation. -/
private def memberParameterSuite (repository : Repository) : TestM Unit := do
  let boundedCopy := "module caller
interface I<minimum: nat>:
    def copy<n: nat>(input: [byte; n]) -> [byte; n] where (minimum <= n)
module M: I<2>:
    def copy(input): input
def evaluate(input: [byte; 1]) -> [byte; 1]: M::copy<n = 1>(input)"
  let fieldCopy := "module caller
use zkc::algebra::{Field}
interface I:
    def copy<T: Field>(x: T) -> T
module M: I:
    def copy(x): x
def evaluate(x: bool) -> bool: "
  let groupEqual := "module caller
use zkc::algebra::{Field}
use zkc::curves::bls12_381::{G1}
interface I:
    def eq<T: Field>(a: T, b: T) -> bool
module M: I = primitive(\"group.equal\")
def evaluate(a: G1, b: G1) -> bool: M::eq<G1>(a, b)"
  let sized := "module caller
interface I:
    nat Size
    def copy(x: bool) -> bool where (2 <= Self::Size)
module M: I:
    nat Size = 1
    def copy(x): x
def evaluate(x: bool) -> bool: M::copy(x)"
  let shake := "module caller
use zkc::hash::{ExtendableOutput, Shake128}
def one<H: ExtendableOutput>(input: [byte]) -> [byte; 1]: H::output(input)
def evaluate(input: [byte]) -> [byte; 1]: one<Shake128>(input)"
  let output := "def output<count: nat>(input: [byte]) -> [byte; count]"
  let boundedOutput : HeaderChange := ⟨"zkc/hash.zkc", output, output ++ " where (2 <= count)"⟩
  let field := "`bool` is not of sort `Field`, which `T` of `copy` requires"
  let cases : List (String × Option HeaderChange × String × String) := [
    (boundedCopy, none, "SP4", "`copy` requires `minimum <= n`, which is `2 <= 1`"),
    (fieldCopy ++ "M::copy<bool>(x)", none, "SP3", field),
    (fieldCopy ++ "M::copy(x)", none, "SP3", field),
    (groupEqual, none, "SP3", "is not of sort `Field`, which `T` of `eq` requires"),
    (sized, none, "SP4", "`copy` requires `2 <= Self::Size`, which is `2 <= 1`"),
    (shake, some boundedOutput, "SP4", "`output` requires `2 <= count`, which is `2 <= 1`")]
  for (source, header, rule, message) in cases do
    let session ← memberSession repository source header
    let file := header.map (fun h => (repository.libraries / h.library).toString) |>.getD "caller"
    let refused := session.diagnostics.any fun d => d.isError && d.rule == rule &&
      d.span.file == file && (d.render session.state.env.renderer).contains message
    expectTrue (refused && ((session.admitRoots (some #["evaluate"])).complete matches .error _))
      s!"{source.splitOn "\n" |>.getLast!}: expected {rule} ({message}); got {session.renderDiagnostics}"

  -- The opaque type has the Group sort. Its order becomes available at the concrete call.
  let orderCall (condition : String) := "module caller
use zkc::algebra::{Group}
use zkc::curves::bls12_381::{G1}
interface Carrier:
    type Element: Group
module Points: Carrier:
    type Element = G1
interface I:
    def copy<T: Group>(x: T) -> T where (" ++ condition ++ ")
module M: I:
    def copy(x): x
def copyValue<T: Group>(x: T) -> T: M::copy(x)
def selected<C: Carrier>(x: C::Element) -> C::Element: copyValue(x)
def evaluate(x: G1) -> G1: selected<Points>(x)"
  let holds ← memberSession repository (orderCall "2 <= T::Order")
  let fails ← memberSession repository (orderCall "T::Order <= 2")
  let rejected := fails.diagnostics.any fun d => d.isError && d.rule == "SP4" &&
    (d.render fails.state.env.renderer).contains "`copy` requires `T::Order <= 2`"
  expectTrue (((holds.admitRoots (some #["evaluate"])).complete matches .ok _) && rejected &&
    ((fails.admitRoots (some #["evaluate"])).complete matches .error _))
    s!"expected the concrete order to decide both constraints: {holds.renderDiagnostics}; {fails.renderDiagnostics}"

def memberRowSuite (repository : Repository) : TestM Unit := do
  memberParameterSuite repository
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
