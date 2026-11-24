import Zkc.Frontend.Written.Statement
import Zkc.Tests.Frontend.PrintedPackageSupport
import Zkc.Tests.Frontend.SyntaxHarness

namespace Zkc.Tests.Frontend
open Zkc.Frontend.Written PrintedPackageSupport

/-- Sources with a written soundness goal: five whose package links a primitive of a project,
and three counterparts that link none. -/
private def writtenPrimitiveCases : String := r#"=== direct Boolean primitive | refuse | sound
module t
use zkc::security::{soundness}
def test(x: bool) -> bool = primitive("project.test")
relation Holds(x: bool): x
protocol Check roles(P,V)(x: bool @(P,V)):
    guard @V test(x)
spec for Check:
    proves @V Holds(x)
scheme Checked = Check:
    prover P
    construction interactive
goal sound = soundness(Checked)

=== primitive on a nominal input | refuse | sound
module t
use zkc::security::{soundness}
type Token = primitive("project.token")
def test(x: Token) -> bool = primitive("project.test")
relation Holds(x: bool): x
protocol Check roles(P,V)(x: bool @(P,V), token: Token @(P,V)):
    guard @V test(token)
spec for Check:
    proves @V Holds(x)
scheme Checked = Check:
    prover P
    construction interactive
goal sound = soundness(Checked)

=== primitive beside a scalar draw | refuse | sound
module t
use zkc::security::{soundness}
type F = primitive("bls12-381.fr")
def test(x: bool) -> bool = primitive("project.test")
relation Holds(x: bool): x
protocol Check roles(P,V)(x: bool @(P,V)):
    coin <- draw F from V to P
    guard @V test(x)
spec for Check:
    proves @V Holds(x)
scheme Checked = Check:
    prover P
    construction interactive
goal sound = soundness(Checked)

=== primitive after a protocol call | refuse | sound
module t
use zkc::security::{soundness}
def test(x: bool) -> bool = primitive("project.test")
relation Holds(x: bool): x
protocol Echo roles(P,V)(x: bool @(P,V)) -> y: bool @(P,V):
    return x
protocol Check roles(P,V)(x: bool @(P,V)):
    y <- Echo(x)
    guard @V test(y)
spec for Check:
    proves @V Holds(x)
scheme Checked = Check:
    prover P
    construction interactive
goal sound = soundness(Checked)

=== primitive in a shared callee | refuse | twice
module t
use zkc::security::{soundness}
relation Holds(claim: bool): claim
def same(a: index<4>, b: index<4>) -> bool = primitive("project.same")
protocol Round roles(P, V)(sent: index<4> @P) -> (hit: bool @(P, V), drawn: index<4> @(P, V)):
    x <- send sent from P to V
    r <- draw index<4> from V to P
    return (same(r, x), r)
spec for Round:
    charge sites.r <= 1 / 4
protocol Twice roles(P, V)(claim: bool @(P, V), first: index<4> @P, second: index<4> @P):
    a <- Round(first)
    b <- Round(second)
    guard @V claim or a.hit or b.hit
spec for Twice:
    proves @V Holds(claim)
scheme Checked = Twice:
    prover P
    construction interactive
goal twice = soundness(Checked, stage = written)


=== nominal input with a local implementation | issue | sound
module t
use zkc::security::{soundness}
type Token = primitive("project.token")
def test(x: Token) -> bool: true
relation Holds(x: bool): x
protocol Check roles(P,V)(x: bool @(P,V), token: Token @(P,V)):
    guard @V test(token)
spec for Check:
    proves @V Holds(x)
scheme Checked = Check:
    prover P
    construction interactive
goal sound = soundness(Checked)
"#

/-- Package admission precedes statement issuance. A control may change the model used in a
module, but cannot supply a meaning for a project's primitive. -/
def writtenPrimitiveSuite : TestM Unit := do
  for block in readBlocks writtenPrimitiveCases do
    let result : Except String Statements := do
      let #[source] := block.files | throw "expected one source file"
      let root ← goalRoot source block.note
      let claims ← goalClaims root [block.note]
      return ⟨claims, claims.functionsBeforeRoot⟩
    match result with
    | .error why => failure s!"{block.id}: could not obtain the package: {why}"
    | .ok statements =>
      let proof : ProofText := {text := "", theorems := []}
      let check (issue : Except String Unit) : TestM Unit :=
        match block.expect, issue with
        | "issue", .ok () => pass
        | "refuse", .error message =>
          expectTrue (message.contains "links a project primitive" && message.contains "no model")
            s!"{block.id}: unexpected diagnostic: {message}"
        | _, .error why => failure s!"{block.id}: {why}"
        | _, .ok () => failure s!"{block.id}: issued a statement for a project primitive"
      check ((statements.module "Check" proof).map fun _ => ())
      check ((statements.module "Check" proof (model := standardModelText)).map fun _ => ())
      check ((statements.ceilingModule "Check").map fun _ => ())
      check ((statements.claimsModule "Check").map fun _ => ())
      check ((statements.coverageModule "Check" (model := arithmeticModelText)).map fun _ => ())

end Zkc.Tests.Frontend
