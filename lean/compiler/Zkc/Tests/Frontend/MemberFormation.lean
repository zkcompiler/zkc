import Zkc.Tests.Frontend.TypingReference

namespace Zkc.Tests.Frontend

open Zkc.Frontend

/-- A sibling selection must validate the interface at this module's concrete arguments. -/
private def selected (interfaces implementation : String) (root : String := "") : String :=
  "module formation\n" ++ interfaces ++ "\n" ++ implementation ++ "\n" ++
    "    pub def helper(x: bool) -> bool: x\n" ++ root ++
    "def evaluate(x: bool) -> bool: M<1>::helper(x)\n"

def memberFormationSuite (repository : Repository) : TestM Unit := do
  let load ← cachedLoader #[repository.libraries]
  let check (source : String) (diagnostic : Option String) : TestM Unit := do
    let session ← liftM <| Driver.Session.start.compile #[⟨"formation", Syntax.parseString "formation" source⟩] load
    let errors := session.diagnostics.filter (·.isError)
    let admitted := (session.admitRoots (some #["evaluate"])).complete.isOk
    let ok := match diagnostic with
      | none => admitted && errors.isEmpty
      | some text => !admitted && errors.any fun d =>
        d.rule == "SP8" && d.span.file == "formation" &&
          (d.render session.state.env.renderer).contains text
    expectTrue ok s!"{source}expected {diagnostic}, admitted={admitted}: {session.renderDiagnostics}"

  let carrier (bound value : String) (family : String := "") (root : String := "") :=
    selected ("type F = primitive(\"koala-bear\")\ninterface Has:\n    type T" ++ family ++ ": " ++ bound)
      ("module M<n: nat>: Has:\n    type T" ++ family ++ " = " ++ value) root
  check (carrier "Field" "bool") (some "not of sort `Field`")
  check (carrier "Field" "F") none
  check (carrier "Field<1>" "F") (some "the sort `Field` takes no static arguments")
  check (carrier "Ring + Field" "[F; n]") (some "not of sort `Ring`")
  check (carrier "Group + Field" "[F; n]") (some "not of sort `Field`")
  check (carrier "Group" "[F; n]") none
  check (carrier "Field" "[F; n]") (some "not of sort `Field`")
  check (carrier "Field" "U" "<U>" "def project(x: M<1>::T<bool>) -> bool: x\n")
    (some "not of sort `Field`")
  check (carrier "Field" "U" "<U>" "def project(x: M<1>::T<F>) -> F: x\n") none

  check (carrier "nat" "bool") (some "cannot satisfy the bound `nat`")
  check (carrier "linear" "bool") none
  let unrelated := "interface Marker\n" ++ "interface Has:\n    type T: Marker"
  check (selected unrelated "module M<n: nat>: Has:\n    type T = bool")
    (some "is not a type sort")
  let eligible := "module formation\ninterface Has<k: nat> where (3 < k):\n    type T: Field\n" ++
    "pub module M<n: nat>: Has<n>:\n    type T = bool\ndef evaluate() -> bool: true\n"
  check eligible none
  check (eligible ++ "// instantiate: M<4>\n") (some "not of sort `Field`")

  let predicate := "module formation\ntype F = primitive(\"koala-bear\")\n" ++
    "interface Has where (Self::T<bool> == F):\n    type T<U>: Field\n" ++
    "pub module M<n: nat>: Has:\n    type T<U> = U\ndef evaluate() -> bool: true\n"
  check predicate none
  check (predicate.replace "== F" "== bool") (some "not of sort `Field`")
  check (predicate.replace "type T<U> = U" "type T<U> = F") none

  let protocolCase (decl impl : String) (body : String := "guard @V true") :=
    selected ("interface Has<U>:\n    type T\n    protocol Run" ++ decl)
      ("module M<n: nat>: Has<[bool; n]>:\n    protocol Run" ++ impl ++
        ":\n        " ++ body ++ "\n    type T = bool")
  let ports := " roles(P,V)(x: bool @(P,V))"
  check (protocolCase ports ports) none
  check (protocolCase ports (ports.replace "bool" "(bool, bool)")) (some "port `x`")
  check (protocolCase ports (ports.replace "roles(P,V)" "roles(V,P)")) (some "role roster")
  check (protocolCase ports (ports.replace "@(P,V)" "@V")) (some "port `x`")
  check (protocolCase ports (ports.replace "x: " "y: ")) (some "port `x`")
  check (protocolCase ports (ports.replace "@(P,V)" "@(P,V) private")) (some "port `x`")
  check (protocolCase ports (ports.replace "x: bool @(P,V)" "spec x: bool")) (some "port `x`")
  check (protocolCase ports (ports.replace "x: bool @" "x: bool @P, y: bool @")) (some "port count")
  check (protocolCase (ports ++ " -> y: bool @V") ports) (some "result count")
  check (protocolCase (ports ++ " -> y: bool @V") (ports ++ " -> y: nat @V") "return 0")
    (some "result `y`")
  check (protocolCase (ports.replace "bool" "U") (ports.replace "bool" "[bool]")) (some "port `x`")
  check (protocolCase (ports.replace "bool" "[bool]") (ports.replace "bool" "[bool; n]"))
    (some "port `x`")
  check (protocolCase (ports.replace "bool" "U") (ports.replace "bool" "[bool; n]")) none
  check (protocolCase (ports.replace "bool" "Self::T") (ports.replace "@(P,V)" "@(V,P)")) none
  check (protocolCase ("<k: nat>" ++ ports) ports) (some "static parameter count")
  check (protocolCase ("<k: Field>" ++ ports) ("<k: Group>" ++ ports)) (some "bound of `k`")
  check (protocolCase ("<k: Field>" ++ ports) ("<k: Field>" ++ ports)) none
  check (protocolCase ports (ports ++ " where (n == 1)")) (some "where clause")

  check (protocolCase (ports ++ " -> y: bool @V") (ports ++ " -> y: bool @P") "return true")
    (some "result `y`")
  check (protocolCase ("<k: nat>" ++ ports) ("<j: nat>" ++ ports)) (some "static parameter")
  check (protocolCase ("<k: nat>" ++ ports ++ " where (k <= 3)")
    ("<k: nat>" ++ ports ++ " where (k <= 4)")) (some "where clause")
  check (protocolCase ("<k: nat>" ++ ports ++ " where (k <= 3)")
    ("<k: nat>" ++ ports ++ " where (k <= 3)")) none
  check (protocolCase ("<k: nat>" ++ ports.replace "bool" "[bool; k]")
    ("<k: nat>" ++ ports.replace "bool" "[nat; k]")) (some "port `x`")
  check (protocolCase (ports.replace "bool" "(left: bool, right: bool)")
    (ports.replace "bool" "(bool, bool)")) none

  let family (width : String) := selected
    "interface Has:\n    protocol Run<k: nat> roles(P,V)(x: [bool; k] @V)"
    ("module M<n: nat>: Has:\n    protocol Run<k: nat> roles(P,V)(x: [bool; " ++ width ++
      "] @V):\n        guard @V true")
    "// instantiate: M<1>::Run<3>\n"
  check (family "1 + k - 1") none
  check (family "k") none
  check (family "k + 1") (some "port `x`")

end Zkc.Tests.Frontend
