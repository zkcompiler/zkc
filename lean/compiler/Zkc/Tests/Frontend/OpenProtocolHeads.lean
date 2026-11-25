import Zkc.Tests.Frontend.TypingReference
import Zkc.Frontend.Written.Goals

namespace Zkc.Tests.Frontend
open Zkc.Frontend

private inductive HeadOutcome where
  | admitted
  | differs (part : String)
  | waits (reason : String)

private def goalSource (name guard : String) : String :=
  s!"protocol {name} roles(P,V)(x: bool @(P,V)):\n    guard @V {guard}\n" ++
  s!"spec for {name}:\n    proves @V Holds(x)\n" ++
  s!"scheme {name}Scheme = {name}:\n    prover P\n    construction interactive\n" ++
  s!"goal {name}Goal = soundness({name}Scheme)\n"

/-- Select only the sibling helper. The generic protocol is never directly instantiated.
Check both roots and issue both named goals, including the independent one. -/
def openProtocolHeadsSuite (repository : Repository) : TestM Unit := do
  let load ← cachedLoader #[repository.libraries]
  let check (promised supplied : String) (outcome : HeadOutcome) (preamble := "")
      (interfaceParams := "") (interfaceArgs := "") (extra := "")
      (imports : Array (String × String) := #[]) : TestM Unit := do
    let text := "module heads\nuse zkc::security::{soundness}\n" ++ preamble ++
      s!"interface Has{interfaceParams}:\n    protocol Do{promised}\n" ++
      s!"module M<n: nat>: Has{interfaceArgs}:\n" ++ extra ++
      s!"    protocol Do{supplied}:\n        guard @V true\n" ++
      "    pub def helper(x: bool) -> bool: x\nrelation Holds(x: bool): x\n" ++
      goalSource "Using" "M<1>::helper(x)" ++ goalSource "Independent" "x"
    let inputs : Array SourceInput := #[⟨"heads", Syntax.parseString "heads" text⟩] ++
      imports.map fun (name, source) => ⟨name, Syntax.parseString name source⟩
    let assembly ← liftM <| assemble inputs load
    let session := Driver.Session.start.runAll (Driver.pipeline assembly)
    let roots := session.admitRoots (some #["Using", "Independent"])
    let goals := Written.issueSoundnessGoals assembly ["UsingGoal", "IndependentGoal"]
    let independent := roots.held.any (·.1 == "Independent") && goals[1]?.any (·.outcome.isOk)
    let held := roots.held.any (·.1 == "Using")
    let messages := goals.map fun g => match g.outcome with
      | .ok _ => "issued"
      | .error why => why
    let ok := match outcome, (goals[0]?.map (·.outcome)).getD (.error "missing goal") with
      | .admitted, .ok _ => held && roots.complete.isOk
      | .differs part, .error why => !held && why.contains part &&
        session.diagnostics.any (fun d => d.rule == "SP8" && d.span.file == "heads" &&
          (d.render session.state.env.renderer).contains part)
      | .waits reason, .error why => !held && !session.hasErrors &&
        why.contains reason && roots.lackingLines.any (·.contains reason)
      | _, _ => false
    expectTrue (independent && ok)
      s!"{text}{session.renderDiagnostics}\n{roots.lackingLines}\n{messages}"

  let port (type : String) (params := "<k: nat>") := s!"{params} roles(P,V)(x: {type} @(P,V))"
  let sized (n : String) := port s!"[bool; {n}]"
  let wrong := HeadOutcome.differs "port `x`"
  check (sized "k") (sized "k") .admitted
  check (sized "k") (port "[nat; k]") wrong
  check (sized "k") (sized "k + 1") wrong
  check (sized "k + 1") (sized "k") wrong
  check (sized "k") (sized "k + 0") .admitted
  check (sized "k * 2") (sized "k + k") .admitted
  check (sized "k + 2") (sized "k * 2") wrong
  check (sized "k * k") (sized "k * (k + 0)") .admitted
  check (sized "k * k") (sized "k ^ 2") (.waits "open protocol head")
  check (sized "k - 1") (sized "k - 1") (.waits "k - 1")
  check (sized "1 + k - 1") (sized "k") .admitted
  check (sized "2 * k - k") (sized "k") .admitted
  check (sized "k - k") (sized "0") .admitted
  check (sized "k ^ 2" ++ " where (k <= 1)") (sized "k * k" ++ " where (k < 1)")
    (.differs "where clause")
  check (port "[nat; k * k]") (sized "k ^ 2") wrong
  check (port "[T; k]" "<T, k: nat>") (port "[T; k]" "<T, k: nat>") .admitted
  check (port "[(T, T); k]" "<T, U, k: nat>") (port "[(T, U); k]" "<T, U, k: nat>") wrong
  check (port "index<k>") (port "nat") wrong
  check (port "[Alias; k]") (sized "k") .admitted "type Alias = bool\n"
  check (port "[Alias; k]") (port "[Alias; k]") wrong "type Alias = bool\n" "" ""
    "    type Alias = nat\n"
  check (sized "k + outer") (sized "n + k") .admitted "" "<outer: nat>" "<n>"
  check (sized "k + outer") (sized "n + k") wrong "" "<outer: nat>" "<n + 1>"
  let result (n : String) := port "bool" ++ s!" -> y: [bool; {n}] @V"
  check (result "k") (result "k + 1") (.differs "result `y`")
  let condition (clause : String) := port "bool" ++ s!" where ({clause})"
  check (condition "k + 1 <= 4") (condition "1 + k <= 2 + 2") .admitted
  check (condition "k + 1 <= 4") (condition "k <= 4") (.differs "where clause")
  check (condition "k <= k + 1") (condition "k <= k + 2") (.differs "where clause")
  check (condition "k <= 4") (condition "k < 4") (.differs "where clause")
  let proofParam (e : String) := port "bool" "<spec e: nat>" ++ s!" where ({e} <= 3)"
  check (proofParam "e + 0") (proofParam "e") .admitted
  check (proofParam "e") (proofParam "e + 1") (.differs "where clause")
  let sorts := "interface Sized<width: nat>:\n    type T\ninterface Other<width: nat>:\n    type T\n"
  let bound (app : String) := port "bool" s!"<k: nat, S: {app}>"
  check (bound "Sized<k>") (bound "Sized<k + 0>") .admitted sorts
  check (bound "Sized<k>") (bound "Sized<k + 1>") (.differs "bound of `S`") sorts
  check (bound "Sized<k>") (bound "Other<k>") (.differs "bound of `S`") sorts
  let two := "interface Pair<a: nat, b: nat>:\n    type T\n"
  check (bound "Pair<a=k,b=k+1>") (bound "Pair<b=k+1,a=k>") .admitted two
  check (bound "Pair<a=k,b=k+1>") (bound "Pair<b=k,a=k+1>") (.differs "bound of `S`") two
  let foreign (name : String) := s!"module {name}\npub interface Limit<n: nat>:\n    type T\n"
  let imports := #[("left", foreign "left"), ("right", foreign "right")]
  let qualified := "use left\nuse right\nuse left::{Limit}\n"
  check (bound "left::Limit<k>") (bound "Limit<k>") .admitted qualified "" "" "" imports
  check (bound "left::Limit<k>") (bound "right::Limit<k>") (.differs "bound of `S`")
    qualified "" "" "" imports
  let whereBound (width : String) := bound "Sized<k>" ++ s!" where (S: Sized<{width}>)"
  check (whereBound "k") (whereBound "k + 0") .admitted sorts
  check (whereBound "k") (whereBound "k + 1") (.differs "where clause") sorts
  let libs := "use zkc::suites::{Merlin3Bls12381}\nuse zkc::construction::{Suite}\n"
  let waiting := port "([bool; k], S::Units::Unit)"
  check waiting (port "([bool; k], bool)") (.waits "Units") libs "<S: Suite>" "<Merlin3Bls12381>"
  check (port "([bool; k], bool)") (port "([bool; k], Merlin3Bls12381::Units::Unit)")
    (.waits "Units") libs

end Zkc.Tests.Frontend
