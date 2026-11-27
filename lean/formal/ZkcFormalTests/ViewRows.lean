import Zkc.Tests.Frontend.SourceClause
import Zkc.Tests.Frontend.PrintedPackageSupport
import Zkc.Subject.SourceNames

/-!
The rows that a check gives the reader of names and types (`ZkcFormalTests.ViewReader`), from a
second reading of a source: the protocol's head and the declaration of the clause's relation as
the frontend lowered them, and the rule of names. They are spelled from neither the subject nor
the naming of views.

The reading has one rule of its own about deployment: a port that the source marks `spec` is in no
deployed header. It is held to the frontend's on every source that is read: the names and holders
that the reading takes as deployed are compared with the deployed ports of the frontend's typed
protocol, and a difference is an error.
-/

open Zkc.Frontend Zkc.Frontend.Written Zkc.Tests.Frontend Zkc.Tests.Frontend.PrintedPackageSupport

namespace ZkcFormalTests.ViewRows

/-- The ports of a source's head that are deployed, in their order: those that are not `spec`.
Refused where the frontend's typed protocol deploys other names or holders. -/
def deployedPorts (c : AdmittedRoot) : Except String (List Lowered.Port) := do
  let head ← SourceClause.rootHead c
  let deployed := head.ports.toList.filter (!·.specification)
  let some checked := c.state.results.checked? c.id | throw "missing the checked protocol of the root"
  let .protocol body := checked.definition.body | throw "the root is no protocol"
  let typed := body.deployedPorts.toList.map fun port => (port.binder.name, port.holders.mask)
  unless deployed.map (fun port => (port.binder.name, port.holders.mask)) == typed do
    throw s!"the second reading deploys {deployed.map (·.binder.name)}, the frontend {typed.map (·.1)}, or their holders differ"
  return deployed

/-- **The second reading of the source**: the binders of a source's shape that a view of the
goal gives, as rows of the reader. For each deployed port that the deciding role holds, by its
ordinal among the deployed ports: its name by the rule of names, and its validity where the
telescope is universal; then a witness for each witness parameter that the declaration of the
clause's relation has, whether the clause writes its witness operands or not. -/
def expectedRows (text goal : String) (existential : Bool) : IO String := do
  let c ← IO.ofExcept (goalRoot text goal)
  let head ← IO.ofExcept (SourceClause.rootHead c)
  let seen ← IO.ofExcept (SourceClause.seen c goal)
  let some role := head.roster.idxOf? seen.role | throw (IO.userError "no deciding role")
  let deployed ← IO.ofExcept (deployedPorts c)
  let names := deployed.map (·.binder.name)
  let mut rows := ""
  for (port, k) in deployed.zipIdx do
    if port.holders.mask.testBit role then
      let count := (names.filter (· == port.binder.name)).length
      let x := Zkc.Subject.inputBinderName port.binder.name k count
      rows := rows ++ s!"  | {x} := input {k}\n"
      unless existential do rows := rows ++ s!"  | {Zkc.Subject.validBinderName x} := valid {k}\n"
  for i in [:(← IO.ofExcept (SourceClause.witnessParameters c goal)).length] do
    rows := rows ++ s!"  | {Zkc.Subject.witnessBinderName i} := witness {i}\n"
  return rows

/-- A reader module over the modules `imports`: one `#view_reads` for each view, each a view of
the subject's first goal row. -/
def reader (imports : List String) (reads : List (String × String × String)) (before := "") : String :=
  String.join (imports.map (s!"import {·}\n")) ++ "import ZkcFormalTests.ViewReader\n\n" ++ before ++
  String.join (reads.map fun (view, subject, rows) => s!"#view_reads {view} of {subject} at 0\n{rows}")

end ZkcFormalTests.ViewRows
