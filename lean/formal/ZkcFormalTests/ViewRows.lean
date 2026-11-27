import Zkc.Tests.Frontend.SourceClause
import Zkc.Tests.Frontend.PrintedPackageSupport
import Zkc.Subject.SourceNames

/-!
The rows that a check gives the reader of names and types (`ZkcFormalTests.ViewReader`), from a
second reading of a source: the protocol's head and the clause's relation as the frontend lowered
them, and the rule of names. They are spelled from neither the subject nor the naming of views.
-/

open Zkc.Frontend Zkc.Frontend.Written Zkc.Tests.Frontend Zkc.Tests.Frontend.PrintedPackageSupport

namespace ZkcFormalTests.ViewRows

/-- **The second reading of the source**: the binders of a source's shape that a view of the
goal gives, as rows of the reader. For each deployed input that the deciding role holds, in the
order of the protocol's ports: its name by the rule of names, and its validity where the
telescope is universal; then a witness for each witness parameter that the declaration of the
clause's relation has, whether the clause writes its witness operands or not. -/
def expectedRows (text goal : String) (existential : Bool) : IO String := do
  let c ← IO.ofExcept (goalRoot text goal)
  let head ← IO.ofExcept (SourceClause.rootHead c)
  let seen ← IO.ofExcept (SourceClause.seen c goal)
  let some role := head.roster.idxOf? seen.role | throw (IO.userError "no deciding role")
  let names := head.ports.map (·.binder.name)
  let mut rows := ""
  for (port, k) in head.ports.toList.zipIdx do
    if port.holders.mask.testBit role then
      let count := (names.filter (· == port.binder.name)).size
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
