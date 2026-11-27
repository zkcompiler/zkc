import Zkc.Tests.Frontend.PrintedPackageSupport
import Zkc.Tests.Frontend.SourceClause

/-! Expected selections for an independent consumer of the issued statements. Read the
original lowered ports and clause operands before observing any generated declaration. -/

namespace ZkcFormalTests.WrittenSource
open Zkc.Frontend Zkc.Frontend.Written
open Zkc.Tests.Frontend Zkc.Tests.Frontend.PrintedPackageSupport

private def position (ports : Array Lowered.Port) (e : Lowered.Expr) : Except String Nat := do
  let .local _ id := e | throw "expected a source port reference"
  let some index := ports.findIdx? (·.binder.id == id) | throw "operand is outside the deployed ports"
  return index

private def equation (lhs rhs : String) := s!"example : {lhs} = {rhs} := rfl\n"

/-- Each request gives the selector to resolve and the public spelling the client expects.
Two distinct spellings may belong to one source declaration. The ordinary charge subjects
have simple public names. Fixtures for escaped labels specify the expected spelling literally. -/
def consumerAt (root : AdmittedRoot) (requests : List (String × String)) : Except String String := do
  let some (first, _) := requests.head? | throw "expected a goal"
  let compiled ← goalClaims root (requests.map Prod.fst)
  let head ← SourceClause.rootHead root
  let ports := head.ports.filter (!·.specification)
  let (selected, _) ← root.goalSource.selectNamed first .soundness
  let some scheme := root.state.program.declarations[selected.scheme.declaration]?
    | throw "unknown selected scheme"
  let some file := root.state.program.files[scheme.file]? | throw "unknown defining module"
  let (prover, verifier) ← schemeParties root selected.scheme
  let mut text := equation "written'root.entry.header.key.number" (toString root.id) ++
    equation "(written'root.prover.val, written'root.verifier.val)" s!"({prover}, {verifier})" ++
    equation "written'origins.schemeFileModule" (reprStr file.path) ++
    equation "written'origins.schemePath" (reprStr selected.schemePath) ++
    equation "written'origins.inputNames" (reprStr (ports.map (·.binder.name)))
  let mut declarations : Array DeclarationId := #[]
  let mut decisions : Array (Nat × InstanceId) := #[]
  let mut labels : List String := []
  for (selector, label) in requests do
    let (id, _) ← selectDeclaration root.state .goal selector "source comparison"
    if labels.contains label then continue
    labels := label :: labels
    let (goal, _) ← root.goalSource.selectId id .soundness
    let clause ← goalClause root selector
    let some app := clause.application | throw "expected a deciding relation"
    let some decl := root.state.program.declarations[app.relation]? | throw "unknown source relation"
    let .relation node := decl.node | throw "the clause does not select a relation"
    let statement ← app.statement.mapM (position ports)
    let witness ← if (node.witness.getD #[]).isEmpty || !app.witness.isEmpty then
        some <$> app.witness.mapM (position ports)
      else pure none
    let (typed, _) ← evaluate compiled.state clause.span
      (Typing.typedClauses root.id goal.specification (only := some clause.place))
    let some (_, .apply _ (.instance relation) _) := typed.find? (·.1 == clause.place)
      | throw "missing instantiated relation at the selected source clause"
    unless (compiled.state.results.key? relation).map (·.declaration) == some app.relation do
      throw "the instance belongs to another source relation"
    let index := (declarations.findIdx? (· == id)).getD declarations.size
    if index == declarations.size then declarations := declarations.push id
    let key := (clause.place, relation)
    let d := (decisions.findIdx? (· == key)).getD decisions.size
    if d == decisions.size then decisions := decisions.push key
    let (table, _) ← goalCaps root goal.specification
    let caps := table.toOption
    -- the reader's own reading of the rule: the ceiling that the goal writes, else the total of
    -- its table, which a goal without a ceiling has
    let bound : Rat ← match goal.ceiling, caps with
      | some ceiling, _ => pure ceiling
      | none, some table => pure table.ratio
      | none, none => throw "a goal without a ceiling has no table of caps"
    let row := s!"written'goal{index}"
    let atIndex := s!"(written'subject.goalAt ⟨{index}, by decide⟩)"
    text := text ++ equation atIndex row ++
      equation s!"(written'subject.goals.get ⟨{index}, by decide⟩).clause.val" (toString d) ++
      -- the row's path is the path of the goal's declaration, and its property is the goal's
      equation s!"(written'subject.goals.get ⟨{index}, by decide⟩).path"
        (reprStr ((Static.qualifiedName root.state.program id).splitOn "::")) ++
      equation s!"(written'subject.goals.get ⟨{index}, by decide⟩).property" (reprStr goal.property) ++
      equation s!"ZkcFormalTests.WrittenBinding.operands {atIndex}"
        s!"({clause.place}, {relation}, {statement.size}, {reprStr statement.toList}, {reprStr (witness.map Array.toList)})" ++
      equation s!"{atIndex}.fields.specification" (reprStr goal.specification.toList) ++
      equation s!"{atIndex}.fields.caps" (match caps with
        | some table => s!"some ({Zkc.Subject.Print.capsTerm table})"
        | none => "none") ++
      equation s!"{atIndex}.fields.ceiling" (toString goal.ceiling.isSome) ++
      equation s!"({atIndex}.fields.bound.numerator, {atIndex}.fields.bound.denominator)"
        s!"({bound.num.toNat}, {bound.den})" ++
      s!"run_cmd ZkcFormalTests.WrittenBinding.checkReferences (← Lean.getCurrNamespace) {reprStr label} {index} {d} {relation} {goal.specification.size}\n"
    for (argument, i) in goal.specification.toList.zipIdx do
      text := text ++ equation s!"{label}Argument{i}" (toString argument)
  return text ++ equation "written'subject.clauses.size" (toString decisions.size) ++
    equation "written'subject.goals.size" (toString declarations.size)

/-- Assemble the original single-file source before observing the issued module. -/
def consumer (source : String) (requests : List (String × String)) : Except String String := do
  let some (first, _) := requests.head? | throw "expected a goal"
  consumerAt (← goalRoot source first) requests

end ZkcFormalTests.WrittenSource
