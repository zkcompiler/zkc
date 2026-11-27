import Zkc.Tests.Frontend.PrintedPackageSupport
import Zkc.Tests.Frontend.SourceClause

/-! Expected selections for an independent consumer of the issued statements. Read the
original lowered ports and clause operands before observing any generated declaration.

What is this reader's own: the ports, the clause's operands and place, the rule of a goal's
bound (the ceiling, else the table's total). What is not: the table of caps is the frontend's
(`goalCaps`), the function that the issuer calls, so a charge read at another site with the
same total passes this comparison. What each site is charged is held by expectations written
by hand in `checks/GoalStatement.lean` (two draws with exchanged charges and one total, a
callee at two proof arguments, the arms of a choice, a call in a loop). -/

namespace ZkcFormalTests.WrittenSource
open Zkc.Frontend Zkc.Frontend.Written
open Zkc.Tests.Frontend Zkc.Tests.Frontend.PrintedPackageSupport

private def position (ports : Array Lowered.Port) (e : Lowered.Expr) : Except String Nat := do
  let .local _ id := e | throw "expected a source port reference"
  let some index := ports.findIdx? (·.binder.id == id) | throw "operand is outside the deployed ports"
  return index

private def equation (lhs rhs : String) := s!"example : {lhs} = {rhs} := rfl\n"

/-- Each request is a selector to resolve. Two selectors may belong to one source declaration,
which is one row. -/
def consumerAt (root : AdmittedRoot) (requests : List String) : Except String String := do
  let some first := requests.head? | throw "expected a goal"
  let compiled ← goalClaims root requests
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
  for selector in requests do
    let (id, _) ← selectDeclaration root.state .goal selector "source comparison"
    -- two selectors of one declaration are one row
    if declarations.contains id then continue
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
    let table ← goalCaps root goal.specification
    let caps := table.toOption
    -- the reader's own reading of the rule: the ceiling that the goal writes, else the total of
    -- its table, which a goal without a ceiling has
    let bound : Rat ← match goal.ceiling, caps with
      | some ceiling, _ => pure ceiling
      | none, some table => pure table.ratio
      | none, none => throw "a goal without a ceiling has no table of caps"
    let atIndex := s!"(written'subject.goals.get ⟨{index}, by decide⟩)"
    text := text ++
      equation s!"(written'subject.goals.get ⟨{index}, by decide⟩).clause.val" (toString d) ++
      -- the row's path is the path of the goal's declaration, and its property is the goal's
      equation s!"(written'subject.goals.get ⟨{index}, by decide⟩).path"
        (reprStr ((Static.qualifiedName root.state.program id).splitOn "::")) ++
      equation s!"(written'subject.goals.get ⟨{index}, by decide⟩).property" (reprStr goal.property) ++
      equation s!"ZkcFormalTests.WrittenBinding.operands (written'subject.clauses.get {atIndex}.clause)"
        s!"({clause.place}, {relation}, {statement.size}, {reprStr statement.toList}, {reprStr (witness.map Array.toList)})" ++
      equation s!"{atIndex}.fields.specification" (reprStr goal.specification.toList) ++
      equation s!"{atIndex}.fields.number.caps" (match caps with
        | some table => s!"some ({Zkc.Subject.Print.capsTerm table})"
        | none => "none") ++
      equation s!"{atIndex}.fields.number.written" (toString goal.ceiling.isSome) ++
      equation s!"({atIndex}.fields.number.bound.numerator, {atIndex}.fields.number.bound.denominator)"
        s!"({bound.num.toNat}, {bound.den})" ++
      s!"run_cmd ZkcFormalTests.WrittenBinding.checkReferences (← Lean.getCurrNamespace) {index} {d} {relation}\n"
  return text ++ equation "written'subject.clauses.size" (toString decisions.size) ++
    equation "written'subject.goals.size" (toString declarations.size)

/-- Assemble the original single-file source before observing the issued module. -/
def consumer (source : String) (requests : List String) : Except String String := do
  let some first := requests.head? | throw "expected a goal"
  consumerAt (← goalRoot source first) requests

end ZkcFormalTests.WrittenSource
