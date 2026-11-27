module

public import Zkc.Frontend.Written.Claim
public import Zkc.Frontend.Written.Package

public section
set_option autoImplicit false

/-!
Issue the typed subject of the retained goals of one scheme. First occurrence fixes table
order. Public names follow selector spellings, fields follow resolved goal declarations, and
decisions follow the source clause position and its instantiated relation in this package.
-/

namespace Zkc.Frontend.Written
open Zkc.Subject.Print

/-- Retain the first occurrence of each public selector after the route has selected its goals. -/
def uniqueGoalSpellings (goals : List ClaimedGoal) : List ClaimedGoal := Id.run do
  let mut seen : Std.HashSet String := {}
  let mut ordered := #[]
  for goal in goals do
    unless seen.contains goal.goal do
      seen := seen.insert goal.goal
      ordered := ordered.push goal
  return ordered.toList

/-- The first-use order for a shared module. Each alias carries its goal index; each
canonical goal carries its decision index. -/
structure SubjectLayout (owner : GoalClaims) where
  private mk ::
  private aliases : Array (ClaimedGoal × Nat)
  private goals : Array (ClaimedGoal × Nat)
  private decisions : Array ClaimedGoal
  private functions : Array InstanceId

namespace SubjectLayout

variable {owner : GoalClaims}

/-- Index the successful occurrences in their original order, within one compiled scheme. -/
def ofGoals (owner : GoalClaims) (retained := owner.goals.attach) : SubjectLayout owner := Id.run do
  let mut aliases := #[]
  let mut spellings : Std.HashSet String := {}
  let mut goals := #[]
  let mut byDeclaration : Std.HashMap DeclarationId Nat := {}
  let mut decisions := #[]
  let mut byClause : Std.HashMap (Nat × InstanceId) Nat := {}
  let mut functions := #[]
  let mut seenFunctions : Std.HashSet InstanceId := {}
  for ⟨goal, _⟩ in retained do
    if spellings.contains goal.goal then continue
    spellings := spellings.insert goal.goal
    let mut goalIndex := goals.size
    if let some index := byDeclaration[goal.declaration]? then
      goalIndex := index
    else
      let clause := (goal.clause.place, goal.relation)
      let mut decisionIndex := decisions.size
      if let some index := byClause[clause]? then
        decisionIndex := index
      else
        byClause := byClause.insert clause decisionIndex
        decisions := decisions.push goal
        unless seenFunctions.contains goal.relation do
          seenFunctions := seenFunctions.insert goal.relation
          functions := functions.push goal.relation
      byDeclaration := byDeclaration.insert goal.declaration goalIndex
      goals := goals.push (goal, decisionIndex)
    aliases := aliases.push (goal, goalIndex)
  return ⟨aliases, goals, decisions, functions⟩

/-- The goals to publish, one per original selector spelling. -/
def publicGoals (layout : SubjectLayout owner) : List ClaimedGoal := layout.aliases.toList.map Prod.fst

private def goalName (index : Nat) := s!"written'goal{index}"
private def fieldsName (index : Nat) := s!"written'fields{index}"
private def capsName (index : Nat) := s!"written'caps{index}"
private def boundName (index : Nat) := s!"written'bound{index}"
private def decisionName (index : Nat) := s!"written'decision{index}"
private def slotName (index : Nat) := s!"written'slot{index}"

/-- Public spellings paired with their already resolved, row-local goal. -/
def namedGoals (layout : SubjectLayout owner) : Array (ClaimedGoal × String) :=
  layout.aliases.map fun (goal, index) => (goal, goalName index)

/-- Emit the complete fields once per declaration. The existing author-facing cap and
argument names use the same values at every spelling. A named cap preserves the term used
by an author's rewrite under the public cap abbreviation. -/
def goalFacts (layout : SubjectLayout owner) (label : ClaimedGoal → String) : String := Id.run do
  let mut lines := #[]
  for ((goal, _), i) in layout.goals.toList.zipIdx do
    let bound := goal.bound
    lines := lines.push (s!"def {capsName i} : Zkc.Subject.CapTable := {capsTerm goal.caps}\n" ++
      s!"def {boundName i} : Zkc.Subject.Bound := ⟨{bound.num.toNat}, {bound.den}, by decide⟩\n" ++
      s!"def {fieldsName i} : Zkc.Subject.GoalFields :=\n" ++
      s!"  \{ specification := {numbers goal.specification.toList}, caps := {capsName i}, " ++
      s!"bound := {boundName i} }\n")
  for (goal, i) in layout.aliases do
    let name := label goal
    lines := lines.push s!"abbrev {name}Caps : Zkc.Subject.CapTable := {capsName i}\n"
    for j in [:goal.specification.size] do
      lines := lines.push (s!"def {name}Argument{j} : Nat := " ++
        s!"{fieldsName i}.specification[{j}]'(by decide)\n")
  return String.join lines.toList

/-- One physical member per distinct function in the installed program, with the existing
public relation facts at each spelling. The caller also emits the package's transfer proofs. -/
def relationFacts (layout : SubjectLayout owner) (relationLabel : ClaimedGoal → String)
    (memberOf : Nat → String) : String := Id.run do
  let mut lines := #[]
  for k in layout.functions do
    lines := lines.push (s!"noncomputable def member'fn{k} : " ++
      s!"Member installed.headers.fns header{k} :=\n  {memberOf k}\n")
  for (goal, _) in layout.aliases do
    let name := relationLabel goal
    let k := goal.relation
    lines := lines.push (s!"abbrev {name}Key : Key := stored{k}.key\n" ++
      s!"noncomputable abbrev {name}Header := header{k}\n" ++
      s!"noncomputable abbrev {name}Member := member'fn{k}\n")
  return String.join lines.toList

/-- The member fixes the full deployed position and its type and holders in the root header.
The two proofs are checked against that position's actual holders and the root's roles. -/
private def portTerm (shared : Bool) (position : Nat) : String :=
  let port := s!"⟨_, {memberAt position}⟩"
  if shared then s!"⟨{port}, by decide +kernel, by decide +kernel⟩" else port

private def operandsText (shared : Bool) (positions : Array Nat) : String :=
  consList (positions.toList.map (portTerm shared))

/-- The decision's short application: the relation, the arity, the Boolean result, the statement
operands. A statement that is made over a short application names this constant and not the
decision; the present published family reads it through the goal's decision. -/
private def applicationText (goal : ClaimedGoal) (i : Nat) : String :=
  s!"noncomputable def written'application{i} : Zkc.Subject.ShortApplication written'root :=\n" ++
    s!"  ⟨written'fn{goal.relation}, ⟨{goal.statement.size}, by decide +kernel⟩, rfl,\n" ++
    s!"   {operandsText true goal.statement}⟩\n"

/-- The decision: its short application, its place in the source contract and its witness operands. -/
private def decisionText (goal : ClaimedGoal) (i : Nat) : String :=
  s!"noncomputable def {decisionName i} : Zkc.Subject.Decision written'root :=\n" ++
    s!"  ⟨written'application{i}, {goal.clause.place}, {option (operandsText false) goal.witness}⟩\n"

/-- Select a named leaf by its absolute position. Splitting on the middle position keeps
each projection logarithmic, including projection of the last row. -/
private def selector (row : Nat → String) (first : Nat) (count : Nat) : String :=
  if count ≤ 1 then row first
  else
    let half := count / 2
    let middle := first + half
    s!"(if i.val < {middle} then {selector row first half} " ++
      s!"else {selector row middle (count - half)})"
termination_by count
decreasing_by all_goals omega

private def tableTerm (row : Nat → String) (count : Nat) : String :=
  match count with
  | 0 => "⟨0, Fin.elim0⟩"
  | 1 => s!"⟨1, fun _ => {row 0}⟩"
  | n + 2 => s!"⟨{n + 2}, fun i => {selector row 0 (n + 2)}⟩"

/-- Close the typed subject over the package, physical members, role facts and lookup proofs
already in scope. Mathematical issuance supports deciding proofs of soundness. -/
def text (layout : SubjectLayout owner) : Except String String := do
  let program := owner.state.program
  let some scheme := program.declarations[owner.scheme]? | throw "missing source scheme declaration"
  let some file := program.files[scheme.file]? | throw "missing defining file of the source scheme"
  let mut lines := #[
    "noncomputable def written'root : Zkc.Subject.WrittenRoot subjectPackage :=\n" ++
      "  ⟨⟨rootHeader, rootMember, found'root⟩, ⟨proverRole, by decide +kernel⟩,\n" ++
      "   ⟨verifierRole, by decide +kernel⟩, by decide +kernel⟩\n",
    "noncomputable def written'origins : Zkc.Subject.RootOrigins written'root :=\n" ++
      s!"  ⟨{reprStr file.path}, {reprStr (Static.qualifiedName program owner.scheme)}, #{list (owner.inputs.toList.map reprStr)}, rfl⟩\n"]
  for k in layout.functions do
    lines := lines.push (s!"noncomputable def written'fn{k} : " ++
      s!"Zkc.Subject.FunctionEntry subjectPackage := ⟨header{k}, member'fn{k}, found'fn{k}⟩\n")
  for (goal, i) in layout.decisions.toList.zipIdx do
    unless goal.clause.kind == .proves do
      throw (s!"{goal.goal}: the goal reads a `reduces` clause. The statement of a reduction " ++
        "is about a return on which the reduced statement is true, and is not issued yet")
    lines := lines.push (applicationText goal i)
  for (goal, i) in layout.decisions.toList.zipIdx do
    lines := lines.push (decisionText goal i)
  lines := lines.push ("noncomputable def written'clauses : " ++
    "Zkc.Subject.BoundedTable (Zkc.Subject.Decision written'root) :=\n" ++
    s!"  {tableTerm decisionName layout.decisions.size}\n")
  for ((goal, d), i) in layout.goals.toList.zipIdx do
    let path := (Static.qualifiedName program goal.declaration).splitOn "::"
    lines := lines.push (s!"noncomputable def {goalName i} : Zkc.Subject.WrittenGoal " ++
      s!"written'root := ⟨{decisionName d}, {fieldsName i}⟩\n" ++
      s!"noncomputable def {slotName i} : Zkc.Subject.GoalSlot written'clauses.size :=\n" ++
      s!"  \{ path := {reprStr path}, property := {reprStr goal.property}, " ++
      s!"clause := ⟨{d}, by decide⟩, fields := {fieldsName i} }\n")
  lines := lines.push ("noncomputable def written'subject : " ++
    "Zkc.Subject.WrittenSubject written'root :=\n" ++
    s!"  ⟨written'clauses, {tableTerm slotName layout.goals.size}, written'origins⟩\n")
  for i in [:layout.goals.size] do
    lines := lines.push (s!"theorem written'goalAt{i} : " ++
      s!"written'subject.goalAt ⟨{i}, by decide⟩ = {goalName i} := rfl\n")
  return String.join lines.toList

end SubjectLayout
end Zkc.Frontend.Written
