module

public import Zkc.Frontend.Written.Diagnostic
public import Zkc.Frontend.Syntax.Spans
public import Zkc.Frontend.Driver.Bodies

@[expose] public section
set_option autoImplicit false

namespace Zkc.Frontend.Written
open Syntax

/-- Ordinary protocol bodies resolve generated-member dependencies regardless of query order. -/
def sourceContext : Compile.Context := Typing.withProtocolBodies {vocabulary}

/-- CLI selectors are exclusive. A scheme selects a written clause; a goal asks for every
requirement of the named source property at its selected stage. -/
inductive Request where
  | scheme (name : String) (clause : Option String := none)
  | goal (name : String)

structure Selection where
  scheme : SchemeEntry
  clause : Option String
  schemePath : String
  goal : Option Goal := none
  goalPath : Option String := none

def declarationRef (s : Compile.State) (file : FileId) (path : Path) : ExportM DeclarationId := do
  let some resolution := s.env.modules.resolution? file path | refuse path.span "WK-REF" "unresolved path"
  unless resolution.segments.all (·.staticArgs.isNone) do
    refuse path.span "WK-REF" "explicit or import-fixed static arguments on a clause reference"
  let some (Step.declaration id) := resolution.segments.back?.map (·.step)
    | refuse path.span "WK-REF" "expected a declaration"
  return id

def lastStage (scheme : SchemeEntry) : String :=
  if scheme.lines.any (fun | .construction _ (.derived ..) | .construction _ (.authored ..) => true | _ => false) then
    "serialized"
  else if scheme.lines.any (fun | .commit .. => true | _ => false) then "committed"
  else "written"

/-- An imported scheme is also a root when an entry goal selects it. Reuse ordinary SC1
instantiation in the defining file and retain the resulting table for body elaboration. -/
def goalScheme (s : Compile.State) (file : FileId) (goal : Goal) :
    ExportM (SchemeEntry × Compile.State) := do
  let id ← declarationRef s file goal.scheme
  if let some scheme := s.results.schemes.find? (·.declaration == id) then return (scheme, s)
  let some declaration := s.program.declarations[id]? | refuse goal.scheme.span "WK-GOAL" "missing goal scheme"
  let .scheme node := declaration.node | refuse goal.scheme.span "WK-GOAL" "expected a scheme"
  let (outcome, after) := (Instances.schemeProtocol id declaration.file node).run sourceContext s
  if let some diag := (after.log.entries.extract s.log.entries.size after.log.entries.size).find?
      (fun d => d.isError || d.isIncomplete) then
    refuse goal.scheme.span "WK-GOAL" (diag.render after.env.renderer)
  let .ok _ := outcome | refuse goal.scheme.span "WK-GOAL" "the named scheme could not be closed"
  let some scheme := after.results.schemes.find? (·.declaration == id)
    | refuse goal.scheme.span "WK-GOAL" "the named scheme has no closed instance"
  return (scheme, after)

def selectedGoal (state : Compile.State) (file : FileId) (goal : Goal) (path : String) :
    ExportM (Selection × Compile.State) := do
  let (scheme, s) ← goalScheme state file goal
  let some resolution := s.env.modules.resolution? file goal.property
    | refuse goal.property.span "WK-GOAL" "unresolved formal property"
  let some (Step.entry library property) := resolution.segments.back?.map (·.step)
    | refuse goal.property.span "WK-GOAL" "expected a formal library property"
  unless resolution.segments.all (·.staticArgs.isNone) do
    refuse goal.property.span "WK-GOAL" "this property takes no static arguments"
  let some entry := vocabularyEntry? library property | refuse goal.property.span "WK-GOAL" "unknown property"
  let .property binding := entry.kind | refuse goal.property.span "WK-GOAL" "a security model cannot select a property"
  let mut stage := none
  let mut label := none
  for argument in goal.args do
    let .named span key value := argument | refuse goal.span "WK-GOAL" "unsupported specification argument"
    unless key.text == "stage" || key.text == "clause" do
      refuse span "WK-GOAL" s!"{property}: no written fork theorem covers goal argument {key.text}"
    let .path _ path none := value | refuse span "WK-GOAL" s!"expected one name for {key.text}"
    let some name := path.plainName? | refuse span "WK-GOAL" s!"expected one name for {key.text}"
    if key.text == "stage" then
      if stage.isSome then refuse span "WK-GOAL" "duplicate stage"
      stage := some name.text
    else
      if label.isSome then refuse span "WK-GOAL" "duplicate clause selection"
      label := some name.text
  let requested := stage.getD (lastStage scheme)
  unless requested == "written" do
    refuse goal.span "WK-GOAL" s!"{goal.name.text} requires stage {requested}; only written executions are available"
  unless binding == some .writtenFork do
    refuse goal.property.span "WK-GOAL" s!"no complete theorem for {library}::{property} at {requested}; a two-run knowledge clause supplies special soundness"
  if goal.ceiling.isSome then refuse goal.span "WK-GOAL" "the written fork property has no quantitative ceiling"
  return (⟨scheme, label, Static.qualifiedName s.program scheme.declaration, some goal, some path⟩, s)

/-- A bare name must be unique among input declarations. A qualified name selects the
canonical path, or a path relative to an input file module. -/
def selectDeclaration (s : Compile.State) (kind : DeclarationKind) (name rule : String) :
    ExportM (DeclarationId × String) := do
  let mut candidates := #[]
  for (d, id) in s.program.declarations.zipIdx do
    unless d.kind == kind && Static.inPackage s.program d.file do continue
    let path := Static.qualifiedName s.program id
    if path == name then return (id, path)
    let root := pathText s.program.files[d.file]!.path
    if s.program.nameOf id == name || (path.dropPrefix (root ++ "::")).toString == name then
      candidates := candidates.push (id, path)
  match candidates with
  | #[(id, path)] => return (id, path)
  | #[] => throw s!"{rule}: no matching declaration named {name} in the input modules"
  | many => throw s!"{rule}: ambiguous {name}; select one of {", ".intercalate (many.toList.map Prod.snd)}"

def select (s : Compile.State) : Request → ExportM (Selection × Compile.State)
  | .scheme name label => do
    let (id, path) ← selectDeclaration s .scheme name "WK-ROOT"
    let some scheme := s.results.schemes.find? (·.declaration == id)
      | throw s!"WK-ROOT: no closed scheme for {path}"
    return (⟨scheme, label, path, none, none⟩, s)
  | .goal name => do
    let (id, path) ← selectDeclaration s .goal name "WK-GOAL"
    let d := s.program.declarations[id]!
    let .goal goal := d.node | throw "WK-GOAL: missing goal declaration"
    selectedGoal s d.file goal path

structure ClauseSource where
  where_ : Span
  file : FileId
  rel : Path
  operands : Array LocalId
  extractor : Path
  label : Option String
  /-- Kind, optional label and location of each other clause in the same contract. -/
  uncovered : List (String × Option String × String)

/-- Link each syntax clause to its ordinary resolved terms. The contract resolver numbers
its port binders in the owning protocol's declaration order. -/
structure BoundContract where
  clauses : Array Clause := #[]
  terms : Std.HashMap UInt32 Lowered.Expr := {}

def contractOf (s : Compile.State) (id : DeclarationId) (at_ : Span) :
    ExportM BoundContract := do
  let ids := s.env.modules.indexes.contracts.getD id #[]
  if ids.isEmpty then return {}
  let some owner := s.program.declarations[id]? | refuse at_ "WK-REF" "missing contract owner"
  let some d := s.program.declarations[ids.back!]? | refuse at_ "WK-REF" "missing contract"
  let .contract c := d.node | refuse at_ "WK-REF" "expected a contract"
  if ids.size > 1 then refuse c.span "WK-CLAUSE" "a declaration has more than one contract"
  unless d.file == owner.file && d.namespace == owner.namespace do
    refuse c.span "WK-CLAUSE" "the contract must be in the module that defines its target"
  unless d.scopes.all (fun scope => owner.scopes.contains scope ||
      (s.program.scopes[scope]?).any (fun item => item.parameters.isEmpty && item.whereClause.isNone)) do
    refuse c.span "WK-CLAUSE" "the contract has additional parameter scopes"
  let _ ← declarationRef s d.file c.target
  let some lowered := s.env.modules.lowered? ids.back! | refuse c.span "WK-REF" "missing resolved contract"
  let .unlowered terms := lowered.content | refuse c.span "WK-REF" "missing resolved clause terms"
  return ⟨c.clauses, terms.foldl (fun table term => table.insert term.span.startByte term) {}⟩

def BoundContract.term (contract : BoundContract) (expr : Expr) : ExportM Lowered.Expr :=
  let span := (Static.withoutParentheses expr).span
  (contract.terms[span.startByte]?).elim (refuse span "WK-REF" "missing resolved clause expression") pure

def clauseIdentity : Clause → String × Option Label
  | .requires _ l _ => ("requires", l)
  | .ensures _ l _ => ("ensures", l)
  | .invariant _ l .. => ("invariant", l)
  | .reduces _ _ l .. => ("reduces", l)
  | .proves _ _ l .. => ("proves", l)
  | .through .. => ("through", none)
  | .knowledge _ l .. => ("knowledge", l)
  | .zeroKnowledge _ l .. => ("zero_knowledge", l)
  | .charge .. => ("charge", none)

def clause (s : Compile.State) (root : DeclarationId) (file : FileId)
    (selected : Option String) (where_ : Span) : ExportM ClauseSource := do
  let contract ← contractOf s root where_
  let mut labels : Std.HashSet String := {}
  let mut chosen := none
  let mut uncovered := #[]
  for cl in contract.clauses do
    let (kind, label) := clauseIdentity cl
    let name := label.map (·.name.text)
    if let some n := name then
      if labels.contains n then refuse cl.span "WK-CLAUSE" s!"duplicate clause label {n}"
      labels := labels.insert n
    match cl with
    | .requires sp .. => refuse sp "WK-CLAUSE" "unsupported protocol precondition"
    | _ => pure ()
    if kind == "knowledge" && (selected.isNone || name == selected) then
      if chosen.isSome then refuse cl.span "WK-CLAUSE" "several knowledge clauses; select a label"
      let .knowledge sp _ expr (.path ext) none := cl
        | refuse cl.span "WK-CLAUSE" "expected one source extractor"
      let .call _ rel (.callArgs _ _ none) := Static.withoutParentheses expr
        | refuse expr.span "WK-CLAUSE" "expected a relation call on statement arguments"
      let .call _ _ args none ← contract.term expr | refuse sp "WK-CLAUSE" "expected a resolved relation call"
      let operands ← args.mapM fun
        | .positional _ (.local _ port) => pure port
        | _ => refuse sp "WK-PORT" "expected positional public port operands"
      chosen := some (sp, rel, operands, ext, name)
    else uncovered := uncovered.push (kind, name, location cl.span)
  let some (sp, rel, operands, ext, name) := chosen
    | refuse where_ "WK-CLAUSE" s!"missing selected knowledge clause{(selected.map (" " ++ ·)).getD ""}"
  return ⟨sp, file, rel, operands, ext, name, uncovered.toList⟩

end Zkc.Frontend.Written
