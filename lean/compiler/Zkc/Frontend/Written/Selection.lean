module

public import Zkc.Frontend.Written.Diagnostic
public import Zkc.Frontend.Syntax.Spans
public import Zkc.Frontend.Driver.Bodies
public import Zkc.Frontend.Static.Rational

@[expose] public section
set_option autoImplicit false

namespace Zkc.Frontend.Written
open Syntax

/-- Ordinary protocol bodies resolve generated-member dependencies regardless of query order. -/
def sourceContext : Compile.Context := Typing.withProtocolBodies {vocabulary}

/-- Run an ordinary frontend request, preserving its nominal instance table for its consumers. -/
def evaluate {α : Type} (s : Compile.State) (at_ : Span) (attempt : CompileM α) :
    ExportM (α × Compile.State) := do
  let (result, after) := attempt.run sourceContext s
  if let some d := (after.log.entries.extract s.log.entries.size after.log.entries.size).find?
      (fun d => d.isError || d.isIncomplete) then
    refuse at_ "WK-TYPE" (d.render after.env.renderer)
  match result with
  | .ok a => pure (a, after)
  | .error (.waiting why) | .error (.defect why) => refuse at_ "WK-TYPE" why
  | .error _ => refuse at_ "WK-TYPE" "could not elaborate the selected source declaration"

/-- An executable instance with the proof-only values at one use, in parameter order. -/
structure ProofSubject where
  protocol : InstanceId
  specification : Array Nat
  deriving DecidableEq, Repr

inductive GoalKind where
  | fork
  | soundness
  deriving BEq

/-- CLI selectors are exclusive. A scheme selects a written clause; a goal asks for every
requirement of the named source property at its selected stage. -/
inductive Request where
  | scheme (name : String) (clause : Option String := none)
  | goal (name : String)

structure Selection where
  scheme : SchemeEntry
  clause : Option String
  schemePath : String
  goal : Option Lowered.Goal := none
  goalPath : Option String := none
  specification : Array Nat := #[]
  ceiling : Option Rat := none

def closedDeclaration (ref : Lowered.Reference) : ExportM DeclarationId := do
  if ref.hasStaticArguments then
    refuse ref.span "WK-REF" "explicit or import-fixed static arguments on a clause reference"
  let some id := ref.declaration? | refuse ref.span "WK-REF" "expected a declaration"
  return id

/-- An imported scheme is also a root when an entry goal selects it. Reuse ordinary SC1
instantiation in the defining file and retain the resulting table for body elaboration. -/
def goalScheme (s : Compile.State) (goal : Lowered.Goal) :
    ExportM (SchemeEntry × Compile.State) := do
  let .reference ref := goal.scheme | refuse goal.scheme.span "WK-GOAL" "unresolved goal scheme"
  let id ← closedDeclaration ref
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

def selectedGoal (state : Compile.State) (goal : Lowered.Goal) (path : String)
    (file : FileId) (kind : GoalKind) :
    ExportM (Selection × Compile.State) := do
  let (scheme, s) ← goalScheme state goal
  let .reference ref := goal.property | refuse goal.property.span "WK-GOAL" "unresolved formal property"
  let some (.entry library property) := ref.lastStep?
    | refuse ref.span "WK-GOAL" "expected a formal library property"
  if ref.hasStaticArguments then refuse ref.span "WK-GOAL" "this property takes no static arguments"
  let some entry := vocabularyEntry? library property | refuse goal.property.span "WK-GOAL" "unknown property"
  let .property description := entry.kind | refuse goal.property.span "WK-GOAL" "a security model cannot select a property"
  let some key := s.results.key? scheme.protocol | refuse goal.span "WK-GOAL" "missing protocol"
  let some protocol := s.program.declarations[key.declaration]? | refuse goal.span "WK-GOAL" "missing declaration"
  let supplied := goal.args.filterMap fun
    | .spec span name expr => some (span, name.text, expr)
    | _ => none
  let (specification, _) ← evaluate s goal.span do
    let some closure ← Static.specificationClosure {file} protocol supplied #[] goal.span | return #[]
    closure.close scheme.protocol {} goal.span
  let mut stage := none
  let mut label := none
  let mut fixed := false
  for argument in goal.args do
    let .named span key value := argument | continue
    if kind == .soundness && key.text == "statement" then
      let .path _ (.reference (.reference _ #[.segment (.word "fixed") none none])) none := value
        | refuse span "GL3" "the written theorem requires a fixed statement"
      if fixed then refuse span "GL2" "duplicate statement selection"
      fixed := true
      continue
    unless key.text == "stage" || key.text == "clause" do
      refuse span "WK-GOAL" s!"{property}: no written theorem covers goal argument {key.text}"
    let .path _ (.reference (.reference _ #[.segment step none none])) none := value
      | refuse span "WK-GOAL" s!"expected one name for {key.text}"
    let name ← match key.text, step with
      | "stage", .word word | "clause", .label word => pure word
      | _, _ => refuse span "WK-GOAL" s!"expected one name for {key.text}"
    if key.text == "stage" then
      if stage.isSome then refuse span "WK-GOAL" "duplicate stage"
      stage := some name
    else
      if label.isSome then refuse span "WK-GOAL" "duplicate clause selection"
      label := some name
  let requested := stage.getD scheme.lastStage
  unless requested == "written" do
    refuse goal.span "WK-GOAL" s!"{goal.name.text} requires stage {requested}; only written executions are available"
  let ceiling ← match kind with
    | .fork => do
      unless description.stages.contains requested && description.binding == some .writtenFork do
        refuse goal.property.span "WK-GOAL" s!"no complete theorem for {library}::{property} at {requested}; a two-run knowledge clause supplies special soundness"
      if goal.ceiling.isSome then refuse goal.span "WK-GOAL" "the written fork property has no quantitative ceiling"
      pure none
    | .soundness => do
      unless library == "zkc::security" && property == "soundness" && description.stages.contains requested do
        refuse goal.property.span "GL3" "expected the written soundness property"
      if !fixed && scheme.lines.any (fun line => line matches .construction _ (.derived ..)) then
        refuse goal.span "GL3" "the written theorem requires a fixed statement"
      if label.isSome then refuse goal.span "GL3" "soundness selection requires one deciding clause"
      goal.ceiling.mapM fun expr => do
        let (value, _) ← evaluate s expr.span (Static.evalRational {file} expr)
        if value < 0 then refuse expr.span "GL4" "a goal ceiling must be nonnegative"
        return value
  return (⟨scheme, label, Static.qualifiedName s.program scheme.declaration,
    some goal, some path, specification, ceiling⟩, s)

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

def selectNamedGoal (s : Compile.State) (name : String) (kind : GoalKind) :
    ExportM (Selection × Compile.State) := do
  let (id, path) ← selectDeclaration s .goal name "WK-GOAL"
  let some decl := s.program.declarations[id]? | throw "WK-GOAL: missing goal"
  let some {content := .goal goal, ..} := s.env.modules.lowered? id
    | throw "WK-GOAL: missing resolved goal"
  selectedGoal s goal path decl.file kind

def select (s : Compile.State) : Request → ExportM (Selection × Compile.State)
  | .scheme name label => do
    let (id, path) ← selectDeclaration s .scheme name "WK-ROOT"
    let some scheme := s.results.schemes.find? (·.declaration == id)
      | throw s!"WK-ROOT: no closed scheme for {path}"
    return (⟨scheme, label, path, none, none, #[], none⟩, s)
  | .goal name => selectNamedGoal s name .fork

structure WrittenParties where
  interactive : Bool
  declaredProver : Option Nat
  place : Span

/-- Written goals use the scheme's online roles and public statement (SC2–SC4).
Construction and layout directives take effect after this stage. -/
def writtenParties (scheme : SchemeEntry) (roles : Array String) : ExportM WrittenParties := do
  let mut interactive := false
  let mut prover := none
  let mut place := scheme.span
  for line in scheme.lines do
    match line with
    | .offline sp .. | .ideal sp .. => refuse sp "WK-VIEW" "the written goal requires two online roles"
    | .construction _ (.interactive _) => interactive := true
    | .prover sp role =>
      if prover.isSome then refuse sp "SC3" "duplicate prover designation"
      let some id := roles.findIdx? (· == role.text) | refuse sp "SC3" s!"unknown prover {role.text}"
      prover := some id
      place := sp
    | _ => pure ()
  return ⟨interactive, prover, place⟩

structure ClauseSource where
  where_ : Span
  rel : Lowered.Reference
  arguments : Array Lowered.Argument
  extractor : Lowered.Reference
  label : Option String
  /-- Kind, optional label and location of each other clause in the same contract. -/
  uncovered : List (String × Option String × String)

/-- Read the resolved clauses attached to the selected declaration. -/
def contractOf (s : Compile.State) (id : DeclarationId) (at_ : Span) :
    ExportM (Array Lowered.Clause) := do
  let some cid := s.env.modules.indexes.contracts[id]? | return #[]
  let some owner := s.program.declarations[id]? | refuse at_ "WK-REF" "missing contract owner"
  let some d := s.program.declarations[cid]? | refuse at_ "WK-REF" "missing contract"
  let some {content := .contract c, ..} := s.env.modules.lowered? cid
    | refuse at_ "WK-REF" "missing resolved contract"
  unless d.scopes.all (fun scope => owner.scopes.contains scope ||
      (s.program.scopes[scope]?).any (fun item => item.parameters.isEmpty && item.whereClause.isNone)) do
    refuse c.span "WK-CLAUSE" "the contract has additional parameter scopes"
  let .reference target := c.target | refuse c.span "WK-REF" "unresolved contract target"
  unless (← closedDeclaration target) == id do refuse c.span "WK-REF" "misindexed contract"
  return c.clauses

def clauseIdentity : Lowered.Clause → String × Option Label
  | .requires _ l _ => ("requires", l)
  | .ensures _ l _ => ("ensures", l)
  | .invariant _ l .. => ("invariant", l)
  | .reduces _ _ l .. => ("reduces", l)
  | .proves _ _ l .. => ("proves", l)
  | .through .. => ("through", none)
  | .knowledge _ l .. => ("knowledge", l)
  | .zeroKnowledge _ l .. => ("zero_knowledge", l)
  | .charge .. => ("charge", none)

def clause (s : Compile.State) (root : DeclarationId)
    (selected : Option String) (where_ : Span) : ExportM ClauseSource := do
  let contract ← contractOf s root where_
  let mut labels : Std.HashSet String := {}
  let mut chosen := none
  let mut uncovered := #[]
  for cl in contract do
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
      let .knowledge sp _ expr (.path (.reference ext)) none := cl
        | refuse cl.span "WK-CLAUSE" "expected one source extractor"
      let .call _ rel args none := expr
        | refuse expr.span "WK-CLAUSE" "expected a relation call on statement arguments"
      chosen := some (sp, rel, args, ext, name)
    else uncovered := uncovered.push (kind, name, location cl.span)
  let some (sp, rel, args, ext, name) := chosen
    | refuse where_ "WK-CLAUSE" s!"missing selected knowledge clause{(selected.map (" " ++ ·)).getD ""}"
  return ⟨sp, rel, args, ext, name, uncovered.toList⟩

end Zkc.Frontend.Written
