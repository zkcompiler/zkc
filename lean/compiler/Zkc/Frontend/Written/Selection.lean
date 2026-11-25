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
  | .error (.exhausted exhaustion) => refuse at_ "WK-TYPE" s!"not checked: {exhaustion.describe}"
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

/-- Why no clause of a kind is the one that a goal reads. -/
inductive ChoiceFailure where
  /-- Two clauses of the contract have one label. -/
  | duplicate (second : Span) (label : String)
  /-- The contract has no clause of the kind. -/
  | absent
  /-- The goal names none of several clauses of the kind; `second` is the second of them. -/
  | several (second : Span) (labels : List String)
  /-- No clause of the contract has the label that the goal names. -/
  | unknown (label : String)
  /-- The label that the goal names is of a clause of another kind. -/
  | otherKind (clause : Span) (kind label : String)

/-- The clause of a kind that a goal reads (GL3), with its place in the contract: the one that
the goal names by its label, or the only one of the kind. A label is of one clause of a
contract. -/
def chooseClause (contract : Array Lowered.Clause) (eligible : Lowered.Clause → Bool)
    (selected : Option String) : Except ChoiceFailure (Nat × Lowered.Clause) := do
  let mut labels : Std.HashSet String := {}
  for clause in contract do
    if let some label := (clauseIdentity clause).2 then
      if labels.contains label.name.text then throw (.duplicate clause.span label.name.text)
      labels := labels.insert label.name.text
  let labelOf (clause : Lowered.Clause) := (clauseIdentity clause).2.map (·.name.text)
  let candidates := (contract.zipIdx.filter fun (clause, _) => eligible clause).map fun (clause, i) => (i, clause)
  match selected with
  | some label =>
    if let some found := candidates.find? (labelOf ·.2 == some label) then return found
    match contract.find? (labelOf · == some label) with
    | some other => throw (.otherKind other.span (clauseIdentity other).1 label)
    | none => throw (.unknown label)
  | none =>
    match candidates with
    | #[found] => return found
    | #[] => throw .absent
    | several => throw (.several several[1]!.2.span (several.toList.filterMap (labelOf ·.2)))

/-- The kinds of clause from which a soundness goal forms its claim. -/
inductive DecidingKind where
  | proves
  | reduces
  deriving BEq, DecidableEq, Repr

/-- The application of a relation in a deciding clause, as the source wrote it: the relation by
its declaration, and its operands in the order of the relation's parameters, whatever the order
in which named arguments were written. -/
structure RelationApplication where
  relation : DeclarationId
  /-- The reference as written, with its static and specification arguments. -/
  reference : Lowered.Reference
  /-- The operands at the statement parameters. -/
  statement : Array Lowered.Expr
  /-- The operands at the witness parameters; none when the clause is written short. -/
  witness : Array Lowered.Expr

/-- A deciding clause of a contract as the source wrote it. It names declarations and binders
of the protocol, which mean the same in every state of one compilation; it names no instance,
whose number is of the state that made it. -/
structure DecidingClause where
  span : Span
  /-- Its place among the clauses of the contract. -/
  place : Nat
  kind : DecidingKind
  label : Option String
  /-- The deciding role, by its place in the roster of the protocol. -/
  role : Option Nat
  /-- What the clause states: for `reduces`, its source. -/
  proposition : Lowered.Expr
  /-- The application of a relation that the proposition is, when it is one. -/
  application : Option RelationApplication
  /-- For `reduces`, what the clause reduces to, as written under the results of the protocol:
  the soundness of a reduction is about it. -/
  target : Option Lowered.Expr := none

/-- Whether a soundness goal can read the clause. -/
def decides : Lowered.Clause → Bool
  | .proves .. | .reduces .. => true
  | _ => false

/-- The deciding clause of a contract that a soundness goal reads (GL3): the one that the goal
names, or the only one. -/
def decidingClause (s : Compile.State) (root : DeclarationId) (selected : Option String)
    (place : Span) : ExportM DecidingClause := do
  let name := s.program.nameOf root
  let (index, clause) ← match chooseClause (← contractOf s root place) decides selected with
    | .ok found => pure found
    | .error (.duplicate second label) => refuse second "GL3" s!"two clauses of `{name}` are labelled `{label}`"
    | .error .absent =>
      refuse place "GL3" s!"`{name}` has no `proves` or `reduces` clause; add one to `spec for {name}`"
    | .error (.several second labels) =>
      let named := if labels.isEmpty then "" else s!" ({", ".intercalate labels})"
      refuse second "GL3" s!"`{name}` has several deciding clauses{named}; the goal names one with `clause = …`"
    | .error (.unknown label) => refuse place "GL3" s!"`{name}` has no clause labelled `{label}`"
    | .error (.otherKind at_ kind label) =>
      refuse at_ "GL3" s!"`{label}` is a `{kind}` clause; soundness reads a `proves` or `reduces` clause"
  let (kind, role, label, proposition, target) ← match clause with
    | .proves _ role label relation => pure (DecidingKind.proves, role, label, relation, none)
    | .reduces _ role label source target => pure (DecidingKind.reduces, role, label, source, some target)
    | other => refuse other.span "GL3" "expected a `proves` or `reduces` clause"
  let application ← match proposition with
    | .call at_ reference arguments witnesses => do
      let some id := reference.declaration? | pure none
      let some found := s.program.declarations[id]? | pure none
      let .relation relation := found.node | pure none
      let paired (parameters : Array Param) (given : Array Lowered.Argument) :=
        match Lowered.pairValueArguments relation.name.text (parameters.map (·.name.text)) given at_ with
        | .ok operands => pure operands
        | .error (span, message) => refuse span "FN6" message
      let statement ← paired relation.statement arguments
      let witness ← match witnesses with
        | some given => paired (relation.witness.getD #[]) given
        | none => pure #[]
      pure (some { relation := id, reference, statement, witness })
    | _ => pure none
  return { span := clause.span, place := index, kind, label := label.map (·.name.text), role
           proposition, application, target }

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
      -- the clause that the goal names is one that soundness reads (GL3); a goal that names
      -- none is not asked for one here: reading a charge at a site states no claim
      if label.isSome then discard <| decidingClause s key.declaration label goal.span
      goal.ceiling.mapM fun expr => do
        let (value, _) ← evaluate s expr.span (Static.evalRational {file} expr)
        if value < 0 then refuse expr.span "GL4" "a goal ceiling must be nonnegative"
        return value
  return (⟨scheme, label, Static.qualifiedName s.program scheme.declaration,
    some goal, some path, specification, ceiling⟩, s)

/-- Exact and file-relative spellings of input declarations of one kind. Two files can
contribute the same qualified path through a nested module and a file module. -/
structure DeclarationIndex where
  exact : Std.HashMap String (Array DeclarationId) := {}
  aliases : Std.HashMap String (Array String) := {}
  deriving Inhabited

def declarationIndex (s : Compile.State) (kind : DeclarationKind) : DeclarationIndex := Id.run do
  let mut index : DeclarationIndex := {}
  for (d, id) in s.program.declarations.zipIdx do
    unless d.kind == kind && Static.inPackage s.program d.file do continue
    let path := Static.qualifiedName s.program id
    index := { index with exact := index.exact.alter path (fun ids => some ((ids.getD #[]).push id)) }
    let root := pathText s.program.files[d.file]!.path
    let relative := (path.dropPrefix (root ++ "::")).toString
    for alias_ in [s.program.nameOf id, relative].eraseDups do
      let aliases := index.aliases.alter alias_ fun paths => some ((paths.getD #[]).push path)
      index := { index with aliases }
  return index

/-- A selector must identify one declaration, including when its relative spelling picks
one file but its canonical path could name a second declaration in another file. -/
def DeclarationIndex.select (index : DeclarationIndex) (name rule : String) :
    ExportM (DeclarationId × String) := do
  let path ← if index.exact.contains name then pure name else
    match index.aliases[name]?.getD #[] with
    | #[path] => pure path
    | #[] => throw s!"{rule}: no matching declaration named {name} in the input modules"
    | many => throw s!"{rule}: ambiguous {name}: {", ".intercalate many.toList}"
  match index.exact[path]?.getD #[] with
  | #[id] => return (id, path)
  | _ => throw s!"{rule}: ambiguous canonical path {path} in the input modules"

def selectDeclaration (s : Compile.State) (kind : DeclarationKind) (name rule : String) :
    ExportM (DeclarationId × String) :=
  (declarationIndex s kind).select name rule

/-- After selection, read the declaration by ID throughout elaboration. -/
def selectGoalId (s : Compile.State) (id : DeclarationId) (kind : GoalKind) :
    ExportM (Selection × Compile.State) := do
  let some decl := s.program.declarations[id]? | throw "WK-GOAL: missing goal"
  let some {content := .goal goal, ..} := s.env.modules.lowered? id
    | throw "WK-GOAL: missing resolved goal"
  selectedGoal s goal (Static.qualifiedName s.program id) decl.file kind

def selectNamedGoal (s : Compile.State) (name : String) (kind : GoalKind) :
    ExportM (Selection × Compile.State) := do
  let (id, _) ← selectDeclaration s .goal name "WK-GOAL"
  selectGoalId s id kind

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

/-- The knowledge clause that a scheme or a fork goal selects, by the same rule, with the form
that the three-message exporter reads. -/
def clause (s : Compile.State) (root : DeclarationId)
    (selected : Option String) (where_ : Span) : ExportM ClauseSource := do
  let contract ← contractOf s root where_
  for cl in contract do
    if let .requires sp .. := cl then refuse sp "WK-CLAUSE" "unsupported protocol precondition"
  let (place, chosen) ← match chooseClause contract (· matches .knowledge ..) selected with
    | .ok found => pure found
    | .error (.duplicate second label) => refuse second "WK-CLAUSE" s!"duplicate clause label {label}"
    | .error (.several second _) => refuse second "WK-CLAUSE" "several knowledge clauses; select a label"
    | .error .absent | .error (.unknown _) | .error (.otherKind ..) =>
      refuse where_ "WK-CLAUSE" s!"missing selected knowledge clause{(selected.map (" " ++ ·)).getD ""}"
  let .knowledge sp label expr (.path (.reference ext)) none := chosen
    | refuse chosen.span "WK-CLAUSE" "expected one source extractor"
  let .call _ rel args none := expr
    | refuse expr.span "WK-CLAUSE" "expected a relation call on statement arguments"
  let uncovered := (contract.zipIdx.filter (·.2 != place)).map fun (cl, _) =>
    let (kind, label) := clauseIdentity cl
    (kind, label.map (·.name.text), location cl.span)
  return ⟨sp, rel, args, ext, label.map (·.name.text), uncovered.toList⟩

end Zkc.Frontend.Written
