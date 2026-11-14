module

public import Zkc.Frontend.Names.Declarations
public import Zkc.Frontend.Syntax.Parser

@[expose] public section

set_option autoImplicit false

/-!
# The check of names

The names of an assembled program are resolved and lowered in one walk: every import, every
declaration of the program, reached or not, the parameters of every section, and the terms of
the comments `// instantiate:`. The result is the lowered form of all of it, the first refusal of
each declaration, and the table of resolutions, which is read off the lowered form: every
reference at the byte where its path starts, every use of a local name at the byte of the name.
The driver runs it as the phase of names, after assembly; refusals are shown in source order:
the files in the order of the program, the given files first (`sortRefusals`).
-/

namespace Zkc.Frontend

open Syntax

namespace Names

/-- The names of the alternatives of every variant of the program. -/
def alternativeNames (program : Program) : Std.HashSet String :=
  program.declarations.foldl (init := {}) fun names declaration =>
    match declaration.node with
    | .enum node => node.alternatives.foldl (init := names) fun names alternative =>
        names.insert alternative.name.text
    | _ => names

def initialState (assembly : Assembly) : State :=
  let program := assembly.program
  let inner (path : String) : Option NamespaceId :=
    (program.modules[path]?).bind fun id => (program.declarations[id]?).bind (·.inner)
  let layout := (inner "zkc::layout").bind fun ns =>
    match (program.namespaces[ns]?).bind (·.names["Layout"]?) with
    | some (.declaration id) =>
      if (program.declarations[id]?).any (·.kind == .interface) then some id else none
    | _ => none
  { program, unreadable := assembly.unreadable
    alternatives := alternativeNames program
    prelude? := inner "zkc::prelude"
    layout? := layout }

/-- The term of a comment `// instantiate: m<args>`, and its offset in the comment in bytes. -/
def instantiateDirective (comment : Comment) : Option (Nat × String) :=
  let marker := "// instantiate:"
  if comment.text.startsWith marker then
    let rest := String.ofList (comment.text.toList.drop marker.length)
    let spaces := (rest.toList.takeWhile (· == ' ')).length
    let term := String.ofList ((rest.toList.drop spaces).reverse.dropWhile (· == ' ')).reverse
    some (marker.length + spaces, term)
  else none

/-- A source in which the term of a directive is the size of a static name and stands at the
line, the column and the byte of the comment: its spans are those of the comment. The line of the
comment is assumed to hold only ASCII before the term. -/
def directiveSource (comment : Comment) (offset : Nat) (term : String) : Option String := do
  let column := comment.column + offset
  if comment.line < 2 || column < 9 || comment.startByte + 1 < comment.column then none
  let lineStart := comment.startByte + 1 - comment.column
  if lineStart < comment.line - 2 + 1 + 8 then none
  let header := lineStart - (comment.line - 2) - 1
  let spaces (count : Nat) := String.ofList (List.replicate count ' ')
  return "module p" ++ spaces (header - 8) ++ "\n" ++ String.ofList (List.replicate (comment.line - 2) '\n')
    ++ "nat q =" ++ spaces (column - 8) ++ term ++ "\n"

/-- Reads the comments `// instantiate: m<args>` of a file and resolves and lowers their terms in
the scope of the file module. A comment that does not parse is refused with the rule of the
parser. -/
def resolveDirectives (file : FileId) : ResolveM Unit := do
  let program := (← get).program
  let some unit := program.files[file]? | return
  let some fileModule := program.modules[pathText unit.path]? | return
  let some declaration := program.declarations[fileModule]? | return
  for comment in unit.tree.comments do
    let some (offset, term) := instantiateDirective comment | continue
    let some source := directiveSource comment offset term | continue
    match parseString unit.name source with
    | .error error => refuse (.declaration fileModule) (Diagnostic.ofSyntax error)
    | .ok parsed =>
      let some (Item.staticName node) := parsed.tree.items[0]? | continue
      let env ← makeEnv (.declaration fileModule) file (declaration.inner.getD declaration.namespace)
        declaration.scopes
      startDeclaration
      let lowered ← resolveExprAt env .plain node.size
      modify fun state => { state with
        instantiations := state.instantiations.push (file, node.size, lowered) }

/-- What one walk over a program gives: the lowered form of every declaration, parameter scope
and import, by number. -/
structure Walked where
  declarations : Array Lowered.Declaration
  scopes : Array Lowered.Scope
  uses : Array (Array Lowered.Expr)

def run : ResolveM Walked := do
  let program := (← get).program
  let mut uses := #[]
  let mut paths : Std.HashSet (FileId × UInt32) := {}
  for id in [0:program.imports.size] do
    let entry := program.imports[id]!
    let key := (entry.file, entry.path.span.startByte)
    uses := uses.push (← resolveImport id (!paths.contains key))
    paths := paths.insert key
  let mut declarations := #[]
  let mut owned : Std.HashMap ScopeId Lowered.Scope := {}
  for id in [0:program.declarations.size] do
    let (declaration, scope) ← resolveDeclaration id
    declarations := declarations.push declaration
    if let some scope := scope then owned := owned.insert scope.id scope
  for id in [0:program.scopes.size] do
    if (program.scopes[id]?).any (·.origin == .«section») then
      if let some scope ← resolveSection id then owned := owned.insert id scope
  for file in [0:program.files.size] do
    resolveDirectives file
  let scopes := (List.range program.scopes.size).toArray.map fun id =>
    owned.getD id { id, bounds := #[], constraints := #[] }
  return { declarations, scopes, uses }

/-! ## The table of resolutions, read off the lowered form -/

namespace Projection

/-- The table of each file so far, and the places where two nodes of the lowered form say
different things. -/
structure State where
  files : Array FileResolutions
  /-- The file of the entry being read: every place of a declaration, a scope, a `use` or a
  comment is in its file, but for the static arguments that an import fixes. -/
  file : FileId := 0
  /-- The `use` being read: the static arguments that it fixes are written in it. -/
  ownImport : Option ImportId := none
  conflicts : Array (FileId × UInt32) := #[]
  /-- The binders that lowering made in the declaration being read: a use of one names no
  path of the source. -/
  made : Std.HashSet LocalId := {}

abbrev ProjectM := StateM State

def summary (resolution : Resolution) : Array (Step × Bool × Option ImportId) :=
  resolution.segments.map fun segment => (segment.step, segment.staticArgs.isSome, segment.fixedBy)

def add (span : Span) (resolution : Resolution) : ProjectM Unit :=
  modify fun state =>
    let byte := span.startByte
    match (state.files[state.file]?).bind (·[byte]?) with
    | some earlier =>
      if summary earlier == summary resolution then state
      else { state with conflicts := state.conflicts.push (state.file, byte) }
    | none => { state with files := state.files.modify state.file (·.insert byte resolution) }

/-- Starts reading an entry of a file. -/
def start (file : FileId) (ownImport : Option ImportId := none) : ProjectM Unit :=
  modify fun state => { state with file, ownImport, made := {} }

mutual
  /-- A reference at the byte where its path starts, and the static arguments written on it;
  those that an import fixes are read with the `use` that writes them. -/
  partial def reference : Lowered.Reference → ProjectM Unit
    | .reference span segments => do
      unless segments.isEmpty do
        add span { segments := segments.map fun (.segment step arguments fixedBy) =>
          { step, staticArgs := arguments, fixedBy } }
      let ownImport := (← get).ownImport
      for (.segment _ arguments fixedBy) in segments do
        if fixedBy.isNone || fixedBy == ownImport then
          for argument in arguments.getD #[] do staticArgument argument

  partial def staticArgument : Lowered.StaticArgument → ProjectM Unit
    | .term _ _ term | .spec _ _ term => expr term
    | .inferred .. => pure ()

  partial def typeTerm : Lowered.TypeTerm → ProjectM Unit
    | .index _ size => expr size
    | .nonzero _ type => typeTerm type
    | .sequence _ element size => do typeTerm element; if let some size := size then expr size
    | .tuple _ fields _ => for field in fields do typeTerm field
    | .reference written => reference written
    | .local span binder => localUse span binder
    | .bool _ | .nat _ | .rational _ | .error _ => pure ()

  partial def localUse (span : Span) (binder : LocalId) : ProjectM Unit := do
    unless (← get).made.contains binder do
      add span { segments := #[{ step := .«local», staticArgs := none }] }

  partial def expr : Lowered.Expr → ProjectM Unit
    | .local span binder => localUse span binder
    | .reference written => reference written
    | .call _ callee arguments witnesses => do
      reference callee
      for argument in arguments ++ witnesses.getD #[] do argumentOf argument
    | .operator _ _ operands => for operand in operands do expr operand
    | .slice _ target lower upper => do
      expr target
      if let some lower := lower then expr lower
      if let some upper := upper then expr upper
    | .field _ target _ | .position _ target _ => expr target
    | .method _ target _ staticArguments arguments => do
      expr target
      for argument in staticArguments.getD #[] do staticArgument argument
      for argument in arguments do argumentOf argument
    | .conditional _ _ a b c => do expr a; expr b; expr c
    | .tuple _ components _ => for component in components do expr component
    | .list _ elements => for element in elements do expr element
    | .repetition _ element count => do expr element; expr count
    | .record _ type fields => do
      reference type
      for (.field _ _ value) in fields do expr value
    | .recordUpdate _ value fields => do
      expr value
      for (.field _ _ value) in fields do expr value
    | .comprehension _ element domain filter => do
      generator domain
      expr element
      if let some filter := filter then expr filter
    | .fold _ _ domain body => do generator domain; expr body
    | .inner _ a b => do expr a; expr b
    | .block _ statements result => do stmts statements; expr result
    | .type written => typeTerm written
    | .number .. | .bytes .. | .bool .. | .error _ => pure ()

  partial def argumentOf : Lowered.Argument → ProjectM Unit
    | .positional _ value | .named _ _ value | .spec _ _ value => expr value

  partial def binder (written : Lowered.Binder) : ProjectM Unit :=
    unless written.origin == .written do
      modify fun state => { state with made := state.made.insert written.id }

  partial def generator : Lowered.Generator → ProjectM Unit
    | .range index start stop _ => do binder index; expr start; expr stop
    | .collection item iteration source => do binder item; binder iteration; expr source

  partial def stmts (statements : Array Lowered.Stmt) : ProjectM Unit :=
    for statement in statements do stmt statement

  partial def stmt : Lowered.Stmt → ProjectM Unit
    | .bind _ written type _ value => do
      binder written
      if let some type := type then typeTerm type
      expr value
    | .staticName _ _ value => expr value
    | .update _ target value => do expr target; expr value
    | .unpack _ shape binders _ value => do
      if let .record type _ _ := shape then reference type
      for written in binders do if let some written := written then binder written
      expr value
    | .guard _ _ condition _ => expr condition
    | .«if» _ _ condition onTrue onFalse => do expr condition; stmts onTrue; stmts onFalse
    | .«match» _ scrutinee cases => do
      expr scrutinee
      for (.«case» _ pattern body) in cases do
        casePattern pattern
        stmts body
    | .«for» _ domain collected body => do
      generator domain
      stmts body
      for (.collected _ _ value) in collected do expr value
    | .event _ _ written type _ what => do
      if let some written := written then binder written
      if let some type := type then typeTerm type
      event what
    | .waiting _ _ names => for name in names do expr name

  partial def casePattern : Lowered.CasePattern → ProjectM Unit
    | .alternative _ alternative payload => do
      reference alternative
      for item in payload do casePattern item
    | .tuple _ items => for item in items do casePattern item
    | .record _ type fields => do
      reference type
      for (_, item) in fields do casePattern item
    | .literal _ value => expr value
    | .any _ _ => pure ()

  partial def event : Lowered.Event → ProjectM Unit
    | .send payload _ _ => expr payload
    | .draw law _ _ | .sample law => typeTerm law
    | .attempt => pure ()
    | .apply callee arguments _ => do
      reference callee
      for argument in arguments do argumentOf argument
end

def functionBody : Lowered.FunctionBody → ProjectM Unit
  | .body value => expr value
  | .primitive _ _ arguments => for argument in arguments do staticArgument argument
  | .external .. | .absent => pure ()

def content : Lowered.Content → ProjectM Unit
  | .function head body => do
    for parameter in head.parameters do typeTerm parameter.type
    if let some result := head.result then typeTerm result
    functionBody body
  | .protocol head body results => do
    for port in head.ports do typeTerm port.type
    for result in head.results do typeTerm result.type
    stmts body
    for result in results do expr result
  | .alias type => typeTerm type
  | .vocabularyType _ arguments => for argument in arguments do staticArgument argument
  | .record _ fields => for (_, type) in fields do typeTerm type
  | .«variant» alternatives => for (_, types) in alternatives do for type in types do typeTerm type
  | .staticName value => expr value
  | .memberDefinition _ body => functionBody body
  | .unlowered names => for name in names do expr name

def scope (written : Lowered.Scope) : ProjectM Unit := do
  for bound in written.bounds do
    if let some bound := bound then
      for sort in bound.sorts do
        if let .reference written := sort then reference written
  for constraint in written.constraints do
    match constraint with
    | .bound _ subject sorts => do
      expr subject
      for sort in sorts do if let .reference written := sort then reference written
    | .compare _ _ left right => do expr left; expr right

end Projection

/-- The table of resolutions of every file, read off the lowered form, and the places where two
nodes of the lowered form say different things, by file name and byte. -/
def project (program : Program) (walked : Walked) (instantiations : Array (FileId × Lowered.Expr)) :
    Resolutions × Array (String × UInt32) :=
  let action : Projection.ProjectM Unit := do
    for id in [0:walked.uses.size] do
      Projection.start ((program.imports[id]?).map (·.file) |>.getD 0) (some id)
      for name in walked.uses[id]! do Projection.expr name
    for declaration in walked.declarations do
      Projection.start ((program.declarations[declaration.id]?).map (·.file) |>.getD 0)
      Projection.content declaration.content
    for written in walked.scopes do
      Projection.start ((program.scopes[written.id]?).map (·.file) |>.getD 0)
      Projection.scope written
    for (file, term) in instantiations do
      Projection.start file
      Projection.expr term
  let ((), state) := action.run { files := Array.replicate program.files.size {} }
  ({ files := state.files }, state.conflicts.map fun (file, byte) =>
    (((program.files[file]?).map (·.name)).getD "?", byte))

end Names

/-- The refusals in source order: by file, in the order of `files`, then by place. -/
def sortRefusals (files : Array String) (refusals : Array Refusal) : Array Refusal :=
  let ranks : Std.HashMap String Nat :=
    (List.range files.size).foldl (init := {}) fun ranks index => ranks.insert files[index]! index
  let key (refusal : Refusal) : Nat × Nat × Nat :=
    ((ranks[refusal.span.file]?).getD files.size, refusal.span.startLine.toNat,
      refusal.span.startColumn.toNat)
  refusals.qsort fun a b =>
    let (fa, la, ca) := key a
    let (fb, lb, cb) := key b
    fa < fb || (fa == fb && (la < lb || (la == lb && (ca < cb || (ca == cb && a.rule < b.rule)))))

/-- What the check of names makes of an assembled program: the lowered form of every
declaration, parameter scope, `use` and comment `// instantiate:`, the table of resolutions read
off it, and the first refusal of each declaration in source order (in the order of the table of
refusals). -/
structure Resolved where
  resolutions : Resolutions
  refusals : Array Diagnostic
  instantiations : Array (FileId × Expr)
  lowered : Array Lowered.Declaration
  loweredScopes : Array Lowered.Scope
  /-- The lowered path and name of each `use`, by number. -/
  loweredUses : Array (Array Lowered.Expr)
  /-- The terms of the comments `// instantiate:`, lowered, in the order of `instantiations`. -/
  loweredInstantiations : Array (FileId × Lowered.Expr)
  /-- Places where two nodes of the lowered form say different things, by file name and byte:
  none on a sound walk. -/
  conflicts : Array (String × UInt32)

/-- Resolves and lowers the names of an assembled program. -/
def resolveProgram (assembly : Assembly) : Resolved :=
  let (walked, state) := Names.run.run (Names.initialState assembly)
  let instantiations := state.instantiations.map fun (file, _, lowered) => (file, lowered)
  let (resolutions, conflicts) := Names.project assembly.program walked instantiations
  { resolutions
    refusals := state.refusals.fold (init := #[]) fun refusals _ refusal => refusals.push refusal
    instantiations := state.instantiations.map fun (file, term, _) => (file, term)
    lowered := walked.declarations, loweredScopes := walked.scopes, loweredUses := walked.uses
    loweredInstantiations := instantiations
    conflicts }

/-- One step as text: what it stands for, and `(use)` when an import fixes its arguments. -/
def renderStep (program : Program) (segment : ResolvedSegment) : String :=
  let name (id : DeclarationId) := program.nameOf id
  let text := match segment.step with
    | .«local» => "local"
    | .parameter reference =>
      let parameter : Option StaticParam :=
        (program.scopes[reference.scope]?).bind (·.parameters[reference.index]?)
      s!"parameter {(parameter.map (·.name.text)).getD "?"}"
    | .self interface => s!"Self of {name interface}"
    | .declaration id => s!"declaration {name id}"
    | .member member (some declared) =>
      let interface := ((program.declarations[declared]?).bind fun d =>
        program.namespaces[d.namespace]?).map (·.owner)
      s!"member {member} of {(interface.map name).getD "?"}"
    | .member member none => s!"member {member} at the instance"
    | .alternative id index =>
      let node : Option DeclarationSyntax := (program.declarations[id]?).map (·.node)
      let alternative : Option String := match node with
        | some (.enum node) => (node.alternatives[index]?).map (·.name.text)
        | _ => none
      s!"alternative {name id}::{alternative.getD "?"}"
    | .generated member => s!"generated {member}"
    | .fixed function =>
      let word := match function with
        | .sum => "sum" | .product => "product" | .all => "all" | .any => "any" | .inner => "inner"
      s!"fixed {word}"
    | .sizeOperator => "log2"
    | .role role => s!"role {role}"
    | .word word => s!"word {word}"
    | .label label => s!"label {label}"
    | .vocabularyModule path => s!"vocabulary module {path}"
    | .entry path entry => s!"entry {path}::{entry}"
    | .bareAlternative alternative => s!"alternative {alternative} of the expected variant"
  let args := if segment.staticArgs.isSome then " <…>" else ""
  let fixed := if segment.fixedBy.isSome then " (use)" else ""
  text ++ args ++ fixed

/-- A resolution as text: its steps joined by ` / `. -/
def renderResolution (program : Program) (resolution : Resolution) : String :=
  " / ".intercalate (resolution.segments.toList.map (renderStep program))

end Zkc.Frontend
