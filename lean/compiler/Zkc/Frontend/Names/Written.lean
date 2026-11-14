module

public import Zkc.Frontend.Names.Forms
public import Zkc.Frontend.Lowered.Declaration

@[expose] public section

set_option autoImplicit false

/-!
# Terms that a later phase reads from the syntax

Typing walks the tree of the parser and evaluates the static terms it meets there. Such a term
is lowered on its own when it is evaluated: every path stands as the steps that the table of
resolutions records for it, with the static arguments that the walk of names lowered; every
local name gets a binder of its own, the same for every use of the name, unless the term binds
it (a comprehension, a fold). The evaluation of a local name reads the name at its place.
-/

namespace Zkc.Frontend.Names.Written

open Syntax
open Lowered (Binder)

/-- What a term lowered apart reads: the program and the tables of resolutions. -/
structure Context where
  program : Program
  tables : Array FileResolutions

structure State where
  /-- The binder of each local name met so far. -/
  locals : Std.HashMap String LocalId := {}
  /-- The names that each open suite binds, innermost last. -/
  suites : Array (Array String) := #[#[]]
  binders : Array Binder := #[]
  deriving Inhabited

abbrev WrittenM := ReaderT Context (StateM State)

/-- Lowers a term apart from its declaration. -/
def lowerApart {α : Type} (program : Program) (tables : Array FileResolutions) (action : WrittenM α) : α :=
  ((action.run { program, tables }).run {}).1

def resolutionAt? (file : FileId) (byte : UInt32) : WrittenM (Option Resolution) :=
  return ((← read).tables[file]?).bind (·[byte]?)

def pushSuite : WrittenM Unit := modify fun state => { state with suites := state.suites.push #[] }

def popSuite : WrittenM Unit :=
  modify fun state =>
    match state.suites.back? with
    | none => state
    | some names =>
      { state with
        locals := names.foldl (init := state.locals) fun locals name => locals.erase name
        suites := state.suites.pop }

/-- A binder of a name that the term binds, in scope in the innermost suite. -/
def bindName (name : Name) : WrittenM Binder := do
  let state ← get
  let binder : Binder := { id := state.binders.size, name := name.text, span := name.span }
  set { state with
    binders := state.binders.push binder
    locals := state.locals.insert name.text binder.id
    suites := state.suites.modify (state.suites.size - 1) (·.push name.text) }
  return binder

/-- The binder of a local name: the one the term binds, or one of its own, the same for every
use of the name. -/
def localBinder (name : String) (span : Span) : WrittenM LocalId := do
  let state ← get
  if let some id := state.locals[name]? then return id
  let id := state.binders.size
  set { state with
    binders := state.binders.push { id, name, span }
    locals := state.locals.insert name id }
  return id

/-- A binder that lowering makes: no source names it. -/
def madeBinder (span : Span) (origin : BinderOrigin) : WrittenM Binder := do
  let state ← get
  let binder : Binder := { id := state.binders.size, name := s!"%{state.binders.size}", span, origin }
  set { state with binders := state.binders.push binder }
  return binder

/-- The reference that the table records for a path at a byte. -/
def reference (span : Span) (resolution : Resolution) : Lowered.Reference :=
  .reference span (resolution.segments.map fun segment =>
    .segment segment.step segment.staticArgs segment.fixedBy)

mutual
  partial def staticArguments (file : FileId) : StaticArgs → WrittenM (Array Lowered.StaticArgument)
    | .staticArgs _ args => args.mapM fun
      | .term span name term => return .term span (name.map (·.text)) (← expr file term)
      | .inferred span name => return .inferred span (name.map (·.text))
      | .spec span name term => return .spec span name.text (← expr file term)

  /-- A path or a name where a value or a static term stands: a local name as its binder, a
  path as its reference, a path that resolution refused as an error. -/
  partial def named (file : FileId) (span : Span) (byte : UInt32) (name : Option String) :
      WrittenM Lowered.Expr := do
    match ← resolutionAt? file byte with
    | some { segments := #[{ step := .«local», .. }] } =>
      match name with
      | some text => return .local span (← localBinder text span)
      | none => return .error span
    | some resolution => return .reference (reference span resolution)
    | none => return .error span

  partial def pathExpr (file : FileId) (span : Span) (path : Path) : WrittenM Lowered.Expr :=
    named file span path.span.startByte (path.plainName?.map (·.text))

  /-- A path that names a declaration: a callee, the type of a record, an interface. -/
  partial def pathReference (file : FileId) (path : Path) : WrittenM (Option Lowered.Reference) := do
    return (← resolutionAt? file path.span.startByte).map (reference path.span)

  partial def typeTerm (file : FileId) : TypeExpr → WrittenM Lowered.TypeTerm
    | .bool span => return .bool span
    | .nat span => return .nat span
    | .rational span => return .rational span
    | .index span size => return .index span (← expr file size)
    | .nonzero span type => return .nonzero span (← typeTerm file type)
    | .sequence span element size =>
      return .sequence span (← typeTerm file element) (← size.mapM (expr file))
    | .tuple span fields => do
      let types ← fields.mapM fun (.tupleField _ _ type) => typeTerm file type
      return .tuple span types (fields.map fun (.tupleField _ name _) => name.map (·.text))
    | .path span path => do
      match ← pathExpr file span path with
      | .local span binder => return .local span binder
      | .reference reference => return .reference reference
      | _ => return .error span

  partial def argument (file : FileId) : Syntax.Argument → WrittenM Lowered.Argument
    | .positional span value => return .positional span (← expr file value)
    | .named span name value => return .named span name (← expr file value)
    | .spec span name value => return .spec span name (← expr file value)

  partial def callArguments (file : FileId) :
      CallArgs → WrittenM (Array Lowered.Argument × Option (Array Lowered.Argument))
    | .callArgs _ arguments witnesses => do
      return (← arguments.mapM (argument file), ← witnesses.mapM (·.mapM (argument file)))

  /-- What a comprehension or a fold ranges over: the domain first, then the binder of each item
  in a new suite (which the caller closes), and the levels of a pattern that takes an item
  apart. -/
  partial def generator (file : FileId) (pattern : Pattern) (domain : Domain) (body : Syntax.Expr) :
      WrittenM (Lowered.Generator × Array Lowered.Stmt) := do
    let .domain span start stop := domain
    let start ← expr file start
    let stop ← stop.mapM (expr file)
    pushSuite
    match stop with
    | some stop =>
      let staticIndex := match pattern with
        | .name name => staticUseIn name.text false body
        | _ => false
      let (index, levels) ← itemBinder file pattern span
      return (.range index start stop staticIndex, levels)
    | none =>
      let (item, levels) ← itemBinder file pattern span
      let iteration ← madeBinder span .iteration
      return (.collection item iteration start, levels)

  /-- The binder of an item: the name of the pattern, or a binder that lowering makes, with the
  levels that take it apart. -/
  partial def itemBinder (file : FileId) (pattern : Pattern) (span : Span) :
      WrittenM (Binder × Array Lowered.Stmt) := do
    match pattern with
    | .name name => return (← bindName name, #[])
    | .wildcard span => return (← madeBinder span .patternValue, #[])
    | _ =>
      let made ← madeBinder span .patternValue
      return (made, ← unpack file pattern (.local span made.id))

  /-- The levels of a pattern that takes a value apart, outermost first. -/
  partial def unpack (file : FileId) (pattern : Pattern) (value : Lowered.Expr) :
      WrittenM (Array Lowered.Stmt) := do
    match pattern with
    | .name _ | .wildcard _ => return #[]
    | .tuple span items =>
      let (binders, inner) ← levelBinders (items.map some)
      let mut statements := #[Lowered.Stmt.unpack span (.tuple items.size) binders none value]
      for (pattern, made) in inner do
        statements := statements ++ (← unpack file pattern (.local span made.id))
      return statements
    | .record span type fields =>
      let typeReference := (← pathReference file type).getD (.reference type.span #[])
      let declaration := match typeReference with
        | .reference _ segments => segments.back?.bind fun
          | .segment (.declaration id) _ _ => some id
          | _ => none
      let positions := fields.map fun (.fieldPattern fieldSpan name _) => (fieldSpan, name.text)
      let patterns := fields.map fun
        | .fieldPattern _ name none => some (Pattern.name name)
        | .fieldPattern _ _ (some pattern) => some pattern
      let (binders, inner) ← levelBinders patterns
      let mut statements :=
        #[Lowered.Stmt.unpack span (.record typeReference (declaration.getD 0) positions) binders none value]
      for (pattern, made) in inner do
        statements := statements ++ (← unpack file pattern (.local span made.id))
      return statements

  /-- The binders of one level: a name binds, `_` binds nothing, a nested pattern binds a value
  that lowering makes and that a level after takes apart. -/
  partial def levelBinders (patterns : Array (Option Pattern)) :
      WrittenM (Array (Option Binder) × Array (Pattern × Binder)) := do
    let mut binders := #[]
    let mut inner := #[]
    for pattern in patterns do
      match pattern with
      | some (.name name) => binders := binders.push (some (← bindName name))
      | some (.wildcard _) | none => binders := binders.push none
      | some nested =>
        let made ← madeBinder nested.span .patternValue
        binders := binders.push (some made)
        inner := inner.push (nested, made)
    return (binders, inner)

  partial def fieldValue (file : FileId) : FieldInit → WrittenM Lowered.FieldValue
    | .fieldInit span name (some value) => return .field span name (← expr file value)
    | .fieldInit span name none =>
      return .field span name (← named file name.span name.span.startByte (some name.text))

  partial def expr (file : FileId) (e : Syntax.Expr) : WrittenM Lowered.Expr := do
    match e with
    | .ifExpr span condition onTrue onFalse =>
      return .conditional span .ifThenElse (← expr file condition) (← expr file onTrue)
        (← expr file onFalse)
    | .orExpr span left right =>
      return .conditional span .or (← expr file left) (.bool span true) (← expr file right)
    | .andExpr span left right =>
      return .conditional span .and (← expr file left) (← expr file right) (.bool span false)
    | .notExpr span operand => return .operator span .not #[← expr file operand]
    | .compare span operator left right =>
      return .operator span (operatorOfCompare operator) #[← expr file left, ← expr file right]
    | .sum span operator left right =>
      return .operator span (operatorOfSum operator) #[← expr file left, ← expr file right]
    | .product span operator left right =>
      return .operator span (operatorOfProduct operator) #[← expr file left, ← expr file right]
    | .unary span operand => return .operator span .negate #[← expr file operand]
    | .power span base exponent => return .operator span .power #[← expr file base, ← expr file exponent]
    | .field span target name => return .field span (← expr file target) name
    | .method span target name staticArgs args =>
      let target ← expr file target
      let staticArgs ← staticArgs.mapM (staticArguments file)
      let (arguments, _) ← callArguments file args
      return .method span target name staticArgs arguments
    | .position span target position => return .position span (← expr file target) position.value
    | .index span target index => return .operator span .index #[← expr file target, ← expr file index]
    | .slice span target lower upper =>
      return .slice span (← expr file target) (← lower.mapM (expr file)) (← upper.mapM (expr file))
    | .number number => return .number number.span number.value
    | .byteString literal => return .bytes literal.span literal.values
    | .trueLiteral span => return .bool span true
    | .falseLiteral span => return .bool span false
    | .path span path => pathExpr file span path
    | .call span callee args =>
      let reference ← pathReference file callee
      let (arguments, witnesses) ← callArguments file args
      match reference with
      | some reference => return .call span reference arguments witnesses
      | none => return .error span
    | .record span type fields =>
      let reference ← pathReference file type
      let fields ← fields.mapM (fieldValue file)
      match reference with
      | some reference => return .record span reference fields
      | none => return .error span
    | .unit span => return .tuple span #[] #[]
    | .paren _ inner => expr file inner
    | .tuple span components =>
      let values ← components.mapM fun (.component _ _ value) => expr file value
      return .tuple span values (components.map fun (.component _ name _) => name.map (·.text))
    | .list span elements => return .list span (← elements.mapM (expr file))
    | .repetition span element count => return .repetition span (← expr file element) (← expr file count)
    | .comprehension span element pattern domain filter =>
      let (generator, levels) ← generator file pattern domain element
      let element ← expr file element
      let filter ← filter.mapM (expr file)
      popSuite
      let element := if levels.isEmpty then element else .block span levels element
      return .comprehension span element generator filter
    | .recordUpdate span value fields =>
      let value ← expr file value
      let fields ← fields.mapM fun (.fieldUpdate span name value) => do
        return Lowered.FieldValue.field span name (← expr file value)
      return .recordUpdate span value fields
    | .binderForm span operator _ pattern domain body =>
      let (generator, levels) ← generator file pattern domain body
      let body ← expr file body
      popSuite
      let body := if levels.isEmpty then body else .block span levels body
      return .fold span (foldOf operator) generator body
    | .innerProduct span _ left right => return .inner span (← expr file left) (← expr file right)
    | .boolType span => return .type (.bool span)
    | .natType span => return .type (.nat span)
    | .rationalType span => return .type (.rational span)
    | .indexType span size => return .type (.index span (← expr file size))
    | .nonzeroType span type => return .type (.nonzero span (← typeTerm file type))
end

/-- A sort of a bound. -/
def sort (file : FileId) : SortExpr → WrittenM Lowered.SortTerm
  | .nat span => return .nat span
  | .linear span => return .linear span
  | .path path => do
    return .reference ((← pathReference file path).getD (.reference path.span #[]))

/-- A constraint of a `where`. -/
def constraint (file : FileId) : Syntax.Constraint → WrittenM Lowered.Constraint
  | .bound span subject bound => do
    return .bound span (← expr file subject) (← bound.sorts.mapM (sort file))
  | .compare span operator left right => do
    return .compare span (operatorOfCompare operator) (← expr file left) (← expr file right)

end Zkc.Frontend.Names.Written
