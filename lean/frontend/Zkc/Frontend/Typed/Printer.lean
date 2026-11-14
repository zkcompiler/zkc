module

public import Std.Data.HashMap
public import Zkc.Frontend.Basic.Message
public import Zkc.Frontend.Typed.Tree

@[expose] public section

set_option autoImplicit false

/-!
# The printed form of a typed tree

A text for tests and traces: one statement per line, suites indented, every binder with its
number and type, every application with what it was resolved to, and the attributes of roles
where a pass has filled them. A local name is printed `name#n`, with the number of its binder.
The form is read by people and compared by tests; nothing parses it.
-/

namespace Zkc.Frontend.Typed

namespace Printer

structure Context where
  renderer : Renderer := .plain
  /-- The names of the roles, for the attributes of roles; a role without a name is printed by
  its number. -/
  roster : Array String := #[]
  /-- Print the type of every expression, not only of binders, literals and conversions. -/
  allTypes : Bool := false

structure State where
  lines : Array String := #[]
  names : Std.HashMap LocalId String := {}
  deriving Inhabited

abbrev PrintM := ReaderT Context (StateM State)

def line (depth : Nat) (text : String) : PrintM Unit :=
  modify fun state => { state with lines := state.lines.push ("".pushn ' ' (2 * depth) ++ text) }

def typeText (type : ClosedType) : PrintM String := return (← read).renderer.type type

def rolesText (roles : RoleSet) : PrintM String := do
  return "{" ++ ", ".intercalate (roles.names (← read).roster).toList ++ "}"

def roleText (role : Nat) : PrintM String := return ((← read).roster[role]?).getD s!"role{role}"

def localText (id : LocalId) : PrintM String := do
  return s!"{((← get).names[id]?).getD "_"}#{id}"

/-- A binder where it binds: `mut name#n: T`. -/
def binder (binder : Binder) : PrintM String := do
  modify fun state => { state with names := state.names.insert binder.id binder.name }
  let marks := (if binder.mutable then "mut " else "") ++ (if binder.linear then "linear " else "")
  return s!"{marks}{binder.name}#{binder.id}: {← typeText binder.type}"

def optionalBinder : Option Binder → PrintM String
  | some found => binder found
  | none => pure "_"

def placement (placement : Placement) : PrintM String := do
  match placement.written with
  | some roles => return s!" written @{← rolesText roles}"
  | none => return ""

def control (control : Control) : PrintM String := do
  let mut updates := #[]
  for index in [0:control.updates.size] do
    let name ← localText control.updates[index]!
    match control.carried[index]? with
    | some type => updates := updates.push s!"{name}: {← typeText type}"
    | none => updates := updates.push name
  return if updates.isEmpty then "" else s!" updates [{", ".intercalate updates.toList}]"

def literal : Literal → String
  | .nat value => toString value
  | .bool value => toString value
  | .index value => s!"index {value}"
  | .nominal data => s!"nominal {data}"
  | .bytes data => s!"bytes {data}"

partial def conversion : Conversion → String
  | .unsized => "unsized" | .indexToNat => "index_to_nat" | .widenIndex => "widen_index"
  | .fromNonzero => "from_nonzero"
  | .sized => "sized!" | .bounded => "below!" | .nonzero => "nonzero!"
  | .elements inner => s!"elements({conversion inner})"
  | .components inner =>
    let parts := inner.toList.map fun
      | some found => conversion found
      | none => "_"
    s!"components({", ".intercalate parts})"
  | .empty => "empty"
  | .andThen first _ second => s!"{conversion first}; {conversion second}"

def callee : Callee → PrintM String
  | .instance id => return s!"call {(← read).renderer.instance id}"
  | .row row => do
    let statics := row.statics.toList.map (← read).renderer.value
    return if statics.isEmpty then s!"row {row.name}" else s!"row {row.name}<{", ".intercalate statics}>"
  | .boundRow row => return s!"row {row.key.name}"
  | .operation operation => return operation.name
  | .member «module» name _ => return s!"member {(← read).renderer.instance «module»}::{name}"
  | .specification name => return s!"spec {name}"

def construction : Construction → PrintM String
  | .tuple => return "tuple"
  | .sequence => return "seq"
  | .record id => return s!"record {(← read).renderer.instance id}"
  | .alternative id index => return s!"variant {(← read).renderer.instance id}.{index}"

def joined (parts : Array String) : String := ", ".intercalate parts.toList

def reason : Zkc.Core.Reason → String
  | .reject => "reject" | .abort => "abort" | .exhausted => "exhausted" | .refused => "refused"

mutual
  /-- An expression on one line. A block is printed between braces, its statements separated
  by `;`. -/
  partial def expr (expression : Expr) : PrintM String := do
    let text ← match expression with
      | .literal info value => pure s!"({literal value} : {← typeText info.type})"
      | .staticValue _ value _ => pure s!"static {value}"
      | .local _ id => localText id
      | .apply _ applied arguments =>
        pure s!"{← callee applied}({joined (← arguments.mapM expr)})"
      | .construct _ what parts => pure s!"make {← construction what}({joined (← parts.mapM expr)})"
      | .project _ target position _ => pure s!"get({← expr target}, {position})"
      | .convert info applied value _ =>
        pure s!"convert {conversion applied}({← expr value} to {← typeText info.type})"
      | .conditional _ form condition onTrue onFalse =>
        let word := match form with
          | .ifThenElse => "if" | .and => "if[and]" | .or => "if[or]"
        pure s!"{word} {← expr condition} then {← expr onTrue} else {← expr onFalse}"
      | .block _ statements result =>
        let saved := (← get).lines
        modify fun state => { state with lines := #[] }
        suite 0 statements
        let inner := (← get).lines.map (·.trimAsciiStart.toString)
        modify fun state => { state with lines := saved }
        pure ("{ " ++ "; ".intercalate (inner.push (← expr result)).toList ++ " }")
      | .error info evaluated =>
        pure s!"(error({joined (← evaluated.mapM expr)}) : {← typeText info.type})"
    match expression with
    | .literal .. | .convert .. | .error .. => return text
    | _ =>
      if (← read).allTypes then return s!"({text} : {← typeText expression.type})"
      else return text

  partial def suite (depth : Nat) (statements : Array Stmt) : PrintM Unit := do
    if statements.isEmpty then line depth "()"
    for statement in statements do stmt depth statement

  partial def stmt (depth : Nat) : Stmt → PrintM Unit
    | .bind _ bound value placed => do
      let value ← expr value
      line depth s!"{← binder bound} = {value}{← placement placed}"
    | .unpack _ binders value placed => do
      let value ← expr value
      line depth s!"({joined (← binders.mapM optionalBinder)}) = {value}{← placement placed}"
    | .update _ target value placed => do
      line depth s!"{← localText target} := {← expr value}{← placement placed}"
    | .guard _ condition stops placed => do
      line depth s!"guard {← expr condition} else {reason stops}{← placement placed}"
    | .if _ condition onTrue onFalse attributes => do
      line depth s!"if {← expr condition}:{← control attributes}"
      suite (depth + 1) onTrue
      line depth "else:"
      suite (depth + 1) onFalse
    | .match _ scrutinee bound «variant» cases attributes => do
      let scrutinee ← expr scrutinee
      let bound ← match bound with
        | some bound => pure s!"{← binder bound} = "
        | none => pure ""
      line depth
        s!"match {bound}{scrutinee} of {(← read).renderer.instance «variant»}:{← control attributes}"
      for (.case _ alternatives payload body) in cases do
        line (depth + 1) s!"case {alternatives.toList}({joined (← payload.mapM optionalBinder)}):"
        suite (depth + 2) body
    | .for _ (.loop index domain collected body) attributes => do
      let index ← binder index
      let domain ← match domain with
        | .range start stop count =>
          let count := match count with
            | some count => s!" count {count}"
            | none => ""
          pure s!"{← expr start}..{← expr stop}{count}"
        | .collection source item size =>
          let size := match size with
            | some size => s!" size {size}"
            | none => ""
          pure s!"{← expr source} item {← binder item}{size}"
      let names ← collected.mapM binder
      let collecting := if names.isEmpty then "" else s!" collect ({joined names})"
      match body with
      | .uniform statements values =>
        line depth s!"for {index} in {domain}{collecting}:{← control attributes}"
        suite (depth + 1) statements
        unless values.isEmpty do line (depth + 1) s!"collected ({joined (← values.mapM expr)})"
      | .empty statements values =>
        line depth s!"for {index} in {domain}{collecting} of no iteration, typed apart:"
        suite (depth + 1) statements
        unless values.isEmpty do line (depth + 1) s!"collected ({joined (← values.mapM expr)})"
      | .stepped iterations =>
        line depth s!"for {index} in {domain}{collecting} stepped:{← control attributes}"
        for (.iteration value statements values) in iterations do
          line (depth + 1) s!"iteration {value}:"
          suite (depth + 2) statements
          unless values.isEmpty do line (depth + 2) s!"collected ({joined (← values.mapM expr)})"
    | .scope _ body => do
      line depth "scope:"
      suite (depth + 1) body
    | .event _ number what => do
      match what with
      | .send bound payload sender receivers =>
        let sender ← match sender with
          | some role => pure s!" from {← roleText role}"
          | none => pure ""
        line depth s!"{← optionalBinder bound} <- send {← expr payload}{sender} to {joined (← receivers.mapM roleText)} [event {number}]"
      | .draw bound law sender receivers =>
        line depth s!"{← optionalBinder bound} <- draw {← callee (.row law)} from {← roleText sender} to {joined (← receivers.mapM roleText)} [event {number}]"
      | .sample bound law role =>
        line depth s!"{← optionalBinder bound} <- sample {← callee (.row law)} at {← roleText role} [event {number}]"
      | .attempt bound role =>
        line depth s!"{← optionalBinder bound} <- attempt at {← roleText role} [event {number}]"
      | .apply results applied arguments specification roleMap _ =>
        let specification ← specification.mapM fun (port, value) => do
          return s!"spec {port} = {← expr value}"
        line depth s!"({joined (← results.mapM optionalBinder)}) <- apply {(← read).renderer.instance applied}({joined ((← arguments.mapM expr) ++ specification)}) @({joined (← roleMap.mapM roleText)}) [event {number}]"
    | .error _ binders => do
      line depth s!"error ({joined (← binders.mapM binder)})"
end

def body : Body → PrintM Unit
  | .function found => do
    line 0 s!"function({joined (← found.parameters.mapM binder)}):"
    suite 1 found.statements
    line 1 s!"return {← expr found.result}"
  | .protocol found => do
    let ports ← found.ports.mapM fun port => do
      let holders ← if port.specification then pure "spec" else pure s!"@{← rolesText port.holders}"
      return s!"{← binder port.binder} {holders}"
    line 0 s!"protocol roles({joined found.roster})({joined ports}):"
    suite 1 found.statements
    let results ← found.results.mapM fun result => do
      return s!"{result.name} = {← expr result.value} @{← rolesText result.holders}"
    line 1 s!"return ({joined results})"
  | .row row => do line 0 s!"= {← callee (.row row)}"
  | .external name => line 0 s!"= external(\"{name}\")"

end Printer

/-- The roster of a body: the names of its roles, none for local code. -/
def Body.roster : Body → Array String
  | .protocol body => body.roster
  | _ => #[]

/-- The printed form of a body. -/
def Body.print (body : Body) (renderer : Renderer := .plain) (allTypes : Bool := false) : String :=
  let (_, state) := ((Printer.body body).run { renderer, roster := body.roster, allTypes }).run {}
  "\n".intercalate state.lines.toList

/-- The printed form of a definition: its body and, when it has one, its generic definition. -/
def Definition.print (definition : Definition) (renderer : Renderer := .plain)
    (allTypes : Bool := false) : String :=
  let head := s!"{renderer.instance definition.instance}\n{definition.body.print renderer allTypes}"
  let waiting := match definition.waiting with
    | some reason => s!"\nwaiting: {reason}"
    | none => ""
  match definition.generic with
  | some generic => s!"{head}{waiting}\ngeneric:\n{generic.print renderer allTypes}"
  | none => head ++ waiting

end Zkc.Frontend.Typed
