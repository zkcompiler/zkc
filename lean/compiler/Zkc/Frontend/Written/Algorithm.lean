module

public import Zkc.Frontend.Written.Program
public import Zkc.Frontend.Syntax.Spans

@[expose] public section
set_option autoImplicit false

namespace Zkc.Frontend.Written
open Syntax

def refuse {α : Type} (span : Span) (code message : String) : ExportM α :=
  .error s!"{span.file}:{span.render}: {code}: {message}"

inductive ValueSort where | point | scalar | boolean | runs
  deriving BEq, Repr, Inhabited

structure Value where
  sort : ValueSort
  term : String
  deriving Inhabited

structure View where
  commitment : Typing.SiteEntry
  challenge : Typing.SiteEntry
  response : Typing.SiteEntry
  prover : Nat
  verifier : Nat

def atSort (where_ : Span) (t : ValueSort) (v : Value) : ExportM String :=
  if v.sort == t then pure v.term else refuse where_ "WK-TYPE" s!"expected {repr t}, got {repr v.sort}"

abbrev Locals := List (String × Value)

def localName (e : Expr) : ExportM String := do
  let .path _ path := e | refuse e.span "WK-BINDER" "expected a local source operand"
  let some n := path.plainName? | refuse path.span "WK-BINDER" "expected one local binder"
  return n.text

/-- Lower the supported expression fragment to typed Lean operations. Only compiler-selected
identifiers reach generated code. Source division and guards carry failure in Option. -/
partial def value (view : View) (locals : Locals) (e : Expr) : ExportM Value := do
  let child := value view locals
  let bad := fun msg => refuse e.span "WK-EXPR" msg
  match e with
  | .paren _ x => child x
  | .path .. =>
    let n ← localName e
    let some v := locals.lookup n | bad s!"unbound source operand {n}"
    return v
  | .number n =>
    if n.value == 0 then return ⟨.scalar, "ops.zero"⟩
    bad "only the scalar literal zero is supported"
  | .trueLiteral _ => return ⟨.boolean, "true"⟩
  | .falseLiteral _ => return ⟨.boolean, "false"⟩
  | .field _ (.index _ source (.number n)) field =>
    let _ ← atSort source.span .runs (← child source)
    let leaf ← match n.value with
      | 0 => pure "left" | 1 => pure "right"
      | _ => refuse n.span "WK-VIEW" "leaf index is outside Runs<2>"
    if view.commitment.name == some field.text then return ⟨.point, "commitment"⟩
    if view.challenge.name == some field.text then return ⟨.scalar, leaf ++ ".challenge"⟩
    if view.response.name == some field.text then return ⟨.scalar, leaf ++ ".suffix"⟩
    refuse field.span "WK-VIEW" s!"field {field.text} is absent from the deciding role's run"
  | .sum _ .subtract a b =>
    return ⟨.scalar, s!"(ops.sub {← atSort a.span .scalar (← child a)} {← atSort b.span .scalar (← child b)})"⟩
  | .sum _ .add a b =>
    return ⟨.point, s!"(ops.add {← atSort a.span .point (← child a)} {← atSort b.span .point (← child b)})"⟩
  | .product _ .multiply a b =>
    let x ← child a
    let y ← atSort b.span .scalar (← child b)
    match x.sort with
    | .point => return ⟨.point, s!"(ops.scale {x.term} {y})"⟩
    | .scalar => return ⟨.scalar, s!"(ops.mul {x.term} {y})"⟩
    | _ => bad "multiplication needs a point or scalar"
  | .product _ .divide a b =>
    return ⟨.scalar, s!"(← divide ops {← atSort a.span .scalar (← child a)} {← atSort b.span .scalar (← child b)})"⟩
  | .compare _ op a b =>
    let x ← child a
    unless [.scalar, .point, .boolean].contains x.sort do refuse e.span "WK-EXPR" "equality is undefined on a run view"
    let y ← atSort b.span x.sort (← child b)
    let op ← match op with
      | .equal => pure "=" | .notEqual => pure "≠"
      | _ => refuse e.span "WK-EXPR" "unsupported comparison"
    return ⟨.boolean, s!"(decide ({x.term} {op} {y}))"⟩
  | _ => bad "unsupported expression in the written clause"

def algorithm (view : View) (params : Locals) (result : ValueSort) (body : Body) : ExportM String := do
  let (steps, out) := match body with
    | .expression _ x | .suiteExpression _ x => (#[], x)
    | .statements _ steps x => (steps, x)
  let mut locals := params
  let mut lines := #[]
  for stmt in steps do
    match stmt with
    | .binding _ (.name name) none none x =>
      let v ← value view locals x
      let slot := s!"local{lines.size}"
      locals := (name.text, {v with term := slot}) :: locals
      lines := lines.push s!"  let {slot} := {v.term}"
    | .guard _ none x none | .guard _ none x (some (.reject _)) =>
      let test ← atSort x.span .boolean (← value view locals x)
      lines := lines.push s!"  require {test}"
    | _ => refuse stmt.span "WK-BODY" "unsupported statement in the written clause"
  let r ← atSort out.span result (← value view locals out)
  return "\n".intercalate (lines.push s!"  return {r}").toList

end Zkc.Frontend.Written
