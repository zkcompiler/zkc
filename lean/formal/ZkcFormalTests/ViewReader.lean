import Lean
import ZkcFormal.Written.Publish
import ZkcFormal.Written.StandardInterpretation

/-!
A check's reader of a declared view: the binders that have a source's shape (`input_<name>`,
`valid_input_<name>`, `port<k>`, `valid_port<k>`, `witness<i>`), in the order of the term, are
exactly the ones that the check spells from a second reading of the source, each with its name
and its type. A value binder's type is held by definitional equality to the value type of the
deployed input that it binds, read from the subject (`root.entry.header.ins`); a validity
binder's type to that input's validity at the value binder that the reader met for it; a witness
binder's type to the value type of the relation's witness parameter, read from the row's short
application. The library's own binders are passed over. The proposition itself is held to the
published statement by the view's `view_iff`, which this reader does not read.

The reader uses neither the naming nor the presenting of `ZkcFormal.Written.Views`.
-/

open Lean Meta Elab Command Term

namespace ZkcFormalTests.ViewReader

/-- What an expected binder binds: a deployed input by its ordinal in the header, that input's
validity, or a witness by its position. -/
inductive Binds where
  | input (k : Nat)
  | valid (k : Nat)
  | witness (i : Nat)

/-- A row of the reader: `| <name> := input <k>`, `valid <k>` or `witness <i>`. -/
syntax viewBinder := "|" ident " := " ident num

private def digitsAfter (s p : String) : Bool :=
  let rest := s.toList.drop p.length
  s.startsWith p && !rest.isEmpty && rest.all Char.isDigit

/-- Whether a binder's name has the shape of a source's name. -/
def sourceShaped (x : Name) : Bool :=
  match x with
  | .str .anonymous s =>
    s.startsWith "input_" || s.startsWith "valid_input_" || digitsAfter s "port" ||
      digitsAfter s "valid_port" || digitsAfter s "witness"
  | _ => false

private partial def listCells (e : Expr) : MetaM (List Expr) := do
  let s ← whnf e
  match_expr s with
  | List.nil _ => return []
  | List.cons _ x xs => return x :: (← listCells xs)
  | _ => throwError "view reader: expected a concrete list, got{indentExpr s}"

/-- What the reader holds while it walks a view. -/
structure Reading where
  view : Name
  model : Expr
  ports : Array Expr
  witnesses : Array Expr
  expected : Array (Name × Binds)
  index : Nat := 0
  values : Std.HashMap Nat Expr := {}

/-- A binder that has a source's shape, compared with the next expected one. -/
private def compare (x : Name) (v t : Expr) : StateRefT Reading MetaM Unit := do
  let r ← get
  let some (name, binds) := r.expected[r.index]?
    | throwError "{r.view}: the view binds `{x}` beyond the binders that the source gives"
  unless x == name do
    throwError "{r.view}: at the source's binder {r.index} the view binds `{x}` where the source gives `{name}`"
  let portAt (k : Nat) : MetaM Expr := do
    let some port := r.ports[k]? | throwError "{r.view}: the root deploys no input {k}"
    mkProjection port `ty
  let expectedType ← match binds with
    | .input k => do mkAppM ``Zkc.Core.Model.Val #[r.model, ← portAt k]
    | .valid k => do
      let some value := r.values[k]? | throwError "{r.view}: `{x}` stands before the value of input {k}"
      mkAppM ``Zkc.Core.Model.Valid #[r.model, ← portAt k, value]
    | .witness i => do
      let some ty := r.witnesses[i]? | throwError "{r.view}: the relation has no witness {i}"
      mkAppM ``Zkc.Core.Model.Val #[r.model, ty]
  unless ← isDefEq t expectedType do
    throwError "{r.view}: the binder `{x}` has the type{indentExpr t}\nwhere the source gives{indentExpr expectedType}"
  if let .input k := binds then modify fun r => { r with values := r.values.insert k v }
  modify fun r => { r with index := r.index + 1 }

/-- Walk a term in its order, comparing each binder of a source's shape. -/
private partial def walk (e : Expr) : StateRefT Reading MetaM Unit := do
  match e with
  | .forallE x t b bi | .lam x t b bi =>
    walk t
    withLocalDecl x bi t fun v => do
      if sourceShaped x then compare x v t
      walk (b.instantiate1 v)
  | .letE x t v b _ =>
    walk t
    walk v
    withLetDecl x t v fun fv => walk (b.instantiate1 fv)
  | .app f a => walk f; walk a
  | .mdata _ b => walk b
  | .proj _ _ b => walk b
  | _ => pure ()

/-- `#view_reads V of S at i | <name> := input <k> | …`: the binders of a source's shape in the
value of the view `V` are exactly the rows, in their order, each with its type, read from the
subject `S` (its root's deployed inputs, and the witnesses of the short application of its goal
row `i`), at the standard interpretation's model. A row `i` past the subject's rows is refused
(`Publish.rowAt`). -/
elab "#view_reads " v:ident " of " s:ident " at " i:num rows:viewBinder* : command => liftTermElabM do
  let view ← realizeGlobalConstNoOverloadWithInfo v
  let subject ← realizeGlobalConstNoOverloadWithInfo s
  let some (.defnInfo info) := (← getEnv).find? view | throwError "{view} is no definition"
  let mut expected := #[]
  for row in rows do
    let `(viewBinder| | $x:ident := $kind:ident $n:num) := row | throwUnsupportedSyntax
    let binds ← match kind.getId.toString with
      | "input" => pure (Binds.input n.getNat)
      | "valid" => pure (Binds.valid n.getNat)
      | "witness" => pure (Binds.witness n.getNat)
      | other => throwErrorAt kind "view reader: no binder kind {other}"
    expected := expected.push (x.getId, binds)
  let subjectType ← whnf (← inferType (← mkConstWithLevelParams subject))
  let root := subjectType.appArg!
  let ports ← listCells (← mkProjection (← mkProjection (← mkProjection root `entry) `header) `ins)
  let t ← ZkcFormal.Written.Publish.tables subject
  let row ← ZkcFormal.Written.Publish.rowAt t i.getNat
  let app := Lean.mkConst row.application
  let relation ← mkProjection (← mkProjection (← mkProjection app `relation) `header) `ins
  let arity ← mkProjection (← mkProjection app `arity) `val
  let witnesses ← listCells (← mkAppM ``List.drop #[arity, relation])
  let model := Lean.mkConst ``ZkcFormal.Written.StandardInterpretation.model
  let ((), r) ← (walk info.value).run
    { view, model, ports := ports.toArray, witnesses := witnesses.toArray, expected }
  if let some (name, _) := r.expected[r.index]? then
    throwError "{view}: the view does not bind `{name}`, which the source gives"
  logInfo m!"{view}: the binders of the source, by name and type ({r.index})"

end ZkcFormalTests.ViewReader
