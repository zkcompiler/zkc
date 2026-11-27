import Lean
import ZkcFormal.Written.Publish
import Zkc.Frontend.Written.Statement

/-!
Controls of the shape of what the issuer publishes, read from the built modules.

* `#data_module M of S`: the data module `M` with its subject `S` imports the modules of the
  issuer's list (`Statements.dataImports`) and no other, and through them no module of the
  formal library; each of its declarations is a definition that is no instance and whose type
  does not end in `Prop`, or a theorem that the subject reaches (a lookup) or one of the package's
  listed names; it declares no inductive type; and, reading the subject's rows as the commands
  read them, each row's bound is a declaration of the module at two numerals and each row's
  table a declaration of the module that reads no other. The rows are followed from the subject:
  a bound or a table is told by its place in a row, not by its name.
* `#challenge_module C over M`: every module that the challenge `C` imports, directly or not, is
  the data module `M`, a module that `M` imports, or a module that the library's
  `ZkcFormal.Written.Publish` imports. A views module, a fees module and an author's tool are none
  of these.

Each lists what is allowed.
-/

open Lean Elab Command

namespace ZkcFormalTests.PublicationControl

/-- The modules that a module imports, directly or not, itself included. -/
partial def closure (env : Environment) (start : Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut todo := [start]
  while !todo.isEmpty do
    let name := todo.head!
    todo := todo.tail!
    if seen.contains name then continue
    seen := seen.insert name
    if let some index := env.getModuleIdx? name then
      for imported in env.header.moduleData[index.toNat]!.imports do
        todo := imported.module :: todo
  return seen

private def digitsAfter (s p : String) : Bool :=
  let rest := s.toList.drop p.length
  s.startsWith p && !rest.isEmpty && rest.all Char.isDigit

/-- The theorems that a data module may hold, in the subject's name space: the package's (with the
equation `elaborated<k>.eq` of each definition that the kernel elaborated) and the lookups'. -/
def allowedTheorem (space : Name) : Name → Bool
  | .str (.str parent definition) "eq" => parent == space && digitsAfter definition "elaborated"
  | .str parent last => parent == space &&
    ["admitted_exists", "elaborated", "readback"].contains last
  | _ => false

private def numeral (e : Expr) : Bool :=
  match e.consumeMData with
  | .lit (.natVal _) => true
  | e => e.isAppOfArity ``OfNat.ofNat 3 && (e.getArg! 1).consumeMData.isRawNatLit

/-- The declarations of a module that a declaration of it reaches through types and values. -/
private partial def reached (env : Environment) (home : ModuleIdx) : List Name → NameSet → NameSet
  | [], seen => seen
  | name :: rest, seen =>
    if seen.contains name then reached env home rest seen else
    match env.find? name with
    | none => reached env home rest seen
    | some info =>
      let used := info.type.getUsedConstants ++
        ((info.value? (allowOpaque := true)).map (·.getUsedConstants)).getD #[]
      reached env home (used.toList.filter (env.getModuleIdxFor? · == some home) ++ rest) (seen.insert name)

elab "#data_module " m:ident " of " s:ident : command => do
  let env ← getEnv
  let some index := env.getModuleIdx? m.getId | throwError "data control: no module {m.getId}"
  for imported in (closure env m.getId).toList do
    if (`ZkcFormal).isPrefixOf imported then
      throwError "data control: {m.getId} imports the formal library's {imported}"
  let listed := `Init :: Zkc.Frontend.Written.Statements.dataImports.map String.toName
  for imported in env.header.moduleData[index.toNat]!.imports do
    unless listed.contains imported.module do
      throwError "data control: {m.getId} imports {imported.module}, which is none of the issuer's list"
  let subject ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo s
  let inModule (name : Name) : Bool := env.getModuleIdxFor? name == some index
  unless inModule subject do throwError "data control: the subject {subject} is no declaration of {m.getId}"
  let space := subject.getPrefix
  -- The rows, read as the commands read them: each bound is a declaration of the module at two
  -- numerals, and each table a declaration of the module that reads no other.
  for row in ← liftTermElabM (ZkcFormal.Written.Publish.rows subject) do
    let number ← liftTermElabM row.number
    let some bound := number.bound.constName?
      | throwError "data control: the bound of the row at {row.path} is no declaration:{indentExpr number.bound}"
    let some (.defnInfo d) := env.find? bound
      | throwError "data control: the bound {bound} is no definition"
    unless inModule bound && d.value.isAppOfArity ``Zkc.Subject.Bound.mk 3 && numeral (d.value.getArg! 0) &&
        numeral (d.value.getArg! 1) do
      throwError "data control: the bound {bound} is not two numerals:{indentExpr d.value}"
    if let some table := number.table then
      let some caps := table.constName?
        | throwError "data control: the table of the row at {row.path} is no declaration:{indentExpr table}"
      let some (.defnInfo t) := env.find? caps
        | throwError "data control: the table {caps} is no definition"
      if let some read := t.value.getUsedConstants.find? inModule then
        throwError "data control: the table {caps} reads {read}"
  -- The declarations: no proposition, no instance, no inductive type; a theorem is one that the
  -- subject reaches (a lookup of the root or of a relation) or one of the package's.
  let fromSubject := reached env index [subject] {}
  for name in env.header.moduleData[index.toNat]!.constNames do
    if name.isInternalDetail then continue
    let some info := env.find? name | continue
    match info with
    | .thmInfo _ =>
      unless fromSubject.contains name || allowedTheorem space name do
        throwError "data control: {m.getId} states the theorem {name}, which is none of a data module's"
    | .defnInfo d =>
      if d.type.getForallBody.isProp || (← liftTermElabM (Meta.forallTelescopeReducing d.type fun _ body =>
          return (← Meta.whnf body).isProp)) then
        throwError "data control: {m.getId} defines the proposition {name}"
      if Lean.Meta.isInstanceCore env name then
        throwError "data control: {m.getId} declares the instance {name}"
    | .opaqueInfo _ | .axiomInfo _ =>
      throwError "data control: {m.getId} declares {name} without a value"
    | .inductInfo _ =>
      throwError "data control: {m.getId} declares the inductive type {name}"
    | _ => pure ()
  logInfo m!"{m.getId}: a data module"

elab "#challenge_module " c:ident " over " m:ident : command => do
  let env ← getEnv
  unless (env.getModuleIdx? c.getId).isSome do throwError "challenge control: no module {c.getId}"
  let allowed := (closure env m.getId).union (closure env `ZkcFormal.Written.Publish)
  for imported in (closure env c.getId).toList do
    unless imported == c.getId || allowed.contains imported do
      throwError "challenge control: {c.getId} imports {imported}, which neither the data module nor the publication command imports"
  logInfo m!"{c.getId}: a challenge over {m.getId}"

end ZkcFormalTests.PublicationControl
