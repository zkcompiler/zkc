import Lean
import ZkcFormal.Written.Publish
import Zkc.Frontend.Written.Statement

/-!
Controls of the shape of what the issuer publishes, read from the built modules.

* `#data_module M of S`: the data module `M` with its subject `S` imports the modules of the
  issuer's list (`Statements.dataImports`) and no other, and through them no module of the
  formal library; each of its declarations is a definition that is no instance, whose type
  names no `Prop` and is no proposition, or a theorem that the subject reaches and that states a
  lookup in the installed program, or one of the package's listed names; it declares no inductive type; the subject, its table of rows, each row, its
  fields and its number are constructors over declarations of the module as they stand
  (`rowsAsTheyStand`); and, reading the subject's rows as the commands read them, each row's
  bound is a declaration of the module at two numerals and each row's table a declaration of
  the module that reads no other. The rows are followed from the subject: a bound or a table is
  told by its place in a row, not by its name.
* `#challenge_module C over M`: every module that the challenge `C` imports, directly or not, is
  the data module `M`, a module that `M` imports, or a module that the library's
  `ZkcFormal.Written.Publish` imports. A views module, a fees module and an author's tool are none
  of these.
* `#challenge_theorems C of S published … beside …`: the theorems that the challenge `C` states are
  those of the rows of `S`, each with the statement that the control spells from the row's short
  application and bound, and the theorems that the check lists beside them; the names that a
  judgment is given are the rows' theorems.

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

/-- The theorems that a data module may hold by name, in the subject's name space: the package's
(with the equation `elaborated<k>.eq` of each definition that the kernel elaborated). A lookup is
told by its statement (`isLookup`). -/
def allowedTheorem (space : Name) : Name → Bool
  | .str (.str parent definition) "eq" => parent == space && digitsAfter definition "elaborated"
  | .str parent last => parent == space &&
    ["admitted_exists", "elaborated", "readback"].contains last
  | _ => false

/-- A numeral of `Nat` as Lean elaborates one: a literal, or `OfNat.ofNat Nat n (instOfNatNat n)`
at one literal `n`. Another instance could compute the number from anything. -/
private def numeral (e : Expr) : Bool :=
  match e.consumeMData with
  | .lit (.natVal _) => true
  | e =>
    e.isAppOfArity ``OfNat.ofNat 3 && (e.getArg! 0).consumeMData.isConstOf ``Nat &&
      (let n := (e.getArg! 1).consumeMData
       let inst := (e.getArg! 2).consumeMData
       n.isRawNatLit && inst.isAppOfArity ``instOfNatNat 1 && inst.appArg!.consumeMData == n)

/-- The statement of a lookup in an installed program: `p.find key = some _` or
`p.findProtocol key = some _`. -/
private def isLookup (type : Expr) : Bool :=
  type.isAppOfArity ``Eq 3 &&
    (let found := (type.getArg! 1).getAppFn
     found.isConstOf ``Zkc.Core.Typed.find || found.isConstOf ``Zkc.Core.Typed.findProtocol) &&
    (type.getArg! 2).isAppOf ``Option.some

/-- The head of a declaration's type after its binders, with definitions unfolded: an alias of a
row's type is that type. -/
def typeHead (name : Name) : MetaM (Option Name) := do
  let type := (← getConstInfo name).type
  Meta.forallTelescopeReducing type fun _ body => return (← Meta.whnf body).getAppFn.constName?

/-- **The rows of a subject as they stand.** The subject is its constructor over a table of rows
whose selector reads, of the module, only declarations of rows; each such row is its constructor
with a declaration of the module for its fields; the fields are their constructor with a number
that is a constructor over declarations of the module (a table, a bound; a table or none). So no
row, no fields and no number is chosen by a computation over anything else of the module. -/
def rowsAsTheyStand (inModule : Name → Bool) (subject : Name) : MetaM Unit := do
  let valueOf (name : Name) : MetaM Expr := do
    let some value := (← getConstInfo name).value? | throwError "data control: {name} has no value"
    return value.consumeMData
  let declared (e : Expr) : Bool := e.consumeMData.constName?.any inModule
  let value ← valueOf subject
  unless value.isAppOfArity ``Zkc.Subject.WrittenSubject.mk 6 do
    throwError "data control: the subject {subject} is not its constructor:{indentExpr value}"
  let table := (value.getArg! 4).consumeMData
  unless table.isAppOfArity ``Zkc.Subject.BoundedTable.mk 3 do
    throwError "data control: the table of rows of {subject} is not its constructor:{indentExpr table}"
  for slot in (table.getArg! 2).getUsedConstants do
    unless inModule slot do continue
    unless (← typeHead slot) == some ``Zkc.Subject.GoalSlot do
      throwError "data control: the table of rows of {subject} reads {slot}, which is no row"
    let row ← valueOf slot
    unless row.isAppOfArity ``Zkc.Subject.GoalSlot.mk 5 && declared (row.getArg! 4) do
      throwError "data control: the row {slot} is not its constructor over a declaration of its fields:{indentExpr row}"
    let fieldsName := (row.getArg! 4).consumeMData.constName!
    let fields ← valueOf fieldsName
    unless fields.isAppOfArity ``Zkc.Subject.GoalFields.mk 2 do
      throwError "data control: the fields {fieldsName} are not their constructor:{indentExpr fields}"
    let number := (fields.getArg! 1).consumeMData
    let total := number.isAppOfArity ``Zkc.Subject.GoalNumber.total 2 &&
      declared (number.getArg! 0) && declared (number.getArg! 1)
    let caps := (number.getArg! 1).consumeMData
    let ceiling := number.isAppOfArity ``Zkc.Subject.GoalNumber.ceiling 2 && declared (number.getArg! 0) &&
      (caps.isAppOfArity ``Option.none 1 || (caps.isAppOfArity ``Option.some 2 && declared caps.appArg!))
    unless total || ceiling do
      throwError "data control: the number of {fieldsName} is not a constructor over declarations:{indentExpr number}"

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
  -- The rows as they stand, then as the commands read them: each bound is a declaration of the
  -- module at two numerals, and each table a declaration of the module that reads no other.
  liftTermElabM (rowsAsTheyStand inModule subject)
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
      unless inModule caps do throwError "data control: the table {caps} is no declaration of {m.getId}"
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
      unless (fromSubject.contains name && isLookup info.type) || allowedTheorem space name do
        throwError "data control: {m.getId} states the theorem {name}, which is none of a data module's"
    | .defnInfo d =>
      if (d.type.find? (·.isProp)).isSome || (← liftTermElabM (Meta.forallTelescopeReducing d.type fun _ body =>
          return (← Meta.whnf body).isProp)) then
        throwError "data control: {m.getId} defines the proposition {name}"
      if ← liftTermElabM (Meta.isProp d.type) then
        throwError "data control: {m.getId} holds a proof in the definition {name}"
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

/-- The theorems of a row as this control lists them: a soundness row publishes `sound` and `met`.
The control has no expectation of a row of another property and refuses it. -/
private def publishedBy (row : ZkcFormal.Written.Publish.Row) : MetaM (List String) := do
  unless row.property == ``Zkc.Security.Property.soundness do
    throwError "challenge control: no expectation for a row of the property {row.property}"
  return ["sound", "met"]

/-- The statement of a row's theorem as this control spells it: source text over the row's short
application and bound, elaborated here. It is not the library's builder of a statement. -/
private def spelled (row : ZkcFormal.Written.Publish.Row) (which : String) : TermElabM Expr := do
  let application := mkCIdent row.application
  let term ← match which with
    | "sound" => do
      let bound := mkCIdent (← row.bound)
      `(ZkcFormal.Written.Soundness.Result ZkcFormal.Written.StandardInterpretation.model $application
          ZkcFormal.Written.StandardInterpretation.draws ZkcFormal.Written.StandardInterpretation.covers
          (Zkc.Subject.Bound.limit $bound))
    | "met" =>
      `(ZkcFormal.Written.Soundness.Witnessed ZkcFormal.Written.StandardInterpretation.model $application
          ZkcFormal.Written.StandardInterpretation.draws)
    | other => throwError "challenge control: no spelling of the theorem `{other}`"
  let e ← Term.elabTerm term (some (.sort .zero))
  Term.synthesizeSyntheticMVarsNoPostponing
  instantiateMVars e

/-- `#challenge_theorems C of S published "a", … beside "b", …`: the theorems of the challenge `C`
are those of the rows of the subject `S`, each under the row's path with the statement that this
control spells (compared whole, by `Expr.equal`), and the listed theorems `beside` them (a check's
consumers), and no other; and the names `published`, which a judgment is given, are exactly the
rows' theorems. -/
elab "#challenge_theorems " c:ident " of " s:ident " published " published:str,* " beside " beside:str,* : command => do
  let env ← getEnv
  let some index := env.getModuleIdx? c.getId | throwError "challenge control: no module {c.getId}"
  let subject ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo s
  let space := subject.getPrefix
  let declared := (env.header.moduleData[index.toNat]!.constNames.toList.filter fun name =>
    !name.isInternalDetail && (match env.find? name with | some (.thmInfo _) => true | _ => false)).map toString
  let published := published.getElems.toList.map (·.getString)
  let beside := beside.getElems.toList.map (·.getString)
  let mut expected : List String := []
  for row in ← liftTermElabM (ZkcFormal.Written.Publish.rows subject) do
    for which in ← liftTermElabM (publishedBy row) do
      let name := Name.str (row.path.foldl (fun parent component => Name.str parent component) space) which
      unless env.getModuleIdxFor? name == some index do
        throwError "challenge control: {c.getId} does not state {name}"
      let some (.thmInfo info) := env.find? name
        | throwError "challenge control: {name} of {c.getId} is no theorem"
      let term ← liftTermElabM (spelled row which)
      unless Expr.equal info.type term do
        throwError m!"challenge control: {name}: the challenge states{indentExpr info.type}\nthe control spells{indentExpr term}"
      expected := expected ++ [toString name]
  let same (a b : List String) := a.length == b.length && a.all b.contains && b.all a.contains
  unless same published expected do
    throwError "challenge control: the judgment is given {published}; the rows of {subject} publish {expected}"
  unless same declared (expected ++ beside) do
    throwError "challenge control: {c.getId} states {declared}; the rows of {subject} publish {expected} and the check states {beside} beside them"
  logInfo m!"{c.getId}: {expected.length} theorems of the rows of {subject}, each the statement that the control spells, and {beside.length} beside them"

end ZkcFormalTests.PublicationControl
