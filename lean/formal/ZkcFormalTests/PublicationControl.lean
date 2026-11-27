import Lean
import ZkcFormal.Written.Publish
import Zkc.Frontend.Written.Statement

/-!
Controls of the shape of what the issuer publishes, read from the built modules.

* `#data_module M of S`: the data module `M` with its subject `S` imports the modules of the
  issuer's list (`Statements.dataImports`) and no other, and through them no module of the
  formal library; each of its declarations is a definition that is no instance, whose type
  names no `Prop` and is no proposition, or a theorem that the subject reaches and that states a
  lookup in the installed program, or one of the package's listed names; it declares no inductive type; the subject, its tables, each
  row, its fields, its number and each decision are constructors over literals and declarations
  of the module as they stand (`subjectAsItStands`, which lists what may stand at each place); and, reading the subject's rows as the commands read them, each row's
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

**What these controls are for, and what they do not establish.** A data module is printed by the
issuer, which is trusted with the compiler; the controls hold the issuer's printing to a shape, so
that a change of the issuer that makes it state a proposition, compute a row or import the formal
library fails a check. They are no defence against a module written to deceive them, which is not
the issuer's. Within a module that passes, these are not held to any shape, and a statement does
not rest on them being so: a proposition wrapped in a data type (`PLift`, a subtype); the
statement of a theorem that has one of the package's listed names; the key of a lookup; an
auxiliary declaration that Lean makes under a declaration of the module (a nested proof, a
matcher); the root's and a short
application's own term; a constructor's parameters and implicit fields; the source's names. What
holds a published statement to the source is the comparison of the subject with a second reading
of the source by value, in the checks that run it, and the comparator's comparison of constants.
A further rule is added here only for a way through one of the rules above.
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

/-- The types of the parts of a subject that have a rule of their own in `subjectAsItStands` or
in the rows' rules. -/
def partTypes : List Name :=
  [``Zkc.Subject.GoalSlot, ``Zkc.Subject.GoalFields, ``Zkc.Subject.Decision, ``Zkc.Subject.ShortApplication,
    ``Zkc.Subject.CapTable, ``Zkc.Subject.Bound, ``Zkc.Subject.BoundedTable]

/-- Whether a term is built of constructors, literals, numerals and declarations of the module
(each standing alone, applied to nothing). A proof and a type are not looked into, nor a
constructor's parameters and implicit fields: none of these chooses a value. A term with any other head (a conditional, a matcher, a recursor, a function
of a library) is none, so nothing in such a term is computed from the module's data. -/
partial def constructorTerm (inModule : Name → Bool) (e : Expr) : MetaM Bool := do
  let e := e.consumeMData
  if numeral e then return true
  if e.isLit || e.isSort || e.isForall then return true
  if ← (try Meta.isProof e catch _ => pure false) then return true
  if ← (try Meta.isType e catch _ => pure false) then return true
  let .const head _ := e.getAppFn | return false
  if inModule head then
    -- a declaration of the module stands alone, and is a part with a rule of its own (a row, its
    -- fields, a table, a bound, a decision, a short application) or is itself such a term
    unless e.getAppNumArgs == 0 do return false
    if (← typeHead head).any partTypes.contains then return true
    let some value := (← getConstInfo head).value? | return false
    return ← constructorTerm inModule value
  let some (.ctorInfo constructor) := (← getEnv).find? head | return false
  -- the constructor's fields that are written: its parameters and its implicit fields are fixed
  -- by the type at which it stands
  let info ← Meta.getFunInfoNArgs e.getAppFn e.getAppNumArgs
  let args := e.getAppArgs
  for index in [constructor.numParams:args.size] do
    if (info.paramInfo[index]?.map (·.binderInfo.isExplicit)).getD true then
      unless ← constructorTerm inModule args[index]! do return false
  return true

/-- The declarations of the module that a term reads as values: those in its types (that are no
propositions) and in its proofs are left out, since neither chooses a value; a condition is a
proposition and is read. -/
partial def valueReads (inModule : Name → Bool) (e : Expr) (found : NameSet := {}) : MetaM NameSet := do
  let e := e.consumeMData
  if ← (try Meta.isProof e catch _ => pure false) then return found
  if ← (try (do return (← Meta.isType e) && !(← Meta.isProp e)) catch _ => pure false) then return found
  match e with
  | .const name _ => return if inModule name then found.insert name else found
  | .app .. =>
    let mut found ← valueReads inModule e.getAppFn found
    for arg in e.getAppArgs do found ← valueReads inModule arg found
    return found
  | .lam name type body info | .forallE name type body info =>
    Meta.withLocalDecl name info type fun x => valueReads inModule (body.instantiate1 x) found
  | .letE name type value body _ =>
    let found ← valueReads inModule value found
    Meta.withLetDecl name type value fun x => valueReads inModule (body.instantiate1 x) found
  | .proj _ _ body => valueReads inModule body found
  | _ => return found

/-- The elements of a table's selector, where the selector has the issuer's shape: one
declaration of the module, or a conditional on the index's value against a numeral whose two
branches have that shape. A selector of another shape gives nothing. -/
partial def selectorLeaves (inModule : Name → Bool) (index : Expr) (e : Expr) : Option (List Name) := do
  let e := e.consumeMData
  if let some name := e.constName? then
    if inModule name then return [name] else none
  guard (e.isAppOfArity ``ite 5)
  let condition := (e.getArg! 1).consumeMData
  guard (condition.isAppOfArity ``LT.lt 4)
  let value := (condition.getArg! 2).consumeMData
  guard (value.isAppOfArity ``Fin.val 2 && value.appArg!.consumeMData == index && numeral (condition.getArg! 3))
  return (← selectorLeaves inModule index (e.getArg! 3)) ++ (← selectorLeaves inModule index (e.getArg! 4))

/-- **The subject as it stands.** What may stand at each place, for the subject, a table, a row,
its fields and a decision:

* the subject is its constructor; its table of decisions and its table of rows are each a
  declaration of the module or a table in place;
* a table is its constructor at a numeral, and its selector has the issuer's shape: one
  element, or conditionals on the index's value against numerals over elements; run at each
  index, it gives the elements in their order, each at one index;
* a row is its constructor: its path, its property and its clause's place are terms of
  constructors, literals and numerals (a declaration of the module that stands at such a place
  is itself such a term), and its fields are a declaration of the module;
* the fields are their constructor: the proof arguments are a term of constructors and numerals,
  and the number is a constructor over declarations of the module (a table and a bound; a bound
  with a table or none);
* a decision is its constructor: its short application is a declaration of the module, and its
  place and its witness operands are terms of constructors, numerals and such declarations.

So no row, decision, path, property, place, number or operand is chosen by a computation over
the module's data. -/
def subjectAsItStands (inModule : Name → Bool) (subject : Name) : MetaM Unit := do
  let valueOf (name : Name) : MetaM Expr := do
    let some value := (← getConstInfo name).value? | throwError "data control: {name} has no value"
    return value.consumeMData
  let declared (e : Expr) : Bool := e.consumeMData.constName?.any inModule
  let plain (what : MessageData) (e : Expr) : MetaM Unit := do
    unless ← constructorTerm inModule e do
      throwError "data control: {what} is not built of constructors, literals and declarations:{indentExpr e}"
  -- a table, in place or as a declaration: the declarations of its element that its selector reads
  let elements (what : MessageData) (table : Expr) (element : Name) : MetaM (Array Name) := do
    let table ← if declared table then valueOf table.consumeMData.constName! else pure table.consumeMData
    unless table.isAppOfArity ``Zkc.Subject.BoundedTable.mk 3 && numeral (table.getArg! 1) do
      throwError "data control: {what} is not a table's constructor at a numeral:{indentExpr table}"
    let read := (← valueReads inModule (table.getArg! 2)).toArray
    for name in read do
      unless (← typeHead name) == some element do
        throwError "data control: {what} reads {name}, which is none of its elements"
    -- the selector has the issuer's shape, and gives each element at one index
    let some size := (table.getArg! 1).nat? | throwError "data control: {what} has no numeral for its size"
    if size == 0 then return #[]
    let leaves ← Meta.lambdaBoundedTelescope (table.getArg! 2).consumeMData 1 fun xs body => do
      let #[index] := xs
        | throwError "data control: the selector of {what} is no function of an index:{indentExpr (table.getArg! 2)}"
      return selectorLeaves inModule index body.headBeta
    let some leaves := leaves
      | throwError "data control: the selector of {what} is not one element or conditionals on the index's value against numerals:{indentExpr (table.getArg! 2)}"
    unless leaves.length == size && leaves.eraseDups.length == size do
      throwError "data control: the selector of {what} does not give {size} elements, each at one index: {leaves}"
    -- and what it gives at each index is the element that stands there: the selector is run at
    -- every index, so a threshold or a comparison that sends two indexes to one element is seen
    let sizeTerm := table.getArg! 1
    for (leaf, at_) in leaves.zipIdx do
      let position := mkNatLit at_
      let below ← Meta.mkDecideProof (← Meta.mkAppM ``LT.lt #[position, sizeTerm])
      let index ← Meta.mkAppM ``Fin.mk #[position, below]
      let given ← Meta.whnfUntil (mkApp (table.getArg! 2) index) leaf
      unless given.any (·.isConstOf leaf) do
        throwError "data control: the selector of {what} does not give {leaf} at the index {at_}"
    return read
  let value ← valueOf subject
  unless value.isAppOfArity ``Zkc.Subject.WrittenSubject.mk 6 do
    throwError "data control: the subject {subject} is not its constructor:{indentExpr value}"
  for decision in ← elements m!"the table of decisions of {subject}" (value.getArg! 3) ``Zkc.Subject.Decision do
    let held ← valueOf decision
    unless held.isAppOfArity ``Zkc.Subject.Decision.mk 6 && declared (held.getArg! 3) do
      throwError "data control: the decision {decision} is not its constructor over a declaration of its short application:{indentExpr held}"
    plain m!"the place of the decision {decision}" (held.getArg! 4)
    plain m!"the witness operands of the decision {decision}" (held.getArg! 5)
  for slot in ← elements m!"the table of rows of {subject}" (value.getArg! 4) ``Zkc.Subject.GoalSlot do
    let row ← valueOf slot
    unless row.isAppOfArity ``Zkc.Subject.GoalSlot.mk 5 && declared (row.getArg! 4) do
      throwError "data control: the row {slot} is not its constructor over a declaration of its fields:{indentExpr row}"
    plain m!"the path of the row {slot}" (row.getArg! 1)
    plain m!"the property of the row {slot}" (row.getArg! 2)
    plain m!"the clause of the row {slot}" (row.getArg! 3)
    let fieldsName := (row.getArg! 4).consumeMData.constName!
    let fields ← valueOf fieldsName
    unless fields.isAppOfArity ``Zkc.Subject.GoalFields.mk 2 do
      throwError "data control: the fields {fieldsName} are not their constructor:{indentExpr fields}"
    plain m!"the proof arguments of {fieldsName}" (fields.getArg! 0)
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
  liftTermElabM (subjectAsItStands inModule subject)
  for row in ← liftTermElabM (ZkcFormal.Written.Publish.rows subject) do
    let number ← liftTermElabM row.number
    let some bound := number.bound.constName?
      | throwError "data control: the bound of the row at {row.path} is no declaration:{indentExpr number.bound}"
    let some (.defnInfo d) := env.find? bound
      | throwError "data control: the bound {bound} is no definition"
    unless inModule bound && d.value.isAppOfArity ``Zkc.Subject.Bound.mk 3 && numeral (d.value.getArg! 0) &&
        numeral (d.value.getArg! 1) do
      throwError "data control: the bound {bound} is not two numerals:{indentExpr d.value}"
    if let some table ← liftTermElabM number.table then
      let some caps := table.constName?
        | throwError "data control: the table of the row at {row.path} is no declaration:{indentExpr table}"
      let some (.defnInfo t) := env.find? caps
        | throwError "data control: the table {caps} is no definition"
      unless inModule caps do throwError "data control: the table {caps} is no declaration of {m.getId}"
      if let some read := t.value.getUsedConstants.find? inModule then
        throwError "data control: the table {caps} reads {read}"
      unless ← liftTermElabM (constructorTerm (fun _ => false) t.value) do
        throwError "data control: the table {caps} is not built of constructors and numerals:{indentExpr t.value}"
  -- The declarations: no proposition, no instance, no inductive type; a theorem is one that the
  -- subject reaches (a lookup of the root or of a relation) or one of the package's.
  let fromSubject := reached env index [subject] {}
  for name in env.header.moduleData[index.toNat]!.constNames do
    -- an auxiliary declaration that Lean makes for a declaration of the module (a nested proof, a
    -- matcher: its name is under that declaration's) is not looked at; a private declaration,
    -- and one whose name only looks auxiliary, is the module's own and is held to the rules
    if name.isInternalDetail && (privateToUserName? name).isNone &&
        (env.find? name.getPrefix).isSome && inModule name.getPrefix then continue
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
