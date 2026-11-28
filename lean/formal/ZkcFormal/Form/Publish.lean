module

public import ZkcFormal.Form.Produce
public meta import Zkc.Subject.WrittenGoal

/-!
The forms of a subject, declared once and registered.

`publish_forms S`, for a written subject `S`, declares the form and the equation of every
definition in its reach, and records each in a register that an importer reads. **The reach**
is what a proof of the subject's goals is about: the program of the root's deciding role; the
function of each clause's relation; and, from these, every definition that a form in the reach
calls, a protocol at the role that the caller's role plays in it. The reach is not a list that
a text writes: it is read from the subject and from the calls that the walk meets.

Each definition in the reach has one name, by the kind and the key of its header
(`protocol<key>`, `function<key>` under the name space of the command), which is its member of
the installed program; a protocol's form at a role is `protocol<key>.role<r>.form` with
`protocol<key>.role<r>.reads`, a function's `function<key>.form` with `function<key>.reads`. A
tool asks the register by the program, the key and the role, and does not find a form by a
name (`registered?`); `#registered_forms` prints the register's rows of a program.
-/

public meta section

namespace ZkcFormal.Form
open Lean Meta Elab

/-- What is registered of a definition of a program, at a role when it is a protocol. -/
structure Registered where
  /-- The installed program. -/
  program : Lean.Name
  /-- The key of the definition's header. -/
  key : Nat
  /-- The role, of a protocol. -/
  role : Option Nat
  /-- The definition's member of the program. -/
  member : Lean.Name
  /-- The form, a computation for every model, path and list of inputs. -/
  form : Lean.Name
  /-- The equation: the reading of the definition's meaning is the form. -/
  reads : Lean.Name
  deriving Inhabited

/-- The register of forms: the rows of this module and of every module that it imports. -/
initialize registry : SimplePersistentEnvExtension Registered (Array Registered) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun imported => imported.foldl (· ++ ·) #[] }

/-- The registered form of a definition of a program, by its key and its role. -/
def registered? (env : Environment) (program : Lean.Name) (key : Nat) (role : Option Nat) :
    Option Registered :=
  (registry.getState env).find? fun row =>
    row.program == program && row.key == key && row.role == role

namespace Publish
open Produce

/-- The arguments of a term that reduces to an application of a constructor. -/
def parts (e : Expr) (constructor : Lean.Name) : MetaM (Array Expr) := do
  let e ← whnfD e
  unless e.isAppOf constructor do
    throwError "publish_forms: expected an application of {constructor}, got{indentExpr e}"
  return e.getAppArgs

/-- A natural that the subject writes. -/
def number (e : Expr) : MetaM Nat := do
  let e ← whnfD e
  match e.rawNatLit? <|> e.nat? with
  | some n => return n
  | none => throwError "publish_forms: expected a number, got{indentExpr e}"

/-- The functions of the relations of a subject's clauses, each as its header and its member. -/
def relations (subject : Expr) : MetaM (Array (Expr × Expr)) := do
  let table ← parts (← parts subject ``Zkc.Subject.WrittenSubject.mk)[3]!
    ``Zkc.Subject.BoundedTable.mk
  let size ← number table[1]!
  let mut found := #[]
  for i in [0:size] do
    let below ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit i, mkNatLit size])
    let index ← mkAppOptM ``Fin.mk #[some (mkNatLit size), some (mkNatLit i), some below]
    let decision ← parts (mkApp table[2]! index) ``Zkc.Subject.Decision.mk
    let application ← parts decision[3]! ``Zkc.Subject.ShortApplication.mk
    let relation ← parts application[3]! ``Zkc.Subject.FunctionEntry.mk
    found := found.push (relation[2]!, relation[3]!)
  return found

end Publish

open Publish Produce in
/-- **The forms of a subject.** `publish_forms S` declares and registers the form of every
definition in the reach of the written subject `S`, under the current name space. -/
elab "publish_forms " subject:term : command => Command.liftTermElabM do
  let subject ← Term.elabTermAndSynthesize subject none
  let type ← whnfR (← inferType subject)
  unless type.isAppOfArity ``Zkc.Subject.WrittenSubject 3 do
    throwError "publish_forms: expected a written subject, got a term of type{indentExpr type}"
  let vocabulary := type.getArg! 0
  let program ← whnfR (← mkAppM ``Zkc.Subject.Package.installed #[type.getArg! 1])
  let some programName := program.constName?
    | throwError "publish_forms: the installed program is not a declaration:{indentExpr program}"
  let naming : Naming := ⟨← getCurrNamespace, ← IO.mkRef #[]⟩
  -- the root at its deciding role, and the relation of each clause
  let root ← parts type.appArg! ``Zkc.Subject.WrittenRoot.mk
  let entry ← parts root[2]! ``Zkc.Subject.ProtocolEntry.mk
  let deciding ← number (← parts root[4]! ``Fin.mk)[1]!
  let (rootMember, rootKey) ← named naming.space "protocol" ``Zkc.Core.ProtocolHeader.key
    entry[2]! entry[3]!
  naming.calls.modify (·.push ⟨rootMember.constName!, rootKey, some deciding⟩)
  for (header, member_) in ← relations subject do
    let (name, key) ← named naming.space "function" ``Zkc.Core.FnHeader.key header member_
    naming.calls.modify (·.push ⟨name.constName!, key, none⟩)
  -- every definition that a form in the reach calls
  let model ← mkAppM ``Zkc.Core.Model #[vocabulary]
  let mut seen : Array Called := #[]
  repeat
    let met ← naming.calls.modifyGet fun calls => (calls, #[])
    let fresh := met.foldl (fun fresh called =>
      if seen.contains called || fresh.contains called then fresh else fresh.push called) #[]
    if fresh.isEmpty then break
    for called in fresh do
      seen := seen.push called
      let member_ := mkConst called.member
      let name := match called.role with
        | some r => called.member ++ Lean.Name.mkSimple s!"role{r}"
        | none => called.member
      withLocalDeclD `M model fun M => do
        let stored ← match called.role with
          | some r => mkAppM ``ZkcFormal.Form.storedRole #[M, program, member_, mkRawNatLit r]
          | none => mkAppM ``ZkcFormal.Form.storedFunction #[M, program, member_]
        declare naming name (← mkLambdaFVars #[M] stored)
      modifyEnv (registry.addEntry · {
        program := programName, key := called.key, role := called.role
        member := called.member, form := name ++ `form, reads := name ++ `reads })

/-- `#registered_forms p` prints the register's rows of the program `p`, one a line, in the
order of their keys and roles. -/
elab "#registered_forms " program:ident : command => do
  let name ← Command.liftCoreM (realizeGlobalConstNoOverloadWithInfo program)
  let rows := (registry.getState (← getEnv)).filter (·.program == name)
  let rows := rows.qsort fun a b =>
    a.key < b.key || (a.key == b.key && a.role.getD 0 < b.role.getD 0)
  let lines := rows.toList.map fun row =>
    match row.role with
    | some r => s!"protocol {row.key} role {r}: {row.form}"
    | none => s!"function {row.key}: {row.form}"
  logInfo ("registered forms:\n" ++ "\n".intercalate lines)

end ZkcFormal.Form
