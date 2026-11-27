module

public import Zkc.Subject.WrittenGoal
public import ZkcFormal.Written.Soundness
public import ZkcFormal.Written.Publish
public import ZkcFormal.Written.ViewLabels
public import ZkcFormal.Written.FunctionMeaning
public import ZkcFormal.ComputedTypes
public meta import Lean
public meta import Zkc.Subject.SourceNames

/-!
Named views of what a subject publishes, declared by a command over the subject.

`publish_views S` declares, for each goal row of the subject `S` at the path `p` (in the name space
`<space>` of `S`) and each theorem `t` that the row's property publishes, the proposition
`<space>.<p>.<t>.view` and the theorem `<space>.<p>.<t>.view_iff : view ↔ published% S p t`, proved
by `Iff.rfl`; and, for a row of the property `soundness` (the one published property today), the
view of what an author proves, `Soundness.Installed` at the row's short application and the limit of
its bound, under `<space>.<p>.installed`. For such a row whose stored program the standard
interpretation covers (decided by the kernel) it declares the coverage fact `<space>.<p>.covered`
and the author's last step `<space>.<p>.sound_of_installed : installed.view → published% S p sound`;
a row that is not covered gets neither, and a line that says so. A views module is its imports and
that line. It is for proofs and readers, not for a challenge: the repository's challenges do not
import it, and nothing refuses a challenge that does yet.

A stored view is the library's term **named** and then **presented**:

* *Naming* reads the subject's origins (`WrittenSubject.origins`, given with the rows) and the two
  lists below: the definitions that it unfolds and the heads whose premises it names. It walks the
  proposition and, at each application of `Goal.Internal.inputs` whose ports are the root's deployed
  inputs, binds each input that the role holds as `input_<name>` with `valid_input_<name>` (or
  `port<ordinal>` with `valid_port<ordinal>`, by `Zkc.Subject.inputBinderName`), and at each
  application of `Goal.Internal.witnesses` binds `witness<i>`, followed by the validities of the
  witnesses where the continuation's head is `validWitnesses`, and by the continuation as it stands
  otherwise. The premise after an input telescope takes the name of its head constant where that
  constant is registered (`Rejected` gives `rejected`); one whose head is not registered is
  anonymous where the rest does not refer to its proof, and keeps its name where the rest does. To
  reach a telescope, a definition is unfolded only if it is in the list (the library's, below, and
  those with the label `view_unfold`) and its value leads to a telescope; a `let` is substituted; a
  negation stays as the library writes it. An input telescope over other ports is reported. A
  declaration named like an input, a variable of that name, a local notation and a printing option
  around the command leave a stored view as it is; a registration by one of the two labels before
  the command is read by it.
* *Presenting* reduces the projections of the short application, the root, the package and the
  entries, and applies the meanings of functions and roles to the reduced cells of their inputs, so
  that an author rewrites on the view. In a view the binder of an input or of a witness has its type
  computed where naming makes the binder; no other binder has its type computed.
-/

public meta section

namespace ZkcFormal.Written.Views
open Lean Meta Elab Term Command

/-! ## The list -/

/-- The library's definitions that naming unfolds where their value leads to a telescope. -/
def libraryUnfolds : List Name :=
  [``Soundness.Result, ``Soundness.AdmittedBound, ``Soundness.admission, ``Soundness.BoundOf,
    ``Soundness.Witnessed, ``Soundness.Rejected, ``Soundness.Installed]

/-- The library's propositions whose premise after an input telescope is named after its head. -/
def libraryPremises : List Name := [``Soundness.Rejected]

/-- The list of definitions that naming unfolds: the library's and the registered ones. -/
def unfoldList : CoreM (List Name) := return libraryUnfolds ++ (← labelled `view_unfold).toList

/-- The heads whose premises are named: the library's and the registered ones. -/
def premiseList : CoreM (List Name) := return libraryPremises ++ (← labelled `view_premise).toList

/-! ## The origins of a subject -/

private partial def listCells (e : Expr) : MetaM (List Expr) := do
  let s ← whnf e
  match_expr s with
  | List.nil _ => return []
  | List.cons _ x xs => return x :: (← listCells xs)
  | _ => throwError "views: expected a concrete list, got{indentExpr s}"

private def numeral (e : Expr) : MetaM Nat := do
  let some n ← getNatValue? (← whnf e) | throwError "views: expected a concrete number in{indentExpr e}"
  return n

/-- The source names of a subject's root and the deployed inputs that they name. -/
structure Origins where
  /-- The written root of the subject. -/
  root : Expr
  /-- The root's deployed inputs, `root.entry.header.ins`. -/
  ports : Expr
  /-- For each deployed input, in order: its source name and its holders. -/
  inputs : List (String × List Nat)

/-- The origins of the subject `S`, read from its field `origins`. -/
def originsOf (subject : Name) : MetaM Origins := do
  let s ← mkConstWithLevelParams subject
  let type ← whnf (← inferType s)
  unless type.isAppOf ``Zkc.Subject.WrittenSubject do
    throwError "views: {subject} is not a written subject"
  let root := type.appArg!
  let origins ← Publish.fieldOf s ``Zkc.Subject.WrittenSubject `origins
  let names ← (← listCells (← mkAppM ``Array.toList #[← mkProjection origins `inputNames])).mapM fun e => do
    let some n := getStringValue? (← whnf e) | throwError "views: expected a source name in{indentExpr e}"
    return n
  let ports ← mkProjection (← mkProjection (← mkProjection root `entry) `header) `ins
  let cells ← listCells ports
  unless names.length == cells.length do
    throwError "views: the origins of {subject} name {names.length} inputs, its root deploys {cells.length}"
  let holders ← cells.mapM fun c => do (← listCells (← mkProjection c `holders)).mapM numeral
  return { root, ports, inputs := names.zip holders }

/-- The binder names of the inputs that role `r` holds, each with its ordinal in the deployed
header: a function of the origins alone. -/
def heldNames (o : Origins) (r : Nat) : List (Name × Nat) :=
  let counts := o.inputs.foldl (init := ({} : Std.HashMap String Nat)) fun m (s, _) =>
    m.insert s (m.getD s 0 + 1)
  let named := o.inputs.toArray.zipIdx.map fun ((s, _), k) =>
    Name.mkSimple (Zkc.Subject.inputBinderName s k (counts.getD s 0))
  let held := (o.inputs.zipIdx.filter fun ((_, holders), _) => holders.contains r).map (·.2)
  held.map fun k => (named[k]!, k)

/-! ## Naming -/

/-- What naming reads: the origins, the list, the registered premises, the type that a bound value
gets, and whether a telescope was named. -/
structure Namer where
  origins : Origins
  listed : List Name
  premises : List Name
  /-- The type that the binder of an input or of a witness gets, from the type that its telescope
  gives it. Naming alone leaves the type; a view computes it (`viewOf`). It is applied where the
  binder is made, and to no other binder. -/
  carrier : Expr → MetaM Expr
  found : IO.Ref Bool

/-- Whether the value of a listed definition leads to a telescope: it names `inputs` or
`witnesses`, or a listed definition whose value does. -/
partial def leads (listed : List Name) (c : Name) (seen : NameSet := {}) : MetaM Bool := do
  if c == ``Goal.Internal.inputs || c == ``Goal.Internal.witnesses then return true
  if seen.contains c || !listed.contains c then return false
  let some (.defnInfo info) := (← getEnv).find? c | return false
  let seen := seen.insert c
  info.value.getUsedConstants.anyM fun d => leads listed d seen

/-- Whether an application's head is a definition that naming unfolds. -/
private def unfolded (n : Namer) (e : Expr) : MetaM (Option Expr) := do
  let .const c us := e.getAppFn | return none
  if c == ``Goal.Internal.inputs || c == ``Goal.Internal.witnesses then return none
  unless ← leads n.listed c do return none
  let some (.defnInfo info) := (← getEnv).find? c | return none
  return some ((info.value.instantiateLevelParams info.levelParams us).beta e.getAppArgs)

/-- The name of the premise of the proposition `t`: its head's, where the head is registered. -/
private def premiseName (n : Namer) (t : Expr) : Option Name :=
  match t.getAppFn.constName? with
  | some c@(.str _ s) => if n.premises.contains c then some (Name.mkSimple s.decapitalize) else none
  | _ => none

private def validName (n : Name) : Name := Name.mkSimple (Zkc.Subject.validBinderName n.toString)

mutual

/-- The term with its telescopes named. -/
partial def name (n : Namer) (e : Expr) : MetaM Expr := do
  let e := e.consumeMData.headBeta
  if e.isAppOfArity ``Goal.Internal.inputs 6 then return ← namedInputs n e
  if e.isAppOfArity ``Goal.Internal.witnesses 4 then return ← namedWitnesses n e
  match e with
  | .forallE x t b bi =>
    let t ← name n t
    withLocalDecl x bi t fun v => do mkForallFVars #[v] (← name n (b.instantiate1 v))
  | .lam x t b bi =>
    let t ← name n t
    withLocalDecl x bi t fun v => do mkLambdaFVars #[v] (← name n (b.instantiate1 v))
  | .letE _ _ v b _ => name n (b.instantiate1 v)
  | .app .. =>
    if let some u ← unfolded n e then return ← name n u
    return mkAppN e.getAppFn (← e.getAppArgs.mapM (name n))
  | .const .. =>
    if let some u ← unfolded n e then return ← name n u
    return e
  | _ => return e

/-- An input telescope: the inputs that the role holds under the origins' names. The
continuation is made a variable while the telescope is reduced, so that reduction stops where
the telescope ends. -/
partial def namedInputs (n : Namer) (e : Expr) : MetaM Expr := do
  let args := e.getAppArgs
  unless ← isDefEq args[4]! n.origins.ports do
    throwError "views: an input telescope over ports that are not the deployed inputs of the subject's root{indentExpr args[4]!}"
  n.found.set true
  let names := heldNames n.origins (← numeral args[2]!)
  let k := args[5]!
  withLocalDecl `k .default (← inferType k) fun kv => do
    held n names (mkApp (mkAppN e.getAppFn args.pop) kv) kv k

/-- The binders of the held inputs, then the continuation. -/
partial def held (n : Namer) (names : List (Name × Nat)) (cur kv k : Expr) : MetaM Expr := do
  let s ← whnf cur
  match names with
  | [] =>
    unless s.getAppFn == kv do
      throwError "views: the input telescope binds more than the inputs that its role holds{indentExpr s}"
    continuation n (mkAppN k s.getAppArgs).headBeta
  | (x, _) :: rest =>
    match s with
    | .forallE _ ty b bi =>
      withLocalDecl x bi (← n.carrier ty) fun v => do
        let .forallE _ vty vb vbi := (b.instantiate1 v).headBeta
          | throwError "views: expected the validity of {x}"
        withLocalDecl (validName x) vbi vty fun hv => do
          mkForallFVars #[v, hv] (← held n rest (vb.instantiate1 hv).headBeta kv k)
    | _ =>
      let_expr Exists ty pair := s | throwError "views: expected the binder of {x} in{indentExpr s}"
      let .lam _ _ body pbi := pair | throwError "views: expected a binder in{indentExpr pair}"
      let ty ← n.carrier ty
      let lam ← withLocalDecl x pbi ty fun v => do
        let_expr And valid more := (body.instantiate1 v).headBeta
          | throwError "views: expected the validity of {x}"
        mkLambdaFVars #[v] (mkApp2 (mkConst ``And) valid (← held n rest more.headBeta kv k))
      return mkApp2 s.appFn!.appFn! ty lam

/-- The continuation of an input telescope: its first premise is named after its head where the
head is registered. A premise whose head is not registered is anonymous where the rest does not
refer to its proof, and keeps the name that it has where the rest does. -/
partial def continuation (n : Namer) (body : Expr) : MetaM Expr := do
  match body with
  | .forallE x t b bi =>
    if ← isProp t then
      let premise := (premiseName n t).getD (if b.hasLooseBVars then x else .anonymous)
      let t ← name n t
      withLocalDecl premise bi t fun h => do mkForallFVars #[h] (← name n (b.instantiate1 h))
    else name n body
  | _ => name n body

/-- A witness telescope: `witness<i>`, then the continuation by its own head. -/
partial def namedWitnesses (n : Namer) (e : Expr) : MetaM Expr := do
  n.found.set true
  let args := e.getAppArgs
  let count := (← listCells args[2]!).length
  let k := args[3]!
  withLocalDecl `k .default (← inferType k) fun kv => do
    witnessBinders n count 0 (mkApp (mkAppN e.getAppFn args.pop) kv) kv k

partial def witnessBinders (n : Namer) (count i : Nat) (cur kv k : Expr) : MetaM Expr := do
  let s ← whnf cur
  if i < count then
    let .forallE _ ty b bi := s | throwError "views: expected witness {i} in{indentExpr s}"
    withLocalDecl (Name.mkSimple (Zkc.Subject.witnessBinderName i)) bi (← n.carrier ty) fun v => do
      mkForallFVars #[v] (← witnessBinders n count (i + 1) (b.instantiate1 v).headBeta kv k)
  else
    unless s.getAppFn == kv do throwError "views: expected the end of the witnesses in{indentExpr s}"
    afterWitnesses n (mkAppN k s.getAppArgs).headBeta

/-- After the witnesses: their validities where the continuation's head is `validWitnesses`. -/
partial def afterWitnesses (n : Namer) (body : Expr) : MetaM Expr := do
  if body.isAppOfArity ``Goal.Internal.validWitnesses 5 then
    let args := body.getAppArgs
    withLocalDecl `q .default (mkSort .zero) fun qv => do
      validities n (mkApp (mkAppN body.getAppFn args.pop) qv) qv args[4]!
  else name n body

partial def validities (n : Namer) (cur qv q : Expr) : MetaM Expr := do
  let s ← whnf cur
  if s == qv then return ← name n q
  let .forallE x ty b bi := s | throwError "views: expected the validity of a witness in{indentExpr s}"
  withLocalDecl x bi ty fun h => do mkForallFVars #[h] (← validities n (b.instantiate1 h) qv q)

end

/-! ## Presenting -/

/-- Reduce the projections of the short application, the root, the package and the entries,
without unfolding what they select. -/
def subjectFields (e : Expr) : MetaM Expr :=
  let selected := fun s => [``Zkc.Subject.ShortApplication, ``Zkc.Subject.WrittenRoot,
    ``Zkc.Subject.ProtocolEntry, ``Zkc.Subject.FunctionEntry, ``Zkc.Subject.Package].contains s
  Meta.transform e (pre := fun s => do
    if let some p ← reduceProjOf? s selected then return .visit p
    if let .proj c _ _ := s then
      if selected c then
        if let some p ← reduceProj? s then return .visit p
    return .continue)

/-- The cells of a concrete list of inputs, each reduced. -/
private partial def cells (e : Expr) : MetaM Expr := do
  let s ← whnf e
  if s.isAppOf ``Zkc.Core.HList.nil then return s
  let_expr Zkc.Core.HList.cons α F a as v rest := s | return e
  let v ← whnf v
  let v := if v.isConstOf ``PUnit.unit then Lean.mkConst ``Unit.unit else v
  return mkAppN s.getAppFn #[α, F, a, as, v, ← cells rest]

/-- A meaning of a function or a role, at the subject's fields and its reduced input cells. -/
private def meaningAt (e : Expr) : MetaM (Option Expr) := do
  for head in [``Zkc.Core.fnMeaning, ``Zkc.Core.roleMeaning] do
    if let some s ← whnfUntil e head then
      let s ← subjectFields s
      let args := s.getAppArgs
      -- the inputs are the last explicit argument of both meanings
      return some (mkAppN s.getAppFn (args.pop.push (← cells args.back!)))
  return none

/-- Every meaning of the term, at the subject's fields and its reduced input cells. -/
def meanings (e : Expr) : MetaM Expr :=
  Meta.transform e (pre := fun s => do
    if s.isAppOf ``ZkcFormal.Written.functionResult then
      if let some m ← meaningAt s.appArg! then return .done (mkApp s.appFn! m)
    if s.isAppOf ``Zkc.Core.roleMeaning then
      if let some m ← meaningAt s then return .done m
    return .continue)

/-- A named term's meanings presented for rewriting. -/
def present (e : Expr) : MetaM Expr := do
  subjectFields (← meanings e)

/-! ## Views -/

/-- The term `e` named after the origins of the subject `S`, with `carrier` applied to the type of
each binder of an input or a witness. The callers are the two functions below, whose carriers
return a type that is definitionally the one given. -/
private def namedWith (subject : Name) (e : Expr) (carrier : Expr → MetaM Expr) : MetaM Expr := do
  let e ← instantiateMVars e
  let n : Namer := { origins := ← originsOf subject, listed := ← unfoldList,
                     premises := ← premiseList, carrier, found := ← IO.mkRef false }
  let named ← name n e
  unless ← n.found.get do
    throwError m!"views: no input or witness telescope is reached in{indentExpr e}\nthrough the definitions of the list; a definition outside the list is not unfolded (`@[view_unfold]` adds one)"
  return named

/-- The term `e` named after the origins of the subject `S`, not presented, with every type as it
is. Naming changes binder names, unfolds definitions and substitutes `let`s, so the result is
definitionally `e`; what holds a declared view to `e` is its theorem `view_iff`, which the kernel
checks (`declareView`), and no check of the elaborator's here: at 64 deployed inputs held by the
verifier, `isDefEq` of the named term with the term reaches Lean's maximum recursion depth where
the kernel's check does not. -/
def namedOf (subject : Name) (e : Expr) : MetaM Expr := namedWith subject e pure

/-- **The view of `e` over the subject `S`**: named with the types of the bound inputs and
witnesses computed, then presented. -/
def viewOf (subject : Name) (e : Expr) : MetaM Expr := do
  present (← namedWith subject e ZkcFormal.computedTypes)

/-- Declare `<base>.view : Prop` with the value `value` and `<base>.view_iff : view ↔ e` by
`Iff.rfl`. -/
def declareView (base : Name) (value e : Expr) : MetaM Unit := do
  let viewName := base ++ `view
  let iffName := base ++ `view_iff
  for n in [viewName, iffName] do
    if (← getEnv).contains n then throwError "views: {n} is already declared"
  let height := getMaxHeight (← getEnv) value + 1
  let decl : DefinitionVal :=
    { name := viewName, levelParams := [], type := mkSort Level.zero, value, hints := .regular height, safety := .safe }
  addDecl (.defnDecl decl)
  let iff ← mkAppM ``Iff #[mkConst viewName, e]
  addDecl (.thmDecl { name := iffName, levelParams := [], type := iff, value := mkApp (mkConst ``Iff.refl) e })

/-- The statement of what an author proves for a row: the installed bound at the row's short
application and the limit of its bound. -/
def installedStatement (row : Publish.Row) : MetaM Expr := do
  let model := Lean.mkConst ``ZkcFormal.Written.StandardInterpretation.model
  let draws := Lean.mkConst ``ZkcFormal.Written.StandardInterpretation.draws
  let limit ← mkAppM ``Zkc.Subject.Bound.limit #[Lean.mkConst (← row.bound)]
  mkAppM ``ZkcFormal.Written.Soundness.Installed #[model, Lean.mkConst row.application, draws, limit]

/-- The coverage fact of a row and the step from the view of the installed bound to the published
result, where the kernel reduces the row's coverage to `true`; otherwise the reason that the row
gets neither. The coverage is the first conjunct of the published result. -/
def declareClosing (space : Name) (row : Publish.Row) : MetaM (Option MessageData) := do
  let base := (Publish.theoremName space row "sound").getPrefix
  let sound ← Publish.statement row "sound"
  let some result ← unfoldDefinition? sound
    | throwError "views: the published result of {base} does not unfold"
  let_expr And coverage _ := result.headBeta
    | throwError "views: the published result of {base} is not a coverage and a bound"
  let_expr Eq _ covered _ := coverage | throwError "views: the coverage of {base} is not an equation"
  let reduced ← ofExceptKernelException (Kernel.whnf (← getEnv) (← getLCtx) covered)
  unless reduced.isConstOf ``Bool.true do
    return some m!"publish_views: {".".intercalate row.path}: the standard interpretation does not cover the stored program of this goal; no step to its published result"
  let coveredName := base ++ `covered
  let stepName := base ++ `sound_of_installed
  for n in [coveredName, stepName] do
    if (← getEnv).contains n then throwError "views: {n} is already declared"
  let coveredProof ← mkEqRefl (Lean.mkConst ``Bool.true)
  addDecl (.thmDecl { name := coveredName, levelParams := [], type := coverage, value := coveredProof })
  let model := Lean.mkConst ``ZkcFormal.Written.StandardInterpretation.model
  let draws := Lean.mkConst ``ZkcFormal.Written.StandardInterpretation.draws
  let view := Lean.mkConst (base ++ `installed ++ `view)
  let step ← withLocalDeclD `installed view fun h => do
    let installed ← mkAppM ``Iff.mp #[Lean.mkConst (base ++ `installed ++ `view_iff), h]
    mkLambdaFVars #[h] (← mkAppM ``ZkcFormal.Written.Soundness.result_of_installed
      #[model, Lean.mkConst row.application, draws, Lean.mkConst coveredName, installed])
  let stepType ← withLocalDeclD `installed view fun h => mkForallFVars #[h] sound
  addDecl (.thmDecl { name := stepName, levelParams := [], type := stepType, value := step })
  return none

/-- **Declare the views of what the goals of a subject publish** and of what an author proves,
with the coverage fact and the step to the published result. -/
elab "publish_views " s:ident : command => do
  let subject ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo s
  let space := subject.getPrefix
  let t ← liftTermElabM (Publish.tables subject)
  for index in [:t.goals] do
    let row ← liftTermElabM (Publish.rowAt t index)
    for which in ← liftTermElabM (Publish.theoremsOf row) do
      let e ← liftTermElabM (Publish.statement row which)
      liftTermElabM do declareView (Publish.theoremName space row which) (← viewOf subject e) e
    -- what an author of a soundness proof proves, and the step from it
    if row.isSoundness then
      liftTermElabM do
        let e ← installedStatement row
        declareView (Publish.theoremName space row "installed") (← viewOf subject e) e
      if let some reason ← liftTermElabM (declareClosing space row) then logInfo reason

end ZkcFormal.Written.Views
