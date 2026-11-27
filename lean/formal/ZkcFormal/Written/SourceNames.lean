module

public import Zkc.Subject.WrittenGoal
public import ZkcFormal.Written.Goal.Inputs
public import ZkcFormal.ComputedTypes
public import ZkcFormal.Written.FunctionMeaning
public meta import Lean
public meta import Zkc.Subject.SourceNames

/-!
Source names for a library term applied to a typed subject.

`present` reads a proposition of the library applied to a subject (any property) and returns a
definitionally equal proposition in which:
- each telescope of deployed inputs (`Goal.Internal.inputs`) binds the inputs that the role
  holds under the names of the source, read from the `Zkc.Subject.SourceNames` instance of the root that
  the telescope's ports belong to, each validity as `valid_<name>`;
- each telescope of witnesses (`Goal.Internal.witnesses`) binds `witness<i>`;
- the premise that follows an input telescope is named after the head of its proposition
  (`Rejected` gives `rejected`);
- the meanings of functions and roles are applied to the subject's own fields and to the
  cells of their inputs (casts and projections of the subject reduced).

A definition of the library is unfolded only where its value reaches one of the two telescopes.
Two front ends use it: the tactic `source_intro` (names given when a proof introduces the
binders) and the elaborators `source_view%`, `named%` with the command `source_view` (a named
view beside a published term).
-/

public meta section

namespace ZkcFormal.Written.SourceNames
open Lean Meta Elab Term Tactic Command

private partial def listCells (e : Expr) : MetaM (List Expr) := do
  let s ← whnf e
  match_expr s with
  | List.nil _ => return []
  | List.cons _ x xs => return x :: (← listCells xs)
  | _ => throwError "source names: expected a concrete list, got {s}"

private def numeral (e : Expr) : MetaM Nat := do
  let some n ← getNatValue? (← whnf e) | throwError "source names: expected a concrete number in {e}"
  return n

/-- The written root whose header lists the ports, read before any reduction. -/
private def rootOf (ports : Expr) : MetaM Expr := do
  let some entry := ports.find? (·.isAppOfArity ``Zkc.Subject.WrittenRoot.entry 3)
    | throwError "source names: the ports {ports} are not those of a written root"
  return entry.appArg!

/-- The names of the inputs that role `r` holds, in the order of the deployed header. -/
private def heldNames (root : Expr) (r : Nat) : MetaM (List Name) := do
  let cls ← mkAppM ``Zkc.Subject.SourceNames #[root]
  let inst ← synthInstance cls
  let origin ← mkAppOptM ``Zkc.Subject.SourceNames.origins #[none, none, root, inst]
  let raw ← listCells (← mkAppM ``Array.toList #[← mkProjection origin `inputNames])
  let names ← raw.mapM fun e => do
    let some s := getStringValue? (← whnf e) | throwError "source names: expected a spelling in {e}"
    return s
  let counts := names.foldl (init := ({} : Std.HashMap String Nat)) fun m s => m.insert s (m.getD s 0 + 1)
  let inputs ← listCells (← mkProjection (← mkProjection (← mkProjection root `entry) `header) `ins)
  unless names.length == inputs.length do throwError "source names: origins and deployed header disagree"
  let mut taken : Std.HashSet String := {}
  for s in names do
    for candidate in ["input_" ++ s, "valid_input_" ++ s] do
      unless (← resolveGlobalName (Name.mkSimple candidate)).isEmpty do taken := taken.insert candidate
  let mut held := #[]
  for ((s, input), i) in (names.zip inputs).zipIdx do
    let holders ← (← listCells (← mkProjection input `holders)).mapM numeral
    if holders.contains r then
      held := held.push (Name.mkSimple (Zkc.Subject.inputBinderName s i (counts.getD s 0) taken.contains))
  return held.toList

/-- A premise is named after the head of its proposition: `Rejected` gives `rejected`. -/
private def premiseName (domain : Expr) : Name :=
  match domain.getAppFn.constName? with
  | some (.str _ s) => Name.mkSimple (s.decapitalize)
  | _ => `premise

/-- Whether a definition's value reaches an input or witness telescope, through definitions of
the formal library. -/
private partial def reachesTelescope (c : Name) (seen : NameSet := {}) : MetaM Bool := do
  if c == ``Goal.Internal.inputs || c == ``Goal.Internal.witnesses then return true
  if seen.contains c || !(`ZkcFormal).isPrefixOf c then return false
  let some (.defnInfo info) := (← getEnv).find? c | return false
  let seen := seen.insert c
  for d in info.value.getUsedConstants do
    if ← reachesTelescope d seen then return true
  return false

/-- Reduce the projections of the subject's records, without unfolding what they select. -/
private def subjectFields (e : Expr) : MetaM Expr :=
  let selected := fun n => [``Zkc.Subject.WrittenGoal, ``Zkc.Subject.GoalFields, ``Zkc.Subject.Decision, ``Zkc.Subject.ShortApplication,
    ``Zkc.Subject.WrittenRoot, ``Zkc.Subject.ProtocolEntry, ``Zkc.Subject.FunctionEntry,
    ``Zkc.Subject.Package, ``Fin, ``Zkc.Core.LTy].contains n
  Meta.transform e (pre := fun s => do
    if let some p ← reduceProjOf? s selected then return .visit p
    if let .proj n _ _ := s then
      if selected n then
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
      let inputs ← cells args.back!
      return some (mkAppN s.getAppFn (args.pop.push inputs))
  return none

/-- Apply `meaningAt` to every meaning of the term that is not under a binder of its own. -/
private def meanings (e : Expr) : MetaM Expr :=
  Meta.transform e (pre := fun s => do
    if s.isAppOf ``ZkcFormal.Written.functionResult then
      let arg := s.appArg!
      if let some m ← meaningAt arg then return .done (mkApp s.appFn! m)
    if s.isAppOf ``Zkc.Core.roleMeaning then
      if let some m ← meaningAt s then return .done m
    return .continue)

mutual

/-- The term with its telescopes named (and whether a telescope was found). -/
partial def present (e : Expr) : MetaM (Expr × Bool) := do
  let e := e.consumeMData.headBeta
  if e.isAppOfArity ``Goal.Internal.inputs 6 then return (← inputs e, true)
  if e.isAppOfArity ``Goal.Internal.witnesses 4 then return (← witnesses e, true)
  match e with
  | .forallE n t b bi =>
    let (t', c1) ← present t
    withLocalDecl n bi t' fun x => do
      let (b', c2) ← present (b.instantiate1 x)
      return (← mkForallFVars #[x] b', c1 || c2)
  | .lam n t b bi =>
    withLocalDecl n bi t fun x => do
      let (b', c) ← present (b.instantiate1 x)
      return (← mkLambdaFVars #[x] b', c)
  | .letE _ _ v b _ => present (b.instantiate1 v)
  | .app .. =>
    let f := e.getAppFn
    if let some c := f.constName? then
      if ← reachesTelescope c then
        if let some u ← unfoldDefinition? e then
          let (u', changed) ← present u
          if changed then return (u', true)
    let mut changed := false
    let mut args := #[]
    for a in e.getAppArgs do
      let (a', c) ← present a
      changed := changed || c
      args := args.push a'
    return (if changed then mkAppN f args else e, changed)
  | _ => return (e, false)

/-- An input telescope, its binders named by the origins of its root. -/
partial def inputs (e : Expr) : MetaM Expr := do
  let role ← numeral (e.getArg! 2)
  let names ← heldNames (← rootOf (e.getArg! 4)) role
  inputsFrom names e

partial def inputsFrom (names : List Name) (e : Expr) : MetaM Expr := do
  match names with
  | [] =>
    -- the body after the telescope: its first premise is named after its head
    let s ← whnf e
    match s with
    | .forallE _ t b bi =>
      if (← isProp t) && !b.hasLooseBVars then
        let (t', _) ← present t
        let t' ← meanings t'
        withLocalDecl (premiseName t) bi t' fun h => do
          let (b', _) ← present b
          mkForallFVars #[h] (← meanings b')
      else return (← meanings (← present s).1)
    | _ => return (← meanings (← present s).1)
  | name :: rest =>
    let s ← whnf e
    match s with
    | .forallE _ ty body bi =>
      let ty ← ZkcFormal.computedTypes ty
      withLocalDecl name bi ty fun x => do
        let .forallE _ vty vbody vbi ← whnfCore (body.instantiate1 x)
          | throwError "source names: expected the validity of {name}"
        withLocalDecl (Name.mkSimple ("valid_" ++ name.toString)) vbi vty fun hv => do
          let next ← inputsFrom rest (vbody.instantiate1 hv).headBeta
          mkForallFVars #[x, hv] next
    | _ =>
      let_expr Exists ty pair := s | throwError "source names: expected the binder of {name} in {s}"
      let .lam _ _ pbody pbi := pair | throwError "source names: expected a binder in {pair}"
      let ty' ← ZkcFormal.computedTypes ty
      let lam ← withLocalDecl name pbi ty' fun x => do
        let_expr And valid more := (← whnfCore (pbody.instantiate1 x))
          | throwError "source names: expected the validity of {name}"
        let next ← inputsFrom rest more.headBeta
        mkLambdaFVars #[x] (← mkAppM ``And #[valid, next])
      return mkApp2 s.appFn!.appFn! ty lam

/-- A witness telescope, its binders named `witness<i>`, then its validity premises. -/
partial def witnesses (e : Expr) : MetaM Expr := do
  let count := (← listCells (e.getArg! 2)).length
  let rec go (i : Nat) (cur : Expr) : MetaM Expr := do
    if i < count then
      let .forallE _ ty body bi ← whnf cur | throwError "source names: expected witness {i}"
      let ty ← ZkcFormal.computedTypes ty
      withLocalDecl (Name.mkSimple s!"witness{i}") bi ty fun x => do
        mkForallFVars #[x] (← go (i + 1) (body.instantiate1 x).headBeta)
    else validities count 0 cur
  go 0 e

/-- The validity premises of the witnesses, then the relation's result. -/
partial def validities (count i : Nat) (cur : Expr) : MetaM Expr := do
  if i < count then
    let .forallE n ty body bi ← whnf cur | throwError "source names: expected validity {i}"
    withLocalDecl n bi ty fun h => do
      mkForallFVars #[h] (← validities count (i + 1) (body.instantiate1 h).headBeta)
  else
    meanings (← whnf cur)

end

/-- The named view of a proposition, checked to be the proposition. -/
def view (e : Expr) : MetaM Expr := do
  let e ← instantiateMVars e
  let (v, changed) ← present e
  unless changed do throwError "source names: no input or witness telescope in{indentExpr e}"
  let v ← subjectFields v
  unless ← isDefEq v e do
    throwError "source names: the view differs from the term{indentExpr v}\nexpected{indentExpr e}"
  return v

/-- How many binders a proposition begins with. -/
private def leadingBinders : Expr → Nat
  | .forallE _ _ body _ => leadingBinders body + 1
  | .mdata _ e => leadingBinders e
  | _ => 0

/-- **Introduce the binders of a library term by the names of the source.** -/
elab "source_intro" : tactic => liftMetaTactic fun goal => do
  let target ← instantiateMVars (← goal.getType)
  let v ← view target
  let goal ← goal.replaceTargetDefEq v
  let (_, introduced) ← goal.introNP (leadingBinders v)
  return [introduced]

/-- The named view of a proposition of the library (a term of type `Prop`). -/
elab "source_view% " t:term : term => do
  let e ← elabTermEnsuringType t (some (.sort .zero))
  synthesizeSyntheticMVarsNoPostponing
  view e

/-- A proof read at the named view of its proposition, for application by name. -/
elab "named% " t:term : term => do
  let h ← elabTerm t none
  synthesizeSyntheticMVarsNoPostponing
  let h ← instantiateMVars h
  let v ← view (← inferType h)
  mkExpectedTypeHint h v

/-- `source_view N : P` declares the view `N` of `P` and `N_iff : N ↔ P`, by `Iff.rfl`. -/
macro "source_view " n:ident " : " t:term : command => do
  let iff := mkIdentFrom n (n.getId.appendAfter "_iff")
  `(def $n : Prop := source_view% $t
    theorem $iff : $n ↔ $t := Iff.rfl)

/-- `#view_names V : P`: the value of the view `V` is `source_view% P`, binder names included
(`Expr.equal`; `Iff.rfl` and the comparator's `Expr.eqv` do not compare binder names). -/
elab "#view_names " v:ident " : " t:term : command => liftTermElabM do
  let name ← realizeGlobalConstNoOverloadWithInfo v
  let some (.defnInfo d) := (← getEnv).find? name | throwError "{name} is not a definition"
  let e ← elabTermEnsuringType t (some (.sort .zero))
  synthesizeSyntheticMVarsNoPostponing
  let expected ← view (← instantiateMVars e)
  unless Expr.equal d.value expected do
    throwError "{name}: the view's names are not those that the origins give{indentExpr d.value}\nexpected{indentExpr expected}"
  logInfo m!"{name}: the names are the origins'"

end ZkcFormal.Written.SourceNames
