module

public import ZkcFormal.Written.Goal
public meta import Lean

namespace ZkcFormal.Written.Goal

/-- Publish the named telescope together with the exact semantic application that it presents. -/
@[expose] public def checkedSurface (canonical presentation : Prop) (_ : presentation = canonical) :
    Prop := presentation

public meta section

open Lean Meta Elab Term
open Zkc.Core (HList Model fnMeaning roleMeaning Process)
open Zkc.Subject
open ZkcFormal.ProbabilisticProcess

/-- Inspect constructor spines one cell at a time. A deployed header may compute its list. -/
private partial def listCells (e : Expr) : MetaM (List Expr) := do
  let s ← whnf e
  match_expr s with
  | List.nil _ => return []
  | List.cons _ x xs => return x :: (← listCells xs)
  | _ => throwError "expected a concrete deployed list, got {s}"

private def numeral (e : Expr) : MetaM Nat := do
  let some n ← getNatValue? (← whnf e) | throwError "expected a concrete role or arity in {e}"
  return n

private structure Port where
  name : Name
  ty : Expr

private structure Signature where
  model : Expr
  ports : List Port
  witnesses : List Expr

private def validName (n : Name) := Name.mkSimple ("valid_" ++ n.toString)

/-- Match the issuer's public spelling rule on the full list, including invisible duplicates. -/
private def inputName (raw : String) (ordinal count : Nat) (reserved : List Name) : Name :=
  let n := Name.mkSimple ("input_" ++ raw)
  let plain := !raw.isEmpty && raw.all (fun c => c.isAlphanum || c == '_') && !raw.front.isDigit
  if plain && count == 1 && !reserved.contains n && !reserved.contains (validName n) then n
  else Name.mkSimple s!"port{ordinal}"

/-- The goal occupies the same parameter of all four library applications. Check the actual
application before selecting any operand, including when the helper supplies a proof. -/
private def application (e : Expr) (head : Name) : MetaM Expr := do
  let e := e.consumeMData
  unless e.isAppOfArity head (← getConstInfo head).type.getForallArity do
    throwError "expected the canonical application of {head}, got {e}"
  unless (e.getArg! 4).isConst do throwError "expected a named written goal in {e}"
  return e

private def signature (canonical origin : Expr) (reserved : List Name) : MetaM Signature := do
  let g := canonical.getArg! 4
  let goalType ← inferType g
  let originType ← inferType origin
  unless goalType.isAppOfArity ``WrittenGoal 3 && originType.isAppOfArity ``RootOrigins 3 &&
      goalType.appArg! == originType.appArg! do
    throwError "goal {g} and origins {origin} must name the same written root"
  let root := goalType.appArg!
  let raw ← listCells (← mkAppM ``Array.toList #[← mkProjection origin `inputNames])
  let names ← raw.mapM fun e => do
    let some s := getStringValue? (← whnf e) | throwError "expected a deployed spelling in {e}"
    return s
  let counts := names.foldl (init := ({} : Std.HashMap String Nat)) fun m s =>
    m.insert s (m.getD s 0 + 1)
  let header ← mkProjection (← mkProjection root `entry) `header
  let inputs ← listCells (← mkProjection header `ins)
  unless names.length == inputs.length do throwError "input origins and deployed header disagree"
  let verifier ← numeral (← mkProjection (← mkProjection root `verifier) `val)
  -- Source annotations use the model vocabulary and ordinary Lean numerals for sizes and keys.
  let modelTy := fun t => do
    let t ← whnf t
    return t.replace fun e =>
      if e == goalType.getArg! 0 then some (canonical.getArg! 0)
      else if e.isAppOf ``OfNat.ofNat then some e
      else if let .lit (.natVal n) := e then some (mkNatLit n)
      else none
  let mut ports := #[]
  for ((s, input), i) in (names.zip inputs).zipIdx do
    let holders ← (← listCells (← mkProjection input `holders)).mapM numeral
    if holders.contains verifier then
      ports := ports.push ⟨inputName s i (counts.getD s 0) reserved, ← modelTy (← mkProjection input `ty)⟩
  let decision ← mkProjection g `decision
  let relation ← mkProjection (← mkProjection decision `relation) `header
  let args ← listCells (← mkProjection relation `ins)
  let arity ← numeral (← mkProjection (← mkProjection decision `arity) `val)
  return ⟨canonical.getArg! 1, ports.toList, ← (args.drop arity).mapM modelTy⟩

/-- Select the fields of the subject without unfolding the selected installation, members or cap
table. These named operands are the ones used by the published entry and rewrite theorems. -/
private def subjectFields (e : Expr) : MetaM Expr :=
  let selected := fun n => [``WrittenGoal, ``GoalFields, ``Decision, ``WrittenRoot,
    ``ProtocolEntry, ``FunctionEntry, ``Package, ``Fin].contains n
  Meta.transform e (pre := fun s => do
    if let some p ← reduceProjOf? s selected then return .visit p
    if let .proj n _ _ := s then
      if selected n then
        if let some p ← reduceProj? s then return .visit p
    return .continue)

/-- Make both the selected values and the hidden indices of the HList match direct rewrites. -/
private partial def operands (indices e : Expr) : MetaM Expr := do
  let s ← whnf e
  if s.isAppOf ``HList.nil then return s
  let_expr HList.cons indexType family _ _ value rest := s
    | throwError "expected a concrete operand list in {e}"
  let_expr List.cons _ index tail := ← whnf indices
    | throwError "expected a matching header input for {e}"
  let v ← whnf value
  let v := if v.isConstOf ``PUnit.unit then Lean.mkConst ``Unit.unit else v
  return mkAppN s.getAppFn #[indexType, family, index, tail, v, ← operands tail rest]

private def atHead (e : Expr) (head : Name) : MetaM Expr := do
  let some s ← whnfUntil e head | throwError "expected {head} in {e}"
  return s

private def meaning (e : Expr) (head : Name) : MetaM Expr := do
  let s ← subjectFields (← atHead e head)
  -- Both meanings infer their header from the member: a binder has its public header,
  -- while an installed member has the source header in its declared type.
  let memberType ← atHead (← inferType (s.getArg! 4)) ``Zkc.Core.Member
  let header := memberType.appArg!
  let inputs ← operands (← mkProjection header `ins) s.appArg!
  let args := s.appFn!.getAppArgs.set! 3 header
  return mkAppN s.getAppFn (args.push inputs)

private def forallParts (e : Expr) : MetaM (Name × Expr × Expr × BinderInfo) := do
  let .forallE n t b bi ← whnf e | throwError "expected a binder in {e}"
  return (n, t, b, bi)

private def ensureEqual (expected actual : Expr) : MetaM Unit := do
  unless ← isDefEq expected actual do
    throwError "written goal presentation differs from the library term{indentExpr actual}\nexpected{indentExpr expected}"

private def forallBinder (e : Expr) (n : Name) (domain : Expr)
    (rest : Expr → Expr → MetaM Expr) : MetaM Expr := do
  let (_, t, b, bi) ← forallParts e
  ensureEqual t domain
  withLocalDecl n bi domain fun x => do mkForallFVars #[x] (← rest x (b.instantiate1 x))

private def validityBinders (e : Expr) : List Expr → MetaM Expr
  | [] => do
    let s ← atHead e ``Eq
    let some (_, lhs, rhs) := s.eq? | throwError "expected the rejection equality"
    let result ← subjectFields (← atHead lhs ``functionResult)
    mkEq (mkApp result.appFn! (← meaning result.appArg! ``fnMeaning)) rhs
  | valid :: rest => do
    let (n, _, _, _) ← forallParts e
    forallBinder e n valid fun _ next => validityBinders next rest

/-- Accumulate the validity domains while opening all witness values in parameter order. -/
private def witnessBinders (model e : Expr) (i : Nat) (validities : List Expr) :
    List Expr → MetaM Expr
  | [] => validityBinders e validities.reverse
  | ty :: rest => do
    forallBinder e (.mkSimple s!"witness{i}") (← mkAppM ``Model.Val #[model, ty]) fun x next => do
      witnessBinders model next (i + 1) ((← mkAppM ``Model.Valid #[model, ty, x]) :: validities) rest

private def presentRejection (sig : Signature) (e : Expr) : MetaM Expr := do
  let canonical ← atHead e ``Soundness.Rejected
  let view ← witnessBinders sig.model canonical 0 [] sig.witnesses
  ensureEqual canonical view
  return view

private def processLeaf (samplers e : Expr) (head : Name) : MetaM Expr := do
  let s ← subjectFields (← atHead e head)
  let args := s.getAppArgs
  let some pos := args.findIdx? (·.isAppOf ``roleMeaning)
    | throwError "expected the verifier's roleMeaning in {s}"
  let process ← meaning args[pos]! ``roleMeaning
  let header := process.getArg! 3
  let original := mkAppN s.getAppFn (args.set! pos process)
  let leaf := original.replace fun e =>
    if e.isAppOfArity ``Zkc.Core.ProtocolHeader.outs 2 then some (mkApp e.appFn! header) else none
  -- The sampler is the next operand after the process in ReturnsWithin and the first
  -- explicit operand in paysWithin. The rest of either policy comes from the canonical leaf.
  let (policy, arity) := if head == ``ReturnsWithin then (``ReturnsWithin, 5) else (``paysWithin, 2)
  let some sampled := leaf.find? (·.isAppOfArity policy arity)
    | throwError "expected a sampler operand of {policy}"
  ensureEqual sampled.appArg! samplers
  return leaf.replace fun e => if e == sampled then some (mkApp e.appFn! samplers) else none

private def universal (sig : Signature) (leaf : Expr → MetaM Expr) (e : Expr) :
    List Port → MetaM Expr
  | [] => do
    let (_, rejected, _, _) ← forallParts e
    forallBinder e `rejected (← presentRejection sig rejected) fun _ next => leaf next
  | port :: rest => do
    forallBinder e port.name (← mkAppM ``Model.Val #[sig.model, port.ty]) fun x next => do
      forallBinder next (validName port.name) (← mkAppM ``Model.Valid #[sig.model, port.ty, x])
        fun _ after => universal sig leaf after rest

private def andParts (e : Expr) : MetaM (Expr × Expr) := do
  let s ← atHead e ``And
  return (s.appFn!.appArg!, s.appArg!)

private inductive ReceiptView where
  | existential (served : Expr)
  | constructor (result : Expr)

/-- Walk the receipt and its constructor together. When publishing the receipt, expand its
terminal rejection once. The constructor reuses that same rejection from the named receipt. -/
private def paired (view : ReceiptView) (sig : Signature) (q helper : Expr) : List Port → MetaM Expr
  | [] => do
    let (service, rejected) ← andParts q
    let (_, premise, body, _) ← forallParts helper
    ensureEqual rejected premise
    match view with
    | .existential served =>
      ensureEqual service served
      mkAppM ``And #[served, ← presentRejection sig premise]
    | .constructor result =>
      if body.hasLooseBVars then throwError "the receipt depends on the rejection proof"
      ensureEqual body result
      forallBinder helper `rejected rejected fun _ _ => pure result
  | port :: rest => do
    let exists_ ← atHead q ``Exists
    if let .constructor _ := view then
      unless exists_.appArg!.isLambda && exists_.appArg!.bindingName! == port.name do
        throwError "the named receipt uses a different binder for {port.name}"
    let (_, t, b, bi) ← forallParts helper
    let ty ← mkAppM ``Model.Val #[sig.model, port.ty]
    ensureEqual exists_.appFn!.appArg! ty
    ensureEqual t ty
    withLocalDecl port.name bi ty fun x => do
      let (valid, next) ← andParts (mkApp exists_.appArg! x)
      let (_, helperValid, after, info) ← forallParts (b.instantiate1 x)
      let v ← mkAppM ``Model.Valid #[sig.model, port.ty, x]
      ensureEqual valid v
      ensureEqual helperValid v
      withLocalDecl (validName port.name) info v fun hv => do
        let body ← paired view sig next (after.instantiate1 hv) rest
        match view with
        | .constructor _ => mkForallFVars #[x, hv] body
        | .existential _ =>
          let pair ← mkAppM ``And #[v, body]
          return ← mkAppM ``Exists #[← mkLambdaFVars #[x] pair]

/-- Expose the same cap and member names that an author can unfold in the goals of a walk
or the hypotheses of a receipt. Both abbreviations refer to concrete entries of this module. -/
private def publish (canonical view : Expr) (caps member_ : Ident) : TermElabM Expr := do
  let table := Lean.mkConst (← realizeGlobalConstNoOverloadWithInfo caps)
  let memberName := Lean.mkConst (← realizeGlobalConstNoOverloadWithInfo member_)
  let presentation := view.replace fun e =>
    if e.isAppOfArity ``CapTable.total 1 || e.isAppOfArity ``CapTable.budget 1 ||
        e.isAppOfArity ``CapTable.allowance 3 then some (mkApp e.appFn! table)
    else if !canonical.isAppOf ``ClaimOf && e.isAppOfArity ``fnMeaning 5 then
      some (mkApp e.appFn! memberName)
    else none
  check presentation
  ensureEqual canonical presentation
  -- Lean may extract this proof into a declaration. Keep its type on the named goal.
  return mkApp3 (mkConst ``checkedSurface) canonical presentation (← mkEqRefl canonical)

private def readTerm (s : Syntax) (type? : Option Expr := none) : TermElabM Expr := do
  let e ← elabTermEnsuringType s type?
  synthesizeSyntheticMVarsNoPostponing
  return (← instantiateMVars e).consumeMData

private def readSignature (target : Expr) (origin caps member_ witnessed : Ident) :
    TermElabM Signature := do
  let n ← realizeGlobalConstNoOverloadWithInfo origin
  signature target (mkConst n) [caps.getId, member_.getId, witnessed.getId]

/-- The specialized constructor selects the same mathematical arguments as this receipt. -/
private def constructorReceipt (helper : Expr) : Expr :=
  mkAppN (mkConst ``Witnessed) (helper.getAppArgs.extract 0 6)

/-- Publish the named input and rejection binders of a claim or fee judgment. -/
elab "goal_surface% " kind:ident origin:ident "(" caps:ident "," member_:ident "," witnessed:ident ")"
    samplers:(ident)? " in " t:term : term => do
  let (head, process) ← match kind.getId with
    | `claim => pure (``ClaimOf, ``ReturnsWithin)
    | `judged => pure (``Judged, ``Process.interpret)
    | _ => throwErrorAt kind "expected claim or judged"
  let canonical ← application (← readTerm t (some (.sort .zero))) head
  let sig ← readSignature canonical origin caps member_ witnessed
  let (_, pathTy, _, _) ← forallParts canonical
  let namedSamplers ← match samplers with
    | some id => pure (Lean.mkConst (← realizeGlobalConstNoOverloadWithInfo id))
    | none => mkAppM ``lawSamplers #[sig.model, canonical.getArg! 5]
  let view ← forallBinder canonical `path pathTy fun _ body =>
    universal sig (processLeaf namedSamplers · process) body sig.ports
  publish canonical view caps member_

/-- Publish the named existential proposition using the actual specialized library constructor. -/
elab "goal_receipt% " origin:ident "(" caps:ident "," member_:ident "," witnessed:ident ")"
    " in " t:term " using " constructor:term : term => do
  let q ← application (← readTerm t (some (.sort .zero))) ``Witnessed
  let helper ← application (← readTerm constructor) ``witnessed_of
  unless constructorReceipt helper == q do throwError "the constructor selects a different receipt"
  let sig ← readSignature q origin caps member_ witnessed
  let served ← inferType helper.appArg!
  publish q (← paired (.existential served) sig q (← inferType helper) sig.ports) caps member_

/-- Present the inferred constructor type with its alias's named receipt as the terminal result. -/
elab "goal_helper% " origin:ident "(" caps:ident "," member_:ident "," witnessed:ident ")"
    " in " constructor:term:max &" returning " out:ident : term => do
  let helper ← application (← readTerm constructor) ``witnessed_of
  let named ← realizeGlobalConstNoOverloadWithInfo out
  unless named.getString! == witnessed.getId.toString do throwErrorAt out "expected {witnessed}"
  let result := Lean.mkConst named
  let some body ← unfoldDefinition? result | throwErrorAt out "expected a published witness receipt"
  unless body.isAppOfArity ``checkedSurface 3 && body.getArg! 0 == constructorReceipt helper do
    throwErrorAt out "receipt does not publish the selected library application"
  let sig ← readSignature helper origin caps member_ witnessed
  let original ← inferType helper
  let view ← paired (.constructor result) sig (body.getArg! 1) original sig.ports
  check view
  ensureEqual original view
  return view

end
end ZkcFormal.Written.Goal
