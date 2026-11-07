module

public import Zkc.Source.DerivationLaws
public import Zkc.Source.DenotationLaws
public import Zkc.Semantics.HandlerReturn
public meta import Lean.Elab.Tactic

@[expose] public section

/-! Check only the live operands consumed by a later region. Each reached
instruction must determine its own successful reply under the same handler.
Stops retain their original state and bypass every later instruction. -/
set_option autoImplicit false
namespace Zkc.Source.Region
variable {dialect : Dialect} {I : PIR.Signature} {m : Type → Type} [Monad m] [LawfulMonad m]
  {S E A : Type} {handler : PIR.MonadHandler m I S E} {invariant : S → Prop}
  {meaning : RegionMeaning dialect I} {Γ outputs : List dialect.Ty}

def ReturnsSatisfying (handler : PIR.MonadHandler m I S E) (invariant : S → Prop)
    (meaning : RegionMeaning dialect I) (body : Region dialect Γ outputs) (env : Environment meaning.Value Γ)
    (post : Values meaning.Value outputs → Prop) : Prop :=
  ∀ state, invariant state → Std.Do.Internal.Ensures
    (fun record ↦ invariant record.state ∧ ∀ out, record.outcome = .returned out → post out)
    ((body.denote meaning env).runM handler state)

def ReturnsProjection (handler : PIR.MonadHandler m I S E) (invariant : S → Prop)
    (meaning : RegionMeaning dialect I) (body : Region dialect Γ outputs) (env : Environment meaning.Value Γ)
    (project : Values meaning.Value outputs → A) (expected : A) : Prop :=
  ReturnsSatisfying handler invariant meaning body env (fun out ↦ project out = expected)

theorem returnsOfLaw {op : dialect.Op} {args : Values meaning.Value (dialect.arguments op)}
    {bodies : Values (RegionFunction meaning.Value I) (dialect.regions op)}
    {reply : Values meaning.Value (dialect.results op)}
    (law : meaning.OperationLaw (fun op ↦ .call op .done) op args bodies (.done reply)) :
    PIR.Process.ReturnsUnder handler invariant (meaning.operation op args bodies) reply := by
  have eq := law bodies (RegionFunctions.translate_identity bodies)
  rw [PIR.Process.interpret_identity] at eq
  exact PIR.Process.ReturnsUnder.ofEquation eq (.done reply)

theorem ReturnsSatisfying.letOp {op : dialect.Op} {args : Operands Γ (dialect.arguments op)}
    {bodies : Regions dialect (dialect.regions op)} {next : Region dialect (dialect.results op ++ Γ) outputs}
    {inputs : Values meaning.Value Γ} {post : Values meaning.Value outputs → Prop}
    {reply : Values meaning.Value (dialect.results op)}
    (operation : PIR.Process.ReturnsUnder handler invariant
      (meaning.operation op (Operands.eval inputs.get args) (bodies.denote meaning)) reply)
    (tail : ReturnsSatisfying handler invariant meaning next (reply.append inputs).get post) :
    ReturnsSatisfying handler invariant meaning (.letOp op args bodies next) inputs.get post := by
  intro state valid
  rw [Region.denote, PIR.runM_bind]
  apply (operation state valid).bind
  rintro ⟨out, current, events⟩ ⟨kept, agrees⟩
  cases out with
  | stopped why => exact Zkc.MonadicPostcondition.pure _ _ ⟨kept, by intro _ eq; cases eq⟩
  | returned actual =>
    obtain rfl := agrees actual rfl
    have replay : ReturnsSatisfying handler invariant meaning next
        (Environment.prepend inputs.get actual) post :=
      (Environment.prepend_values_get inputs actual).symm ▸ tail
    exact Zkc.MonadicPostcondition.map (replay current kept) _ (fun _ post ↦ post)

/-- A source operation that stops precludes any successful return from
the region and leaves the state invariant intact. -/
theorem ReturnsSatisfying.letHalt {op : dialect.Op} {args : Operands Γ (dialect.arguments op)}
    {bodies : Regions dialect (dialect.regions op)} {next : Region dialect (dialect.results op ++ Γ) outputs}
    {inputs : Values meaning.Value Γ} {post : Values meaning.Value outputs → Prop} {why : PIR.Stop}
    (operation : meaning.operation op (Operands.eval inputs.get args) (bodies.denote meaning) = .halt why) :
    ReturnsSatisfying handler invariant meaning (.letOp op args bodies next) inputs.get post := by
  intro state valid
  rw [Region.denote, operation]
  exact Zkc.MonadicPostcondition.pure _ _ ⟨valid, by intro _ eq; cases eq⟩

/-- A checked pure operation contributes its success condition to the actual
continuation. The refused branch never needs a proof of that continuation. -/
theorem ReturnsSatisfying.letChecked {op : dialect.Op} {args : Operands Γ (dialect.arguments op)}
    {bodies : Regions dialect (dialect.regions op)} {next : Region dialect (dialect.results op ++ Γ) outputs}
    {inputs : Values meaning.Value Γ} {post : Values meaning.Value outputs → Prop}
    {reply : Values meaning.Value (dialect.results op)} {condition : Prop} [Decidable condition]
    {reason : PIR.Stop}
    (operation : meaning.operation op (Operands.eval inputs.get args) (bodies.denote meaning) =
      if condition then .done reply else .halt reason)
    (tail : condition → ReturnsSatisfying handler invariant meaning next (reply.append inputs).get post) :
    ReturnsSatisfying handler invariant meaning (.letOp op args bodies next) inputs.get post := by
  by_cases holds : condition
  · exact ReturnsSatisfying.letOp
      (PIR.Process.ReturnsUnder.ofEquation (operation.trans (ite_eq_left holds)) (.done reply)) (tail holds)
  · exact ReturnsSatisfying.letHalt (operation.trans (ite_eq_right holds))

theorem ReturnsProjection.letOp {op : dialect.Op} {args : Operands Γ (dialect.arguments op)}
    {bodies : Regions dialect (dialect.regions op)} {next : Region dialect (dialect.results op ++ Γ) outputs}
    {inputs : Values meaning.Value Γ} {project : Values meaning.Value outputs → A}
    {expected : A} {reply : Values meaning.Value (dialect.results op)}
    (operation : PIR.Process.ReturnsUnder handler invariant
      (meaning.operation op (Operands.eval inputs.get args) (bodies.denote meaning)) reply)
    (tail : ReturnsProjection handler invariant meaning next (reply.append inputs).get project expected) :
    ReturnsProjection handler invariant meaning (.letOp op args bodies next) inputs.get project expected :=
  ReturnsSatisfying.letOp operation tail

theorem ReturnsSatisfying.ret {args : Operands Γ outputs} {env : Environment meaning.Value Γ}
    {post : Values meaning.Value outputs → Prop} (result : post (args.eval env)) :
    ReturnsSatisfying handler invariant meaning (.ret args) env post :=
  fun _ kept ↦ Zkc.MonadicPostcondition.pure _ _ ⟨kept, by intro _ eq; cases eq; exact result⟩

theorem ReturnsSatisfying.stop {reason : PIR.Stop} {env : Environment meaning.Value Γ}
    {post : Values meaning.Value outputs → Prop} :
    ReturnsSatisfying handler invariant meaning (.stop reason) env post := by
  intro state kept
  rw [Region.denote]
  exact Zkc.MonadicPostcondition.pure _ _ ⟨kept, by intro _ eq; cases eq⟩

theorem ReturnsProjection.ret {args : Operands Γ outputs} {env : Environment meaning.Value Γ}
    {project : Values meaning.Value outputs → A} :
    ReturnsProjection handler invariant meaning (.ret args) env project (project (Operands.eval env args)) :=
  ReturnsSatisfying.ret rfl

open Lean Meta Elab Tactic in
/-- Select an operation by its syntax before applying a handler law. Trying
all handler equations by definitional equality can unfold an entire installed
table, even on an unrelated mark. The kernel still checks the local law. -/
private meta def projectStep (head : Ident) (inner : Option Ident) (halt := false)
    (checked := false) : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let type := (← instantiateMVars (← goal.getType)).cleanupAnnotations
  let projected := type.isAppOf ``ReturnsProjection
  unless projected || type.isAppOf ``ReturnsSatisfying do throwError "expected a region return judgment, found {type.getAppFn}"
  let args := type.getAppArgs
  let body ← whnf args[args.size - (if projected then 4 else 3)]!
  unless body.isAppOf ``Region.letOp do throwError "expected a source operation"
  let fields := body.getAppArgs
  let op ← whnf fields[fields.size - 4]!
  let constructor ← realizeGlobalConstNoOverloadWithInfo head
  unless op.isAppOf constructor do throwError "different source operation"
  if let some nested := inner then
    let target ← realizeGlobalConstNoOverloadWithInfo nested
    unless (← whnf op.getAppArgs[0]!).isAppOf target do throwError "different nested operation"
  if checked && projected then throwError "checked operation requires a return postcondition"
  let rule := if checked then ``ReturnsSatisfying.letChecked else if halt then ``ReturnsSatisfying.letHalt
    else if projected then ``ReturnsProjection.letOp else ``ReturnsSatisfying.letOp
  let goals ← goal.apply (← mkConstWithFreshMVarLevels rule)
    {newGoals := .nonDependentOnly, allowSynthFailures := checked}
  replaceMainGoal goals

elab "project_step " head:ident "[" nested:ident "]" : tactic => projectStep head (some nested)
elab "project_step " head:ident : tactic => projectStep head none
elab "project_halt " head:ident : tactic => projectStep head none true
elab "project_checked " head:ident : tactic => projectStep head none false true

open Lean Meta Elab Tactic in
/-- Follow a typed operand through explicit result prefixes. Stop at an unknown
caller tuple, keeping its original reference and semantic value opaque. -/
private meta partial def projectValue (values reference : Expr) : MetaM Expr := do
  let tuple ← whnf values
  let position ← whnf reference
  if tuple.isAppOf ``Values.cons then
    let fields := tuple.getAppArgs
    if position.isAppOf ``Var.here then
      return fields[fields.size - 2]!
    if position.isAppOf ``Var.there then
      return ← projectValue fields.back! position.getAppArgs.back!
  mkAppM ``Values.get #[tuple, position]

open Lean Meta Elab Tactic in
/-- Normalize only the ordered tuple and its typed projections. In particular,
do not normalize the mathematical values stored in that tuple. -/
private meta partial def projectValues (values : Expr) : MetaM Expr := do
  let tuple ← whnf values
  unless tuple.isAppOf ``Values.cons do return tuple
  let fields := tuple.getAppArgs
  let mut value := fields[fields.size - 2]!.cleanupAnnotations
  repeat
    if value.isHeadBetaTarget then
      value := value.headBeta.cleanupAnnotations
    else if value.isAppOf ``Values.get then
      let args := value.getAppArgs
      let projected ← projectValue args[args.size - 2]! args.back!
      if projected == value then break
      value := projected.cleanupAnnotations
    else break
  let tail ← projectValues fields.back!
  return mkAppN tuple.getAppFn
    ((fields.set! (fields.size - 2) value).set! (fields.size - 1) tail)

open Lean Meta Elab Tactic in
/-- Derive the actual output layout before handing its mathematical
postcondition to the author. All normalization is kernel-checked conversion. -/
elab "project_return" : tactic => withMainContext do
  let goal ← getMainGoal
  let type := (← instantiateMVars (← goal.getType)).cleanupAnnotations
  unless type.isAppOf ``ReturnsSatisfying do throwError "expected a region return judgment"
  let args := type.getAppArgs
  let body ← whnf args[args.size - 3]!
  unless body.isAppOf ``Region.ret do throwError "expected a source return"
  let values ← projectValues (← mkAppM ``Operands.eval
    #[args[args.size - 2]!, body.getAppArgs.back!])
  let goals ← goal.apply (← mkConstWithFreshMVarLevels ``ReturnsSatisfying.ret)
  match goals with
  | [result] => replaceMainGoal [← result.replaceTargetDefEq (mkApp args.back! values)]
  | _ => throwError "expected one return postcondition"

end Zkc.Source.Region
