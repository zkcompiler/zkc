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

theorem ReturnsProjection.ret {args : Operands Γ outputs} {env : Environment meaning.Value Γ}
    {project : Values meaning.Value outputs → A} :
    ReturnsProjection handler invariant meaning (.ret args) env project (project (Operands.eval env args)) :=
  ReturnsSatisfying.ret rfl

open Lean Meta Elab Tactic in
/-- Select an operation by its syntax before applying a handler law. Trying
all handler equations by definitional equality can unfold an entire installed
table, even on an unrelated mark. The kernel still checks the local law. -/
private meta def projectStep (head : Ident) (inner : Option Ident) : TacticM Unit := withMainContext do
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
  let rule := if projected then ``ReturnsProjection.letOp else ``ReturnsSatisfying.letOp
  let goals ← goal.apply (← mkConstWithFreshMVarLevels rule)
    {newGoals := .nonDependentOnly}
  replaceMainGoal goals

elab "project_step " head:ident "[" nested:ident "]" : tactic => projectStep head (some nested)
elab "project_step " head:ident : tactic => projectStep head none

end Zkc.Source.Region
