module

public import Zkc.Source.Structure
public import Zkc.Source.ContextOperations
public import Zkc.Semantics.ReturnedPostcondition

@[expose] public section

/-! Split an admitted region at an operation on its continuation spine. The
prefix returns the live SSA values to the original operation and suffix. No
callback is moved out of its enclosing control flow. -/
set_option autoImplicit false
namespace Zkc.Source.Region
variable {d : Dialect} {Γ out : List d.Ty}

/-- The original inputs remain available at the selected operation. A
shadowing result has its own SSA slot. Actions in the prefix may still
change state or stop before this environment exists. -/
def Inherits {Δ : List d.Ty} (earlier : Region d Γ Δ) (embed : Renaming Γ Δ) : Prop :=
  ∀ {I : PIR.Signature} (meaning : RegionMeaning d I) (env : Environment meaning.Value Γ)
    {M : Type → Type} [Monad M] [LawfulMonad M] {S E : Type} (handler : PIR.MonadHandler M I S E) (before : S),
    PIR.Process.OnReturn handler before (earlier.denote meaning env)
      (fun live _ ↦ ∀ {ty} (ref : Var Γ ty), live.get (embed ref) = env ref)

private theorem inheritStep {added Δ : List d.Ty} {earlier : Region d (added ++ Γ) Δ}
    {embed : Renaming (added ++ Γ) Δ} (kept : Inherits earlier embed)
    {I : PIR.Signature} (meaning : RegionMeaning d I) (env : Environment meaning.Value Γ)
    {M : Type → Type} [Monad M] [LawfulMonad M] {S E : Type} (handler : PIR.MonadHandler M I S E)
    (before : S) (head : PIR.Process I (Values meaning.Value added)) :
    PIR.Process.OnReturn handler before (head.bind fun reply ↦ earlier.denote meaning (env.prepend reply))
      (fun live _ ↦ ∀ {ty} (ref : Var Γ ty), live.get (embed (ref.weakenPrefix added)) = env ref) := by
  apply PIR.Process.OnReturn.bindAny
  intro reply state
  exact (kept meaning (env.prepend reply) handler state).weaken fun _ valid live returned _ ref ↦
    (valid live returned (ref.weakenPrefix added)).trans (env.prepend_weakenPrefix reply ref)

structure OperationCut (root : Region d Γ out) where
  context : List d.Ty
  before : Region d Γ context
  op : d.Op
  arguments : Operands context (d.arguments op)
  callbacks : Regions d (d.regions op)
  next : Region d (d.results op ++ context) out
  inherited : Renaming Γ context
  retains : Inherits before inherited
  exactRun : ∀ {I : PIR.Signature} (meaning : RegionMeaning d I) (env : Environment meaning.Value Γ),
    root.denote meaning env = (before.denote meaning env).bind fun live ↦
      (letOp op arguments callbacks next).denote meaning live.get

/-- Execute through the selected operation, retaining both its reply and the
environment needed by the original continuation. -/
def OperationCut.reached {root : Region d Γ out} (cut : OperationCut root)
    {I : PIR.Signature} (meaning : RegionMeaning d I) (env : Environment meaning.Value Γ) :=
  (cut.before.denote meaning env).bind fun live ↦
    (meaning.operation cut.op (cut.arguments.eval live.get) (cut.callbacks.denote meaning)).bind
      fun reply ↦ .done (live, reply)

theorem OperationCut.resume {root : Region d Γ out} (cut : OperationCut root)
    {I : PIR.Signature} (meaning : RegionMeaning d I) (env : Environment meaning.Value Γ) :
    root.denote meaning env = (cut.reached meaning env).bind fun (live, reply) ↦
      cut.next.denote meaning (Environment.prepend live.get reply) := by
  refine (cut.exactRun meaning env).trans ?_
  simp only [reached, Region.denote, PIR.Process.bind_assoc, PIR.Process.bind]

/-- Select the first matching operation following only ordinary continuations.
A return or stop ends the search. Earlier actions and nested regions execute
in their original order and a stopped prefix skips the selected occurrence. -/
def cutFirst (select : d.Op → Bool) {Γ out : List d.Ty} (root : Region d Γ out) : Option (OperationCut root) :=
  match root with
  | .ret _ | .stop _ => none
  | .letOp op args bodies next =>
    if select op then
      some ⟨_, .ret (Operands.identity _), op, args, bodies, next, (fun v ↦ v), by
        intro I meaning env M inst lawful S E handler state
        apply Zkc.MonadicPostcondition.pure
        intro value eq
        cases eq
        exact fun ref ↦ Environment.toValues_get env ref, by
        intros
        simp only [Region.denote, PIR.Process.bind, Operands.get_eval_identity]⟩
    else do
      let cut ← cutFirst select next
      return ⟨cut.context, .letOp op args bodies cut.before, cut.op, cut.arguments, cut.callbacks, cut.next,
        (fun v ↦ cut.inherited (v.weakenPrefix _)), by
          intro I meaning env M inst lawful S E handler state
          exact inheritStep cut.retains meaning env handler state _, by
        intro I meaning env
        simp only [Region.denote, PIR.Process.bind_assoc]
        congr 1
        funext reply
        exact cut.exactRun meaning (env.prepend reply)⟩
  | .bind body next => do
    let cut ← cutFirst select next
    return ⟨cut.context, .bind body cut.before, cut.op, cut.arguments, cut.callbacks, cut.next,
      (fun v ↦ cut.inherited (v.weakenPrefix _)), by
        intro I meaning env M inst lawful S E handler state
        exact inheritStep cut.retains meaning env handler state _, by
      intro I meaning env
      simp only [Region.denote, PIR.Process.bind_assoc]
      congr 1
      funext reply
      exact cut.exactRun meaning (env.prepend reply)⟩

end Zkc.Source.Region
