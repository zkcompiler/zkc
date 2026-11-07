module

public import Zkc.Source.RegionReturnProjection
public import Zkc.Semantics.MonadicWeakestPrecondition

@[expose] public section

/-! An adapter to Lean's standard verification-condition interface. The
underlying execution is still the admitted region's denotation followed by
the selected handler. No additional source traversal or interpreter is used. -/
set_option autoImplicit false
namespace Zkc.Source.Region
open Std.WP Lean.Order PIR.WeakestPrecondition
variable {dialect : Dialect} {I : PIR.Signature} {M : Type → Type} [Monad M] [LawfulMonad M]
  {S E : Type} {handler : PIR.MonadHandler M I S E} {invariant : S → Prop}
  {meaning : RegionMeaning dialect I} {Γ outputs : List dialect.Ty}

theorem ReturnsSatisfying.iff_triple {body : Region dialect Γ outputs}
    {env : Environment meaning.Value Γ} {post : Values meaning.Value outputs → Prop} :
    ReturnsSatisfying handler invariant meaning body env post ↔
    (letI := wpMonadM handler
     Triple (body.denote meaning env) (fun state _ ↦ invariant state)
       (fun value state _ ↦ invariant state ∧ post value)
       estack⟨fun _ state _ ↦ invariant state⟩) := by
  rw [tripleM_iff_run]
  constructor
  · intro law state preceding valid
    apply (law state valid).weaken
    rintro ⟨outcome, current, events⟩ ⟨kept, returned⟩
    cases outcome with
    | stopped reason => exact kept
    | returned value => exact ⟨kept, returned value rfl⟩
  · intro law state valid
    apply (law state [] valid).weaken
    rintro ⟨outcome, current, events⟩ holds
    cases outcome with
    | stopped reason => exact ⟨holds, by intro _ impossible; cases impossible⟩
    | returned value => exact ⟨holds.1, by intro _ same; cases same; exact holds.2⟩

/-- Compose an operation specification with the remaining typed region.
The rule retains the source's dependent operand types rather than asking a
simplifier to unfold the whole denotation and its installed component table. -/
theorem denoteLetOp_spec {Pred EPred : Type} [Assertion Pred] [Assertion EPred]
    [WPMonad (PIR.Process I) Pred EPred]
    (meaning : RegionMeaning dialect I) (op : dialect.Op)
    (args : Operands Γ (dialect.arguments op)) (bodies : Regions dialect (dialect.regions op))
    (next : Region dialect (dialect.results op ++ Γ) outputs)
    (env : Environment meaning.Value Γ)
    (post : Values meaning.Value outputs → Pred) (stopped : EPred) :
    Triple ((Region.letOp op args bodies next).denote meaning env)
      (wp (meaning.operation op (args.eval env) (bodies.denote meaning))
        (fun returned ↦ wp (next.denote meaning (Environment.prepend env returned)) post stopped) stopped)
      post stopped := by
  rw [Region.denote]
  exact ⟨WPMonad.bind_le_wp_bind _ _ _ _⟩

theorem denoteRet_spec {Pred EPred : Type} [Assertion Pred] [Assertion EPred]
    [WPMonad (PIR.Process I) Pred EPred]
    (meaning : RegionMeaning dialect I) (args : Operands Γ outputs)
    (env : Environment meaning.Value Γ)
    (post : Values meaning.Value outputs → Pred) (stopped : EPred) :
    Triple ((Region.ret args).denote meaning env) (post (args.eval env)) post stopped := by
  rw [Region.denote]
  exact ⟨WPMonad.pure_le_wp_pure _ _ _⟩

theorem denoteBind_spec {Pred EPred : Type} [Assertion Pred] [Assertion EPred]
    [WPMonad (PIR.Process I) Pred EPred] {mid : List dialect.Ty}
    (meaning : RegionMeaning dialect I) (body : Region dialect Γ mid)
    (next : Region dialect (mid ++ Γ) outputs) (env : Environment meaning.Value Γ)
    (post : Values meaning.Value outputs → Pred) (stopped : EPred) :
    Triple ((Region.bind body next).denote meaning env)
      (wp (body.denote meaning env)
        (fun returned ↦ wp (next.denote meaning (Environment.prepend env returned)) post stopped) stopped)
      post stopped := by
  rw [Region.denote]
  exact ⟨WPMonad.bind_le_wp_bind _ _ _ _⟩

theorem denoteStop_spec (handler : PIR.MonadHandler M I S E)
    (meaning : RegionMeaning dialect I) (reason : PIR.Stop) (env : Environment meaning.Value Γ)
    (post : Values meaning.Value outputs → S → List E → Prop)
    (stopped : PIR.Stop → S → List E → Prop) :
    (letI := wpMonadM handler
     Triple ((Region.stop reason : Region dialect Γ outputs).denote meaning env)
       (stopped reason) post estack⟨stopped⟩) := by
  rw [Region.denote]
  exact haltM_spec handler reason post stopped

end Zkc.Source.Region
