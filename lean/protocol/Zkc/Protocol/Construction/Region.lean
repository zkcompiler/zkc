module

public import Zkc.Protocol.Construction.Process
public import Zkc.Program.Region.Basic

/-! Structural specifications of the actual shared Region.

The specifications expose no cursor, register index, execution mark or guessed source body.
The operation meaning owns its callbacks; the generic rule never executes a callback eagerly.
-/

@[expose] public section

open PIR Zkc.Source Std.WP

namespace ProtocolProof.Construction

variable {dialect : Dialect} {I : Signature}
  {Pred EPred : Type} [Assertion Pred] [Assertion EPred]
  [WPMonad (Process I) Pred EPred]
  (meaning : RegionMeaning dialect I)
  {Γ mid out : List dialect.Ty}
  (env : Environment meaning.Value Γ)
  (post : Values meaning.Value out → Pred) (stopped : EPred)

@[spec] theorem regionReturn (values : Operands Γ out) :
    ⦃post (Operands.eval env values)⦄ (Region.ret values).denote meaning env
      ⦃post; stopped⦄ :=
  by
    unfold Region.denote
    exact ⟨WPMonad.pure_le_wp_pure (m := Process I) _ _ _⟩

@[spec] theorem regionStop (reason : Stop) :
    ⦃wp (Process.halt (I := I) (A := Values meaning.Value out) reason) post stopped⦄
      (Region.stop reason : Region dialect Γ out).denote meaning env ⦃post; stopped⦄ :=
  ⟨Lean.Order.PartialOrder.rel_refl⟩

@[spec] theorem regionBind (body : Region dialect Γ mid)
    (next : Region dialect (mid ++ Γ) out) :
    ⦃wp (body.denote meaning env)
      (fun values => wp (next.denote meaning (env.prepend values)) post stopped) stopped⦄
      (Region.bind body next).denote meaning env ⦃post; stopped⦄ :=
  by
    simpa only [Region.denote, bind, binderNameHint] using
      (Spec.bind (m := Process I) (post := post) (epost := stopped)
        (body.denote meaning env) (fun values => next.denote meaning (env.prepend values)))

@[spec] theorem regionOperation (op : dialect.Op)
    (arguments : Operands Γ (dialect.arguments op))
    (bodies : Regions dialect (dialect.regions op))
    (next : Region dialect (dialect.results op ++ Γ) out) :
    ⦃wp (meaning.operation op (Operands.eval env arguments) (bodies.denote meaning))
      (fun values => wp (next.denote meaning (env.prepend values)) post stopped) stopped⦄
      (Region.letOp op arguments bodies next).denote meaning env ⦃post; stopped⦄ :=
  by
    simpa only [Region.denote, bind, binderNameHint] using
      (Spec.bind (m := Process I) (post := post) (epost := stopped)
        (meaning.operation op (Operands.eval env arguments) (bodies.denote meaning))
        (fun values => next.denote meaning (env.prepend values)))

/-- Lexical placement changes the actual arguments, never the meaning or private service state. -/
@[spec] theorem regionRename {Δ : List dialect.Ty} (body : Region dialect Δ out)
    (rename : Renaming Δ Γ) :
    ⦃wp (body.denote meaning (fun reference => env (rename reference))) post stopped⦄
      (body.rename rename).denote meaning env ⦃post; stopped⦄ := by
  rw [Region.denote_rename]
  exact ⟨Lean.Order.PartialOrder.rel_refl⟩

end ProtocolProof.Construction
