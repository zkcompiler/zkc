module

public import Zkc.Protocol.Construction.Region
public import Zkc.Program.Source.Component

/-! Common construction for optional participant values. These rules use the existing
component interpretation; helper-specific mathematics never routes source registers. -/

@[expose] public section
open PIR Zkc.Source Std.WP
namespace ProtocolProof.Construction
variable {dialect : Dialect} {I : Signature} {Pred EPred : Type}
  [Assertion Pred] [Assertion EPred] [WPMonad (Process I) Pred EPred]
  (meaning : RegionMeaning dialect I) (operations : ComponentOperations meaning)
  {Γ mid out : List dialect.Ty} (env : Environment (Component meaning.Value) Γ)
  (post : Values (Component meaning.Value) out → Pred) (stopped : EPred)

@[spec] theorem componentReturn (values : Operands Γ out) :
    ⦃post (Operands.eval env values)⦄ (Region.ret values).component meaning operations env
      ⦃post; stopped⦄ := by
  unfold Region.component
  exact ⟨WPMonad.pure_le_wp_pure (m := Process I) _ _ _⟩

@[spec] theorem componentStop (reason : Stop) :
    ⦃wp (Process.halt (I := I) (A := Values (Component meaning.Value) out) reason) post stopped⦄
      (Region.stop reason : Region dialect Γ out).component meaning operations env
      ⦃post; stopped⦄ := ⟨Lean.Order.PartialOrder.rel_refl⟩

@[spec] theorem componentBind (body : Region dialect Γ mid)
    (next : Region dialect (mid ++ Γ) out) :
    ⦃wp (body.component meaning operations env)
      (fun values => wp (next.component meaning operations (env.prepend values)) post stopped) stopped⦄
      (Region.bind body next).component meaning operations env ⦃post; stopped⦄ := by
  simpa only [Region.component, bind, binderNameHint] using
    (Spec.bind (m := Process I) (post := post) (epost := stopped)
      (body.component meaning operations env)
      (fun values => next.component meaning operations (env.prepend values)))

@[spec] theorem componentOperation (op : dialect.Op)
    (arguments : Operands Γ (dialect.arguments op))
    (bodies : Regions dialect (dialect.regions op))
    (next : Region dialect (dialect.results op ++ Γ) out) :
    ⦃wp (operations op (Operands.eval env arguments) (bodies.denote meaning))
      (fun values => wp (next.component meaning operations (env.prepend values)) post stopped) stopped⦄
      (Region.letOp op arguments bodies next).component meaning operations env ⦃post; stopped⦄ := by
  simpa only [Region.component, bind, binderNameHint] using
    (Spec.bind (m := Process I) (post := post) (epost := stopped)
      (operations op (Operands.eval env arguments) (bodies.denote meaning))
      (fun values => next.component meaning operations (env.prepend values)))

end ProtocolProof.Construction
