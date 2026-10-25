module

public import Zkc.Source.Region

@[expose] public section

/-! Total mathematical views of the same structured carrier.

Totality means immediate return, without interactions or stopping. It is a proved
semantic property, not a consequence of an operation's native effect annotation.
-/
set_option autoImplicit false
namespace Zkc.Source

variable {dialect : Dialect} {interface : PIR.Signature}

/-- A process returns a value without issuing an action or stopping. -/
def Returns {A : Type} (process : PIR.Process interface A) : Prop :=
  ∃ value, process = .done value

/-- All callbacks return for all of their declared inputs. -/
def RegionFunctions.Returns {Value : dialect.Ty → Type} {signatures}
    (bodies : Values (RegionFunction Value interface) signatures) : Prop :=
  ∀ signature (reference : Var signatures signature) args, Zkc.Source.Returns (bodies.get reference args)

/-- A sufficient totality contract. Checked operations generally need a restricted
input theorem instead; a potentially failing dot does not satisfy this contract. -/
def RegionMeaning.TotalOperation (meaning : RegionMeaning dialect interface) (op : dialect.Op) : Prop :=
  ∀ args bodies, RegionFunctions.Returns bodies → Returns (meaning.operation op args bodies)

mutual
  /-- Structural sufficient condition over the existing carrier, not a second syntax. -/
  def Region.Total (meaning : RegionMeaning dialect interface) {Γ out} : Region dialect Γ out → Prop
    | .ret _ => True
    | .stop _ => False
    | .letOp op _ bodies next => meaning.TotalOperation op ∧ bodies.Total meaning ∧ next.Total meaning
    | .bind body next => body.Total meaning ∧ next.Total meaning

  def Regions.Total (meaning : RegionMeaning dialect interface) {signatures} :
      Regions dialect signatures → Prop
    | .nil => True
    | .cons body tail => body.Total meaning ∧ tail.Total meaning
end

theorem Region.returns_of_total (meaning : RegionMeaning dialect interface) {Γ out}
    (region : Region dialect Γ out) (total : region.Total meaning)
    (env : Environment meaning.Value Γ) : Returns (region.denote meaning env) := by
  refine Region.rec
    (motive_1 := fun Γ _ region => region.Total meaning →
      ∀ env : Environment meaning.Value Γ, Returns (region.denote meaning env))
    (motive_2 := fun _ bodies => bodies.Total meaning →
      RegionFunctions.Returns (bodies.denote meaning))
    ?_ ?_ ?_ ?_ ?_ ?_ region total env
  · intro Γ out values _ env
    exact ⟨_, rfl⟩
  · intro Γ out reason total
    exact total.elim
  · intro Γ out op args bodies next bodiesIH nextIH total env
    obtain ⟨operation, bodyTotal, nextTotal⟩ := total
    obtain ⟨values, returned⟩ := operation (Operands.eval env args) (bodies.denote meaning)
      (bodiesIH bodyTotal)
    simp only [Region.denote, returned, PIR.Process.bind]
    exact nextIH nextTotal _
  · intro Γ mid out body next bodyIH nextIH total env
    obtain ⟨values, returned⟩ := bodyIH total.1 env
    simp only [Region.denote, returned, PIR.Process.bind]
    exact nextIH total.2 _
  · intro _ signature reference
    cases reference
  · intro inputs outputs rest body tail bodyIH tailIH total signature reference args
    cases reference with
    | here => exact bodyIH total.1 _
    | there reference => exact tailIH total.2 _ reference args

/-- A known immediate result remains valid in any effectful or stopping suffix. -/
theorem Region.bind_return (meaning : RegionMeaning dialect interface) {Γ mid out}
    (body : Region dialect Γ mid) (next : Region dialect (mid ++ Γ) out)
    (env : Environment meaning.Value Γ) (values : Values meaning.Value mid)
    (returned : body.denote meaning env = .done values) :
    (body.bind next).denote meaning env = next.denote meaning (env.prepend values) := by
  simp only [Region.denote, returned, PIR.Process.bind]

/-- A proved immediate operation result can be substituted in any suffix.
The premise concerns its actual arguments and callbacks, not an effect flag. -/
theorem Region.letOp_return (meaning : RegionMeaning dialect interface) {Γ out}
    (op : dialect.Op) (args : Operands Γ (dialect.arguments op))
    (bodies : Regions dialect (dialect.regions op))
    (next : Region dialect (dialect.results op ++ Γ) out)
    (env : Environment meaning.Value Γ) (values : Values meaning.Value (dialect.results op))
    (returned : meaning.operation op (Operands.eval env args) (bodies.denote meaning) =
      .done values) :
    (Region.letOp op args bodies next).denote meaning env =
      next.denote meaning (env.prepend values) := by
  simp only [Region.denote, returned, PIR.Process.bind]

/-- Discarding a zero-result computation is valid only with an immediate-return
proof at the actual input. Lack of result uses alone does not justify removal. -/
theorem Region.bind_empty_return (meaning : RegionMeaning dialect interface) {Γ out}
    (body : Region dialect Γ []) (next : Region dialect Γ out)
    (env : Environment meaning.Value Γ)
    (returned : body.denote meaning env = .done .nil) :
    (body.bind next).denote meaning env = next.denote meaning env := by
  exact Region.bind_return meaning body next env .nil returned

end Zkc.Source
