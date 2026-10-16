module

public import Zkc.Source.Region
public import Zkc.Semantics.Interpretation

@[expose] public section

/-! Translation of higher-order operations requires an explicit compatibility law.

A callback's type alone does not prevent an operation from inspecting its process
shape. Translating callbacks need not commute with an arbitrary operation.
-/
set_option autoImplicit false
namespace Zkc.Source

variable {dialect : Dialect} {I J : PIR.Signature}

/-- Interpret callbacks pointwise, retaining their input and result signatures. -/
def RegionFunctions.translate {Value : dialect.Ty → Type}
    (operations : PIR.OperationInterpretation I J) {signatures} :
    Values (RegionFunction Value I) signatures → Values (RegionFunction Value J) signatures
  | .nil => .nil
  | .cons body tail =>
    .cons (fun args => (body args).interpret operations) (translate operations tail)

/-- A target operation implementation with a law for arbitrary effectful callbacks. -/
structure RegionMeaning.Translation (meaning : RegionMeaning dialect I)
    (operations : PIR.OperationInterpretation I J) where
  operation : (op : dialect.Op) → Values meaning.Value (dialect.arguments op) →
    Values (RegionFunction meaning.Value J) (dialect.regions op) →
      PIR.Proc J (Values meaning.Value (dialect.results op))
  commutes : ∀ op args bodies,
    operation op args (RegionFunctions.translate operations bodies) =
      (meaning.operation op args bodies).interpret operations

abbrev RegionMeaning.Translation.meaning {meaning : RegionMeaning dialect I}
    {operations : PIR.OperationInterpretation I J} (translation : meaning.Translation operations) :
    RegionMeaning dialect J where
  Value := meaning.Value
  operation := translation.operation

mutual
  theorem Region.denote_translate (meaning : RegionMeaning dialect I)
      (operations : PIR.OperationInterpretation I J) (translation : meaning.Translation operations)
      {Γ out} (region : Region dialect Γ out) (env : Environment meaning.Value Γ) :
      region.denote translation.meaning env = (region.denote meaning env).interpret operations := by
    cases region with
    | ret values => rfl
    | stop reason => rfl
    | letOp op args bodies next =>
      simp only [Region.denote, PIR.Proc.interpret_bind, Regions.denote_translate meaning operations translation bodies,
        RegionMeaning.Translation.meaning, translation.commutes]
      congr 1
      funext values
      exact Region.denote_translate meaning operations translation next _
    | bind body next =>
      simp only [Region.denote, PIR.Proc.interpret_bind, Region.denote_translate meaning operations translation body]
      congr 1
      funext values
      exact Region.denote_translate meaning operations translation next _
  termination_by sizeOf region
  decreasing_by all_goals subst_vars; all_goals simp_all; all_goals omega

  theorem Regions.denote_translate (meaning : RegionMeaning dialect I)
      (operations : PIR.OperationInterpretation I J) (translation : meaning.Translation operations)
      {signatures} (bodies : Regions dialect signatures) :
      bodies.denote translation.meaning = RegionFunctions.translate operations (bodies.denote meaning) := by
    cases bodies with
    | nil => rfl
    | cons body tail =>
      simp only [Regions.denote, RegionFunctions.translate, Regions.denote_translate meaning operations translation tail]
      congr 1
      funext values
      exact Region.denote_translate meaning operations translation body _
  termination_by sizeOf bodies
  decreasing_by all_goals subst_vars; all_goals simp_all; all_goals omega
end

end Zkc.Source
