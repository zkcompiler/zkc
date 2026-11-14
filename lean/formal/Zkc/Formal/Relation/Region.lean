module

public import Zkc.Formal.Relation.Process

@[expose] public section

/-! Two models related: regions.

A region has a meaning for each of two models, over one dialect. When every operation of the
region is compatible (on related operands and related nested regions its two meanings are
related), the two meanings of the region are related on related environments
(`region_related`). The operations of a region are named by a test, so that a region is asked
only for the operations it has (`Region.all`).
-/

set_option autoImplicit false

namespace Zkc.Formal

open Zkc.Source Zkc.Core PIR

mutual
  /-- Every operation of a region, nested regions included, passes a test. -/
  def _root_.Zkc.Source.Region.all {dialect : Dialect} (test : dialect.Op → Bool) {Γ out : List dialect.Ty} :
      Region dialect Γ out → Bool
    | .ret _ => true
    | .stop _ => true
    | .letOp op _ bodies next => test op && bodies.all test && next.all test
    | .bind body next => body.all test && next.all test

  def _root_.Zkc.Source.Regions.all {dialect : Dialect} (test : dialect.Op → Bool)
      {signatures : List (List dialect.Ty × List dialect.Ty)} : Regions dialect signatures → Bool
    | .nil => true
    | .cons body tail => body.all test && tail.all test
end

section Regions

variable {M N : Model} (R : Carriers M N) {dialect : Dialect}
  (first : RegionMeaning dialect (Effects M)) (second : RegionMeaning dialect (Effects N))
  (related : ∀ type, first.Value type → second.Value type → Prop)

/-- Two meanings of a nested region are related: on related inputs they are related processes
with related outputs. -/
def FunctionRelated (signature : List dialect.Ty × List dialect.Ty)
    (run : RegionFunction first.Value (Effects M) signature)
    (run' : RegionFunction second.Value (Effects N) signature) : Prop :=
  ∀ values images, ValuesRelated related values images →
    ProcessRelated R (ValuesRelated related) (run values) (run' images)

/-- An operation is compatible: on related operands and related nested regions, its two
meanings are related. -/
def CompatibleAt (op : dialect.Op) : Prop :=
  ∀ (values : Values first.Value (dialect.arguments op))
    (images : Values second.Value (dialect.arguments op)), ValuesRelated related values images →
    ∀ (bodies : Values (RegionFunction first.Value (Effects M)) (dialect.regions op))
      (bodies' : Values (RegionFunction second.Value (Effects N)) (dialect.regions op)),
      ValuesRelated (FunctionRelated R first second related) bodies bodies' →
      ProcessRelated R (ValuesRelated related) (first.operation op values bodies)
        (second.operation op images bodies')

variable {R first second related}

mutual
  /-- The two meanings of a region whose operations are compatible are related. -/
  theorem region_related {test : dialect.Op → Bool}
      (compatible : ∀ op, test op = true → CompatibleAt R first second related op) :
      {Γ out : List dialect.Ty} → (body : Region dialect Γ out) → body.all test = true →
      (env : Environment first.Value Γ) → (env' : Environment second.Value Γ) →
      EnvironmentRelated related env env' →
        ProcessRelated R (ValuesRelated related) (body.denote first env) (body.denote second env')
    | _, _, .ret operands, _, _, _, same => .done (ValuesRelated.operands same operands)
    | _, _, .stop reason, _, _, _, _ => .halt reason
    | _, _, .letOp op operands bodies next, within, env, env', same => by
      simp only [Region.all, Bool.and_eq_true] at within
      exact ProcessRelated.bind
        (compatible op within.1.1 _ _ (ValuesRelated.operands same operands) _ _
          (regions_related compatible bodies within.1.2)) _ _
        fun values images parts =>
          region_related compatible next within.2 _ _
            (EnvironmentRelated.bindAll env env' values images same parts)
    | _, _, .bind body next, within, env, env', same => by
      simp only [Region.all, Bool.and_eq_true] at within
      exact ProcessRelated.bind (region_related compatible body within.1 env env' same) _ _
        fun values images parts =>
          region_related compatible next within.2 _ _
            (EnvironmentRelated.bindAll env env' values images same parts)

  theorem regions_related {test : dialect.Op → Bool}
      (compatible : ∀ op, test op = true → CompatibleAt R first second related op) :
      {signatures : List (List dialect.Ty × List dialect.Ty)} →
      (bodies : Regions dialect signatures) → bodies.all test = true →
        ValuesRelated (FunctionRelated R first second related) (bodies.denote first)
          (bodies.denote second)
    | _, .nil, _ => fun _ position => position.elimNil
    | _, .cons body tail, within => by
      simp only [Regions.all, Bool.and_eq_true] at within
      refine ValuesRelated.cons ?_ (regions_related compatible tail within.2)
      intro values images parts
      exact region_related compatible body within.1 _ _ (EnvironmentRelated.ofValues parts)
end

end Regions

end Zkc.Formal
