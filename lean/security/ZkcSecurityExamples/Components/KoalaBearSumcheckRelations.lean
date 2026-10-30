module

public import ZkcSecurityExamples.Components.KoalaBearSumcheckGenerated.Data
public import ZkcSecurity.Bindings.Models.KoalaBearModel
public import Zkc.Source.KernelRfl
public import Zkc.Source.Structured.OpaqueRegistry
public import Zkc.Polynomial.Multilinear.Embedding

@[expose] public section

/-! An ordinary library installation fixes the linear continuation's meaning.
The source identity and complete nominal ABI select this predicate before any
component evidence is supplied. -/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000
noncomputable section
namespace ZkcSecurity.Examples.Components.KoalaBearSumcheckRelations
open Zkc.Source Zkc.Source.Structured
open ZkcSecurity.Domains.KoalaBearModel (model baseIdentity octicIdentity)
open ZkcSecurity.Domains.KoalaBear (Base Octic embed)
open Zkc.Polynomial.Multilinear
abbrev snapshot := KoalaBearSumcheckGenerated.Data.snapshot

def residual (a b : Base) (point : List Octic) (value : Octic) : Prop :=
  point.length ≤ 1 ∧ value = (restrictPrefixValues ([a, b].map embed) point).sum

def residualInstance : OpaqueInstance model.Value where
  inputs := [.field baseIdentity, .field baseIdentity, .vector octicIdentity, .field octicIdentity]
  purposes := ["parameter", "parameter", "statement", "statement"]
  holds arguments := residual (arguments.get .here) (arguments.get (.there .here))
    (arguments.get (.there (.there .here))) (arguments.get (.there (.there (.there .here))))

def registry : OpaqueRegistry model.Value where
  families := [⟨⟨"mixed-sumcheck.residual/0", "koala-bear-octic", "0"⟩,
    fun arguments => if arguments.isEmpty then some residualInstance else none⟩]
  unique := by simp

def installed : RegisteredRelations model.Value snapshot.relations :=
  .ofChecked registry (by decide +kernel)

abbrev relation : Relation := snapshot.relations.get ⟨1, by decide⟩

def binding : OpaqueRegistry.Binding registry relation where
  instantiation := residualInstance
  selected := by kernel_rfl
  inputs := by kernel_rfl
  outputs := by kernel_rfl
  purposes := by kernel_rfl
  opaqueKind := by kernel_rfl
  noFormula := by kernel_rfl

theorem meaning (a b : Base) (point : List Octic) (value : Octic) :
    installed.meanings ⟨1, by decide⟩ (.cons a (.cons b (.cons point (.cons value .nil)))) ↔
      residual a b point value :=
  installed.meanings_exact _ binding _

theorem initial (a b claim : Base) :
    residual a b [] (embed claim) ↔ claim = a + b := by
  simp only [residual, List.length_nil, Nat.zero_le, true_and,
    restrictPrefixValues_nil, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [← map_add]
  exact embed.injective.eq_iff

theorem terminal (a b : Base) (point value : Octic) :
    residual a b [point] value ↔ value = embed a + (embed b - embed a) * point := by
  simp [residual, restrictPrefixValues, restrictValues]

end KoalaBearSumcheckRelations
end ZkcSecurity.Examples.Components
