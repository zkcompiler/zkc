module

public import ZkcSecurity.Examples.Components.KoalaBearSumcheckRelations

@[expose] public section

/-! The fixed continuation registry refuses wrong nominal ABIs, revisions,
static arguments and absent installations before any proof can select meaning. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace TestsSecurity.KoalaBearSumcheckRelations
open Zkc.Source Zkc.Source.Structured
open ZkcSecurity.Domains.KoalaBearModel (model baseIdentity octicIdentity)
open ZkcSecurity.Domains.KoalaBear (Base Octic embed)
open ZkcSecurity.Examples.Components.KoalaBearSumcheckRelations

example : snapshot.sourceDeclarations.records.length = 1 := by kernel_rfl
example : snapshot.sourceDeclarations.records.map (fun record => (record.resource, record.sealed)) =
    [("linear", true)] := by kernel_rfl
example : registry.check snapshot.relations = true := by decide +kernel
example : (OpaqueRegistry.empty (Value := model.Value)).check snapshot.relations = false := by decide +kernel
example : (registry.resolve { relation with revision := "uninstalled" }).isSome = false := by decide +kernel
example : (registry.resolve { relation with staticArguments := [.field baseIdentity] }).isSome = false := by decide +kernel
example : (registry.resolve { relation with inputs :=
    [.field octicIdentity, .field baseIdentity, .vector octicIdentity, .field octicIdentity] }).isSome = false := by decide +kernel
example : (registry.resolve { relation with purposes :=
    ["statement", "parameter", "parameter", "statement"] }).isSome = false := by decide +kernel

example (a b claim : Base) :
    installed.meanings ⟨1, by decide⟩ (.cons a (.cons b (.cons [] (.cons (embed claim) .nil)))) ↔
      claim = a + b := (meaning a b [] (embed claim)).trans (initial a b claim)
example (a b : Base) (r value : Octic) :
    installed.meanings ⟨1, by decide⟩ (.cons a (.cons b (.cons [r] (.cons value .nil)))) ↔
      value = embed a + (embed b - embed a) * r := (meaning a b [r] value).trans (terminal a b r value)
example (a b : Base) (r s value : Octic) : ¬ residual a b [r, s] value := by
  simp [residual]

#print axioms ZkcSecurity.Examples.Components.KoalaBearSumcheckRelations.meaning
#print axioms ZkcSecurity.Examples.Components.KoalaBearSumcheckRelations.initial
#print axioms ZkcSecurity.Examples.Components.KoalaBearSumcheckRelations.terminal
end TestsSecurity.KoalaBearSumcheckRelations
