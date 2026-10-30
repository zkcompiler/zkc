module

public import Zkc.Source.Structured.Bindings.Template
public import ZkcExamples.Construction.EmbeddingEqualityBinding
public import ZkcExamples.Structured.GkrSourceViews
public import ZkcSecurity.Bindings.Models.KoalaBearModel
public import ZkcSecurityExamples.EmbeddingEqualityCapabilities
public import ZkcSecurity.Bindings.Models.PrimeField
public import Mathlib.Tactic.FinCases

@[expose] public section

/-! Installed mathematics for fresh generator clients. The mixed helper law is
about the complete admitted table, not a name-based replacement. -/
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
noncomputable section
namespace TestsSecurity.ParametricBindings
open Zkc.Source Zkc.Source.Structured Zkc.Source.Structured.NormalForm Zkc.Source.Structured.Bindings

namespace Mixed
open ZkcSecurity.Domains.KoalaBearModel
open ZkcExamples.Construction.EmbeddingEqualityBodies
abbrev program := ZkcExamples.Construction.EmbeddingEqualityBinding.program

def signature : Signature := ⟨[⟨embeddingHelper, .returns [], []⟩], false, true, [], []⟩

def tables : Tables model :=
  program.payload.definitions.foldl (Evaluation.ComponentTablesOn.extend model (.silent _)) ⟨[], []⟩

def results : LawResults model signature.laws where
  result := Fin.cases
    (fun args => .cons (model.embed octicIdentity baseIdentity (args.get .here)) .nil)
    (fun entry => entry.elim0)

/-- Correct dependent signature, deliberately incorrect mathematics. -/
def wrongResults : LawResults model signature.laws where
  result := Fin.cases (fun _ => .cons 0 .nil) (fun entry => entry.elim0)

theorem helperLaws {inputs : List Ty} (input : Values (Component model.Value) inputs) :
    LawsHold tables results input := by
  intro entry
  fin_cases entry
  intro args _ values same
  cases args with
  | cons a args =>
    cases args
    change some (.cons (model.embed octicIdentity baseIdentity a) .nil) = some values at same
    cases same
    rfl

theorem fieldLaw : IsField (model.Field octicIdentity) := laws.field octicIdentity (by decide)

theorem modelLaws : DomainLaws program.snapshot.catalogue model :=
  ZkcSecurity.Examples.EmbeddingEqualityCapabilities.algebra

example : @Fintype.card (model.Field baseIdentity) (fintype baseIdentity (by decide)) =
    ZkcSecurity.Domains.KoalaBear.q := card_base
example : @Fintype.card (model.Field octicIdentity) (fintype octicIdentity (by decide)) =
    ZkcSecurity.Domains.KoalaBear.q ^ 8 := card_octic
example : Function.Injective (model.embed octicIdentity baseIdentity) := embed_injective

/-- The helper's result has the octic carrier; base-field substitution is a
separate type and cannot instantiate this law or the generated template. -/
theorem result_exact (a : model.Field baseIdentity) :
    results.result ⟨0, by decide⟩ (.cons a .nil) =
      .cons (ZkcSecurity.Domains.KoalaBear.embed a) .nil := rfl
end Mixed

namespace Gates
abbrev program := ZkcExamples.Structured.GkrSourceViews.program
abbrev model := ZkcSecurity.Domains.PrimeField.blsScalarModel

def signature : Signature := ⟨[], false, true, program.payload.definitions.map (·.helper), []⟩
theorem modelLaws : DomainLaws program.snapshot.catalogue model :=
  ringModel_laws (ZMod blsModulus) (ZMod blsModulus) program.snapshot.catalogue
end Gates
end TestsSecurity.ParametricBindings
