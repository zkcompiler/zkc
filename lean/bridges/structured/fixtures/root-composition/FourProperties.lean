module
public import TestsSecurity.RootComposition.FourSource
public import ZkcExamples.Structured.Generated.Connections.FourSums
public import ZkcSecurity.Bindings.Source.PairRouting
public import ZkcSecurity.Bindings.Sumcheck.SourceFamilyComposition
public import ZkcSecurity.Bindings.Sumcheck.SourceFamilyPublic
public meta import ZkcSecurityTools.SourceProperties.Assembly
@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace TestsSecurity.RootComposition.Four.Source
open Zkc.Source Zkc.Source.Structured NormalForm
open ZkcExamples.Structured
open ZkcSecurity.Families.Sumcheck ZkcSecurity.Realizations.Sumcheck
variable (model : DomainModel)
def validatorReference (args : Binders model (Zkc.Source.Structured.NormalizedRoot.pattern program 1).scope) :=
  source_composition (Zkc.Source.Structured.NormalizedRoot.process validator model args
    (SourceFamily.validatorResults installation model) (SourceFamily.validatorCallees installation model))
  components [fun site raw scalar count service => SourceFamily.one installation model {} site raw scalar count service]
  atoms [Participant.owned, invoke, SumcheckReductionReference.reference]

theorem validator_reference (args : Binders model (Zkc.Source.Structured.NormalizedRoot.pattern program 1).scope) :
    Occurrence.participant model program 1 (Zkc.Source.Structured.NormalizedRoot.inputs model args) =
      validatorReference model args := by
  rw [SourceFamily.validator_equation installation model validator]
  source_composition_equation atoms [Participant.owned, invoke, SumcheckReductionReference.reference]

variable [fieldLaw : Fact (IsField (model.Field SumcheckReferenceInstallation.field))]
local instance : Field (model.Field SumcheckReferenceInstallation.field) := fieldLaw.out.toField
open Zkc.Transcript Zkc.Obligations ZkcSecurity.Source ZkcSecurity.FiatShamir
open SumcheckReferenceInstallation

def arguments (a b c d : List (model.Field field)) (sa sb sc sd : model.Field field)
    (count service : Nat) : Binders model (Zkc.Source.Structured.NormalizedRoot.pattern program 1).scope :=
  .cons (some a) (.cons (some b) (.cons (some c) (.cons (some d)
    (.cons (some sa) (.cons (some sb) (.cons (some sc) (.cons (some sd)
      (.cons (some count) (.cons (some service) .nil)))))))))

variable [samples : ∀ event : Zkc.Construction.Domain.Event model.toCarriers,
  SampleableType (Zkc.Construction.Domain.Raw event)]
  (price : ENNReal)
  (sampling : ∀ (origin : Zkc.Construction.Origin)
    (request : origin.request = some (.draw field)) (p q : Polynomial (model.Field field)),
    p ≠ q → p.natDegree ≤ 1 → q.natDegree ≤ 1 →
    Pr{let raw ← $ᵗ (Zkc.Construction.Domain.Raw (.challenge origin : Zkc.Construction.Domain.Event model.toCarriers))}[
      p.eval (Zkc.Construction.Original.fieldReply origin field request raw) =
        q.eval (Zkc.Construction.Original.fieldReply origin field request raw)] ≤ price)

omit fieldLaw samples in
theorem both (x y : Option Bool) :
    invoke (Occurrence.helpers model program.payload).components SourceFamily.conjunctionHelper
      (.cons x (.cons y .nil)) = .done (.cons (SourceFamily.optionalAnd x y) .nil) :=
  SourceFamily.conjunction_equation model (by bind_structured_bodies) x y

def rejected (a b c d : List (model.Field field)) (sa sb sc sd : model.Field field)
    (count service : Nat)
    (wrong : ¬(count ≤ installation.maximum ∧ a.length = 2^count ∧ b.length = 2^count ∧
      c.length = 2^count ∧ d.length = 2^count ∧ sa = a.sum ∧ sb = b.sum ∧ sc = c.sum ∧ sd = d.sum))
    (history : List (PublicProperties.Event model.toCarriers)) :
    Derivation PublicProperties.interface (PublicProperties.escape price)
      (fun _ out => out = (.cons (some false) .nil : Values (Component model.Value) [.boolean])) history
      (Occurrence.participant model program 1
        (Zkc.Source.Structured.NormalizedRoot.inputs model (arguments model a b c d sa sb sc sd count service))) := by
  rw [validator_reference]
  dsimp only [validatorReference]
  exact source_property "normalized conjunction rejection" companions [] via by
    assemble_source_no
      [fun site raw rounds handle scalar history => SourceFamily.one_summary model installation
        site raw rounds handle scalar PublicProperties.interface (PublicProperties.escape price)
        (SourceFamilyPublic.escape_empty model price)
        (SourceFamilyPublic.no_steps model price sampling installation site handle raw) history]
      simplifying [both model, SourceFamily.optionalAnd, PropertyAssembly.done_bind,
        Option.bind, Option.map, Option.some.injEq, Values.cons.injEq, Bool.and_eq_true, Bool.eq_false_iff]

theorem maximum_eq : installation.maximum = 4 := rfl

omit samples in
theorem costs (a b c d : List (model.Field field)) (sa sb sc sd : model.Field field)
    (count service : Nat) (history : List (PublicProperties.Event model.toCarriers)) :
    Typed.ChargedCostBound PublicProperties.interface (fun _ _ => price)
      (Occurrence.participant model program 1
        (Zkc.Source.Structured.NormalizedRoot.inputs model (arguments model a b c d sa sb sc sd count service)))
      history (16 • price) := by
  rw [validator_reference]
  dsimp only [validatorReference]
  exact source_property "normalized conjunction cost" companions [] via by
    assemble_source_cost
      [fun site raw rounds handle scalar history => SourceFamily.one_cost model installation
        site raw rounds handle scalar PublicProperties.interface (fun _ _ => price)
        (SourceFamilyPublic.cuts model (SourceFamily.context site) handle)
        (SourceFamilyPublic.boundaries model (SourceFamily.context site)) price (fun _ => le_rfl) history]
      simplifying [both model, SourceFamily.optionalAnd, PropertyAssembly.done_bind, maximum_eq]

omit fieldLaw in
def producerArguments (a b c d : List (model.Field field)) (count : Nat) :
    Binders model (Zkc.Source.Structured.NormalizedRoot.pattern program 0).scope :=
  .cons (some a) (.cons (some b) (.cons (some c) (.cons (some d) (.cons (some count) .nil))))

def producerReference (a b c d : List (model.Field field)) (count : Nat) :=
  source_composition (Zkc.Source.Structured.NormalizedRoot.process producer model
    (producerArguments model a b c d count)
    (SourceFamily.producerResults installation model) (SourceFamily.producerCallees installation model))
  components [fun site raw rounds => SourceFamily.producerOne installation model site raw rounds]
  atoms [Participant.owned, invoke, SourceFamily.producerReduction]

omit fieldLaw samples in
theorem producer_reference (a b c d : List (model.Field field)) (count : Nat) :
    Occurrence.participant model program 0
      (Zkc.Source.Structured.NormalizedRoot.inputs model (producerArguments model a b c d count)) =
      producerReference model a b c d count := by
  rw [SourceFamily.producer_equation installation model producer]
  source_composition_equation atoms [Participant.owned, invoke, SourceFamily.producerReduction]

omit samples in
theorem paired (a b c d : List (model.Field field)) (sa sb sc sd : model.Field field) (count service : Nat)
    (shapeA : a.length = 2^count) (shapeB : b.length = 2^count)
    (shapeC : c.length = 2^count) (shapeD : d.length = 2^count)
    (bounded : count ≤ installation.maximum)
    (finiteA : a.length < indexLimit) (finiteB : b.length < indexLimit)
    (finiteC : c.length < indexLimit) (finiteD : d.length < indexLimit)
    (honest : sa = a.sum ∧ sb = b.sum ∧ sc = c.sum ∧ sd = d.sum) :
    Pair (PairScope.ofContext ZkcExamples.Structured.Generated.Connections.FourSums.context)
      (fun _ v => v = (.cons (some true) .nil : Values (Component model.Value) [.boolean]))
      (Occurrence.participant model program 0
        (Zkc.Source.Structured.NormalizedRoot.inputs model (producerArguments model a b c d count)))
      (Occurrence.participant model program 1
        (Zkc.Source.Structured.NormalizedRoot.inputs model (arguments model a b c d sa sb sc sd count service))) := by
  obtain ⟨ha, hb, hc, hd⟩ := honest
  rw [producer_reference, validator_reference]
  dsimp only [producerReference, validatorReference]
  exact source_property "normalized honest composition" companions [] via by
    assemble_source_pairs
      [SourceFamily.pair_contract model installation
        (PairScope.ofContext ZkcExamples.Structured.Generated.Connections.FourSums.context) ⟨rfl, rfl⟩]
      simplifying [both model, SourceFamily.optionalAnd, PropertyAssembly.done_bind,
        Option.bind, Option.map, Bool.and_true, Bool.true_and]

#print axioms rejected
#print axioms costs
#print axioms paired
end TestsSecurity.RootComposition.Four.Source
