module

public import ZkcExamples.Structured.SumcheckArtifacts.ArtifactBindingHelpers
public import ZkcExamples.Structured.OriginalSumcheckProducerCalls

@[expose] public section
set_option autoImplicit false
namespace ZkcExamples.Structured.SumcheckArtifacts.ArtifactRoot
open Zkc.Source Zkc.Source.Structured Zkc.Construction ZkcExamples.Structured

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

/-- The unchanged full validator return contract, shared by generated roots. -/
def ValidatorReturns (context : Zkc.Construction.Context) (booleanRef transcriptRef : Nat)
    (source : Values (Component (assignment F G)) [.boolean] × Original.State (uniformCarriers F G))
    (actual : Domain.Result (uniformCarriers F G)) : Prop :=
  ∃ value : Bool, source.1 = .cons (some value) .nil ∧
    actual.values = [.data (.boolean value), .transcript context.suite source.2.history] ∧
    actual.environment[booleanRef]? = some (.data (.boolean value)) ∧
    actual.environment[transcriptRef]? = some (.transcript context.suite source.2.history) ∧
    source.2.frames = []

/-- The unchanged full producer return contract, including exact frame arity. -/
def ProducerReturns (context : Zkc.Construction.Context) (transcriptRef arity : Nat)
    (source : Values (Component (assignment F G)) [.boolean] × Original.State (uniformCarriers F G))
    (actual : Domain.Result (uniformCarriers F G)) : Prop :=
  source.1 = .cons none .nil ∧
  actual.values = [.transcript context.suite source.2.history] ∧
  actual.environment[transcriptRef]? = some (.transcript context.suite source.2.history) ∧
  actual.environment.length = arity ∧ source.2.frames = []

theorem boolean_and (left right : Bool) :
    Domain.calculate (ringModel F G) .booleanAnd
      [.data (.boolean left), .data (.boolean right)] =
      .returned [.data (.boolean (left && right))] := rfl

end ZkcExamples.Structured.SumcheckArtifacts.ArtifactRoot
