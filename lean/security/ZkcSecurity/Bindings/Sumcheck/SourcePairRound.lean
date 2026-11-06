module

public import ZkcSecurity.Bindings.Sumcheck.SourceIteration
public import ZkcSecurity.Bindings.Source.Pair

@[expose] public section

/-! The actual producer and validator callbacks satisfy one shared round law.
All local mathematics is installed by exact typed body association. The pair
residual retains both complete source rows and the arbitrary caller frame.
-/
set_option autoImplicit false
noncomputable section
namespace ZkcSecurity.Realizations.Sumcheck.SourcePair
open ZkcSecurity.Families.Sumcheck ZkcSecurity.Realizations.Sumcheck
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcExamples.Structured SumcheckReferenceInstallation TableComponent
open ZkcSecurity.Source

variable {foldNames : MultilinearBodies.FoldNames}
variable (model : DomainModel) [fieldLaw : Fact (IsField (model.Field field))]
local instance : Field (model.Field field) := fieldLaw.out.toField
variable {Frame : Type}

abbrev endpoints {n : Nat} (state : PrefixState (model.Field field) Frame (n+1)) :=
  Zkc.Protocols.Sumcheck.Multilinear.endpoints state.entries

/-- The same representation used by No supplies honest preservation. This is
an algebraic law for every challenge, independent of any sampling distribution. -/
theorem advance_honest {n : Nat} (state : PrefixState (model.Field field) Frame (n+1))
    (challenge : model.Field field) :
    (state.advance (endpoints model state) challenge).scalar =
      (state.advance (endpoints model state) challenge).entries.sum := by
  change (1-challenge) * (endpoints model state).1 + challenge * (endpoints model state).2 = _
  rw [PrefixState.advance_entries]
  exact ((SourceIteration.restriction model state).round_sum challenge).symm

/-- Source callback pairing requires both role projections, the actual table
shape and producer arithmetic bounds. No validator handler is postulated. -/
theorem round {n : Nat} (definitions : List CheckedDefinition)
    (linked : DeclarationsLinked [] definitions)
    (bodies : Bodies definitions (MultilinearSourceBindings.sumcheckFor foldNames))
    (protocols : ProtocolTable model.Value (Occurrence.signature model.toCarriers))
    (ctx : ProtocolContext) (distinctP : NormalForm.RosterDistinct ctx 0 2)
    (distinctV : NormalForm.RosterDistinct ctx 1 2)
    (scope : PairScope)
    (roles : ctx.roles 0 = scope.producer ∧ ctx.roles 1 = scope.validator)
    (delivery : (SumcheckRoundNormalForms.challengeSite ctx,
      SumcheckRoundNormalForms.deliverySite ctx) ∈ scope.deliveries)
    (index handle : Nat) (state : PrefixState (model.Field field) Frame (n+1))
    (bounded : state.entries.length < indexLimit) (small : n+1 < 64)
    (honest : state.scalar = state.entries.sum) :
    Pair scope (fun p v => ∃ challenge : model.Field field,
      p = Prover.state model (state.advance (endpoints model state) challenge).entries n 1
        (state.advance (endpoints model state) challenge).point ∧
      v = SumcheckReferenceInstallation.state model
        (some (state.advance (endpoints model state) challenge).point)
        (some (state.advance (endpoints model state) challenge).scalar))
      (SumcheckVerifierBodies.roundBody.denote
        (participantMeaningWithOn model (.silent _) Occurrence.actions (tables model definitions)
          (ctx.roles 0) protocols ctx Occurrence.iterations)
        (Prover.pattern.environment model
          (Prover.inputs model index state.entries (n+1) 1 state.point none)).get)
      (SumcheckVerifierBodies.roundBody.denote
        (participantMeaningWithOn model (.silent _) Occurrence.actions (tables model definitions)
          (ctx.roles 1) protocols ctx Occurrence.iterations)
        (Syntax.pattern.environment model
          (inputs model index (some state.point) (some state.scalar) (some handle))).get) := by
  rw [Prover.body_reference model definitions linked bodies protocols ctx distinctP index
    state.entries (n+1) 1 state.point none bounded small (by decide)
    (by simpa using state.entries_shape) (by omega)]
  rw [body_reference model definitions linked bodies protocols ctx distinctV index]
  have boundary : state.scalar = (endpoints model state).1 + (endpoints model state).2 := by
    exact honest.trans (Zkc.Protocols.Sumcheck.Multilinear.endpoints_sum state.entries).symm
  dsimp only [endpoints, Zkc.Protocols.Sumcheck.Multilinear.endpoints] at boundary
  change Pair scope _ (PIR.Process.call _ _) (PIR.Process.call _ _)
  apply Pair.message (.field field) _ _ _ _ rfl roles
  apply Pair.message (.field field) _ _ _ _ rfl roles
  simp only [boundary, Zkc.Protocols.Sumcheck.Multilinear.endpoints, ↓reduceIte]
  apply Pair.challenge field _ _ _ _ _ roles delivery
  intro challenge
  apply Pair.done
  exact ⟨challenge, by rw [PrefixState.advance_entries]; rfl, rfl⟩

#print axioms round
end ZkcSecurity.Realizations.Sumcheck.SourcePair
