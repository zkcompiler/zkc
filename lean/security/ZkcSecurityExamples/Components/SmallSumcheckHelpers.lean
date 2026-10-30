module

public import ZkcSecurity.Bindings.Sumcheck.DomainHelpers
public import Zkc.Protocols.Sumcheck.Source.DomainHelpers
public import Zkc.Source.Structured.BodyBindings
public import ZkcExamples.Structured.Generated.Bindings.SmallSumcheckInputs
public import ZkcExamples.Structured.OriginalSumcheckTerminal

@[expose] public section

/-! Closed arithmetic evidence for the actual SmallSumcheck helper table.
This is author mathematical library evidence, not generated Subject assembly.
-/

set_option autoImplicit false
namespace ZkcSecurity.Examples.Components.SmallSumcheck
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcExamples.Structured
open ZkcSecurity.Families.Sumcheck.TableComponent

theorem helper_bodies : ZkcExamples.Structured.SumcheckArtifacts.DomainHelpers.Bodies Generated.Bindings.SmallSumcheckInputs.imported.program :=
  ⟨OriginalSumcheckInstances.Small.producer_bodies, OriginalSumcheckInstances.Small.terminal_bodies⟩

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

/-- Exact nominal terminal equation, including false scalar claims. -/
theorem call_check (raw point : List F) (claim : F)
    (rawBound : raw.length < indexLimit) (pointBound : point.length < indexLimit) :
    Domain.callHelper (ringModel F G) Generated.Bindings.SmallSumcheckInputs.imported.program
      SumcheckHelperBodies.checkHelper.name [.data .boolean]
      [.data (.vector "bls12-381.fr" raw), .data (.vector "bls12-381.fr" point),
        .data (.field "bls12-381.fr" claim)] =
      .returned [.data (.boolean (decide (PrimitiveLibrary.HasShape raw point.length 1 ∧
        (Zkc.Polynomial.Multilinear.restrictPrefixValues raw point).sum = claim)))] :=
  ZkcExamples.Structured.SumcheckArtifacts.DomainHelpers.check _ helper_bodies.terminal
    raw point claim rawBound pointBound

end ZkcSecurity.Examples.Components.SmallSumcheck
