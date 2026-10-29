import Tests.MultilinearReferences
import ZkcExamples.Structured.SumcheckReferenceInstallation
import ZkcExamples.Structured.Generated.Bindings.SmallSumcheckCallbacks
import ZkcExamples.Structured.Generated.Bindings.TwoSumsCallbacks

set_option autoImplicit false
namespace Tests.SumcheckMathematicalInstallation
open Zkc.Source Zkc.Source.Structured NormalForm
open ZkcExamples.Structured
open Tests.MultilinearReferences
open Generated.Bindings

/-- This is the charged source/body selection. No semantic equation is authored
for either source; both use the same library and normal-form certificates. -/
noncomputable def callback : RetainedSource →
    Region protocolDialect
      (.index :: (SumcheckVerifierBodies.repeatState ++ [.service "random.bls12-381.fr/0"]))
      SumcheckVerifierBodies.repeatState
  | .small => SmallSumcheckCallbacks.protocol0Role1Callback0Body
  | .twoSums => TwoSumsCallbacks.protocol0Role1Callback0Body

theorem callback_selected (selected : RetainedSource) :
    callback selected = SumcheckVerifierBodies.roundBody := by
  cases selected <;> kernel_rfl

noncomputable def producerCallback : RetainedSource →
    Region protocolDialect
      (.index :: (SumcheckVerifierBodies.repeatState ++ [.service "random.bls12-381.fr/0"]))
      SumcheckVerifierBodies.repeatState
  | .small => SmallSumcheckCallbacks.protocol0Role0Callback0Body
  | .twoSums => TwoSumsCallbacks.protocol0Role0Callback0Body

theorem producerCallback_selected (selected : RetainedSource) :
    producerCallback selected = SumcheckVerifierBodies.roundBody := by
  cases selected <;> kernel_rfl

theorem bodies (selected : RetainedSource) :
    SumcheckReferenceInstallation.Bodies (source selected).payload.definitions bindings := by
  refine ⟨Tests.MultilinearReferences.bodies selected, ?_⟩
  cases selected <;> bind_structured_bodies

variable (model : DomainModel) (selected : RetainedSource)

theorem actual_round (ctx : ProtocolContext) (distinct : RosterDistinct ctx 1 2)
    (index : Nat) (point : Option (List (model.Field "bls12-381.fr")))
    (claim : Option (model.Field "bls12-381.fr")) (service : Option Nat) :
    (callback selected).denote
      (participantMeaningWithOn model (.silent _) Occurrence.actions
        (SumcheckReferenceInstallation.tables model (source selected).payload.definitions)
        (ctx.roles 1) (Occurrence.table model (source selected).payload) ctx Occurrence.iterations)
      (SumcheckReferenceInstallation.Syntax.pattern.environment model
        (SumcheckReferenceInstallation.inputs model index point claim service)).get =
      SumcheckReferenceInstallation.reference model ctx service point claim := by
  rw [callback_selected]
  exact SumcheckReferenceInstallation.body_reference model _ (source selected).payload.linked
    (bodies selected) _ ctx distinct index point claim service

theorem actual_producer (ctx : ProtocolContext) (distinct : RosterDistinct ctx 0 2)
    (index : Nat) (xs : List (model.Field "bls12-381.fr")) (n w : Nat)
    (point : List (model.Field "bls12-381.fr")) (service : Option Nat)
    (bound : xs.length < indexLimit) (small : n < 64) (width : 0 < w)
    (shape : xs.length = 2^n*w) (positive : 0 < n) :
    (producerCallback selected).denote
      (participantMeaningWithOn model (.silent _) Occurrence.actions
        (SumcheckReferenceInstallation.tables model (source selected).payload.definitions)
        (ctx.roles 0) (Occurrence.table model (source selected).payload) ctx Occurrence.iterations)
      (SumcheckReferenceInstallation.Prover.pattern.environment model
        (SumcheckReferenceInstallation.Prover.inputs model index xs n w point service)).get =
      SumcheckReferenceInstallation.Prover.reference model ctx xs n w point := by
  rw [producerCallback_selected]
  exact SumcheckReferenceInstallation.Prover.body_reference model _
    (source selected).payload.linked (bodies selected) _ ctx distinct index xs n w point service
    bound small width shape positive

/-- Missing bounds/shape cannot be manufactured by selecting the actual source. -/
example (_xs : List (model.Field "bls12-381.fr")) (_n _w : Nat)
    (_r : model.Field "bls12-381.fr") : True := by
  fail_if_success
    have : invoke (ReferenceLibrary.Multilinear.closed model
        (definitions := (source selected).payload.definitions))
        (ReferenceLibrary.Multilinear.firstHelper "bls12-381.fr" bindings)
        (.cons _xs (.cons _n (.cons _w (.cons _r .nil)))) =
        primitiveOutcome (ReferenceLibrary.Multilinear.firstOutcome model "bls12-381.fr"
          (.cons _xs (.cons _n (.cons _w (.cons _r .nil))))) := by
      solve | exact actual_restriction model selected _xs _n _w _r
  trivial

/-- Changing a captured dependency breaks exact template association. -/
example : True := by
  fail_if_success
    have : BodyIn (source .small).payload.definitions
        (ReferenceLibrary.Multilinear.firstHelper "bls12-381.fr" bindings)
        (MultilinearBodies.firstBody "bls12-381.fr" {bindings with collection := "changed_collection"}) := by
      bind_structured_bodies
  trivial

/-- Matching the helper's name and ABI cannot install a changed body. -/
example : True := by
  fail_if_success
    have : BodyIn (source .small).payload.definitions
        (ReferenceLibrary.Multilinear.firstHelper "bls12-381.fr" bindings)
        (.ret (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil)))) := by
      bind_structured_bodies
  trivial

#print axioms actual_round
#print axioms actual_producer
#print axioms bodies
#print axioms SumcheckReferenceInstallation.Prover.laws
#print axioms ReferenceLibrary.forward
end Tests.SumcheckMathematicalInstallation
