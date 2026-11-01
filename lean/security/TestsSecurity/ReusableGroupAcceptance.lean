import ZkcSecurity.Claims.Methods.SampledReadbackCompleteness
import ZkcSecurity.Bindings.Sigma.SourceExecution
import ZkcExamples.Structured.SchnorrVariants
import ZkcSecurityExamples.Generated.Components.SchnorrRandomizedABI
import ZkcSecurityExamples.Generated.Components.SchnorrAndRandomizedABI
import ZkcExamples.Structured.Generated.Constructed.SchnorrRandomizedProducer
import ZkcExamples.Structured.Generated.Constructed.SchnorrRandomizedValidator
import ZkcExamples.Structured.Generated.Constructed.SchnorrAndRandomizedProducer
import ZkcExamples.Structured.Generated.Constructed.SchnorrAndRandomizedValidator
import ZkcSecurityTools.SigmaReadback
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Module.Prod

/-! Actual randomized artifacts on a bounded heterogeneous module. The retained
source relations supply the mathematical premises. These are honest sampled
acceptance controls, without knowledge or zero-knowledge conclusions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000
noncomputable section
namespace TestsSecurity.ReusableGroupAcceptance
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcSecurity.FiatShamir ZkcSecurity.Claims.HonestPair
open ZkcSecurity.Tools.SigmaReadback
open Zkc.Protocols.Sigma.Source ZkcSecurity.Bindings.Sigma.SourceExecution
open ZkcExamples.Structured.SchnorrVariants.Installations
open ZkcExamples.Structured.Generated.Bindings

abbrev Scalar := ZMod 5
abbrev Group := Scalar × Scalar
abbrev model := ringModel Scalar Group
attribute [local implicit_reducible] relationHelper independentHelper sharedHelper

namespace Single
open ZkcSecurity.Examples.Generated.SchnorrRandomized (subject)
open ZkcSecurity.Examples.Generated.Components.SchnorrRandomizedABI (context_eq)
open ZkcExamples.Structured.Generated.Constructed

/-- Actual private draw, every nonce/challenge, arbitrary reached transcript,
and exact acceptance at the actual validator's Boolean output. -/
theorem acceptance (base point : Group) (witness : Scalar)
    (history : Domain.History model.toCarriers)
    (related : invoke (SchnorrRandomizedInputs.program.payload.definitions.foldl
        (Evaluation.extendMeaningsOn model SiteObservations.closed) [])
      (relationHelper domains randomizedRelation.val)
      (.cons base (.cons point (.cons witness .nil))) = .done (.cons true .nil)) :
    SampledReadback (SampledReadback.Allowed subject)
      (fun _ result => Domain.acceptanceAt 0 result.values = some true)
      (Domain.participant model SchnorrRandomizedInputs.program subject.selection.context
        SchnorrRandomizedProducer.artifact
        [.data ⟨.group domains.group, by decide, base⟩,
         .data ⟨.group domains.group, by decide, point⟩,
         .data ⟨.field domains.scalar, by decide, witness⟩,
         .transcript "merlin3.bls12-381.fr64be/0" history])
      (Domain.participant model SchnorrRandomizedInputs.program subject.selection.context
        SchnorrRandomizedValidator.artifact
        [.data ⟨.group domains.group, by decide, base⟩,
         .data ⟨.group domains.group, by decide, point⟩,
         .transcript "merlin3.bls12-381.fr64be/0" history]) := by
  have mathematical := (relation_accepts_iff domains randomizedRelation.val _
    SchnorrRandomizedInputs.program.payload.linked randomizedRelation.property base point witness).mp related
  subst point
  rw [SchnorrRandomizedProducer.participant_eq, SchnorrRandomizedValidator.participant_eq]
  unfold_component_bodies [SchnorrRandomizedProducer.view, SchnorrRandomizedValidator.view]
  prove_sigma_readback
    normalizing (normalize_sigma_process [context_eq])
    authorizing rfl
    finishing rfl
end Single

namespace Independent
open ZkcSecurity.Examples.Generated.SchnorrAndRandomized (subject)
open ZkcSecurity.Examples.Generated.Components.SchnorrAndRandomizedABI (context_eq)
open ZkcExamples.Structured.Generated.Constructed

/-- The actual source uses two private requests through one allowed port.
No equality between their replies or independent witnesses is assumed. -/
theorem acceptance (firstBase firstPoint secondBase secondPoint : Group)
    (firstWitness secondWitness : Scalar) (history : Domain.History model.toCarriers)
    (related : invoke (SchnorrAndRandomizedInputs.program.payload.definitions.foldl
        (Evaluation.extendMeaningsOn model SiteObservations.closed) [])
      (independentHelper domains randomizedAndRelation.val)
      (.cons firstBase (.cons firstPoint (.cons secondBase (.cons secondPoint
        (.cons firstWitness (.cons secondWitness .nil)))))) = .done (.cons true .nil)) :
    SampledReadback (SampledReadback.Allowed subject)
      (fun _ result => Domain.acceptanceAt 0 result.values = some true)
      (Domain.participant model SchnorrAndRandomizedInputs.program subject.selection.context
        SchnorrAndRandomizedProducer.artifact
        [.data ⟨.group domains.group, by decide, firstBase⟩,
         .data ⟨.group domains.group, by decide, firstPoint⟩,
         .data ⟨.group domains.group, by decide, secondBase⟩,
         .data ⟨.group domains.group, by decide, secondPoint⟩,
         .data ⟨.field domains.scalar, by decide, firstWitness⟩,
         .data ⟨.field domains.scalar, by decide, secondWitness⟩,
         .transcript "merlin3.bls12-381.fr64be/0" history])
      (Domain.participant model SchnorrAndRandomizedInputs.program subject.selection.context
        SchnorrAndRandomizedValidator.artifact
        [.data ⟨.group domains.group, by decide, firstBase⟩,
         .data ⟨.group domains.group, by decide, firstPoint⟩,
         .data ⟨.group domains.group, by decide, secondBase⟩,
         .data ⟨.group domains.group, by decide, secondPoint⟩,
         .transcript "merlin3.bls12-381.fr64be/0" history]) := by
  obtain ⟨firstRelated, secondRelated⟩ := (independent_accepts_iff domains randomizedAndRelation.val _
    SchnorrAndRandomizedInputs.program.payload.linked randomizedAndRelation.property
    firstBase firstPoint secondBase secondPoint firstWitness secondWitness).mp related
  subst firstPoint secondPoint
  rw [SchnorrAndRandomizedProducer.participant_eq, SchnorrAndRandomizedValidator.participant_eq]
  unfold_component_bodies [SchnorrAndRandomizedProducer.view, SchnorrAndRandomizedValidator.view]
  prove_sigma_readback
    normalizing (normalize_sigma_process [context_eq])
    authorizing rfl
    finishing rfl
end Independent

#print axioms Single.acceptance
#print axioms Independent.acceptance
end TestsSecurity.ReusableGroupAcceptance
