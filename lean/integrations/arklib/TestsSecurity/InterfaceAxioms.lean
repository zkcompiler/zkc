import ZkcSecurity.Stage.Joint
import ZkcSecurity.HashChain.Instance
import ZkcSecurity.HashChain.Bytes
import Zkc.Construction.Compiled
import ZkcSecurity.FiatShamir.Budget
import ZkcSecurity.FiatShamir.Reduction
import ZkcSecurity.FiatShamir.Binding
import ZkcSecurity.Examples.FriFiatShamir
import ZkcSecurity.Examples.CommittedFri

/-! Axiom closures of the shared interfaces: the core transcript interface, the keyed endpoint and
its transformers, charged reductions, path bounds, stage relations, the verdict transport lemma,
the transport between oracle key forms, the charged commitment bridge and the theorems restated
through them. Every closure is within `propext`, `Classical.choice` and `Quot.sound`. -/

#print axioms Zkc.Transcript.transform_mapRaw
#print axioms Zkc.Transcript.transform_bind_done
#print axioms Zkc.Transcript.replay_append
#print axioms Zkc.Transcript.replay_congr
#print axioms Zkc.Transcript.AcceptedComplete.accepted
#print axioms Zkc.Transcript.Walk.Bound.bind
#print axioms Zkc.Transcript.Walk.Bound.repeatN
#print axioms Zkc.Transcript.Walk.Bound.convert
#print axioms Zkc.Construction.transform_eq_transcript
#print axioms Zkc.Construction.compiled_transform

#print axioms ZkcSecurity.FiatShamir.KeyedCertificate.soundness
#print axioms ZkcSecurity.FiatShamir.KeyedCertificate.soundness_mixture
#print axioms ZkcSecurity.FiatShamir.Typed.ChargedCertificate.keyed
#print axioms ZkcSecurity.FiatShamir.Typed.ChargedCertificate.keyedFixed
#print axioms ZkcSecurity.FiatShamir.Typed.adaptive_soundness_charged
#print axioms ZkcSecurity.FiatShamir.Typed.adaptive_soundness
#print axioms ZkcSecurity.FiatShamir.Typed.soundness
#print axioms ZkcSecurity.FiatShamir.Typed.randomized_adaptive_soundness_charged
#print axioms ZkcSecurity.FiatShamir.Typed.evalWithAnswerFn_transform
#print axioms ZkcSecurity.FiatShamir.Typed.transform_chargedCostBound

#print axioms ZkcSecurity.FiatShamir.Typed.Reduction.bind
#print axioms ZkcSecurity.FiatShamir.Typed.Reduction.repeatN
#print axioms ZkcSecurity.FiatShamir.Typed.Reduction.receive
#print axioms ZkcSecurity.FiatShamir.Typed.Reduction.toCertificate
#print axioms ZkcSecurity.FiatShamir.Typed.UniformEventStep.typed
#print axioms ZkcSecurity.FiatShamir.Typed.UniformCertificate.charged

#print axioms ZkcSecurity.FiatShamir.Typed.queryBound_iff
#print axioms ZkcSecurity.FiatShamir.Typed.costBound_iff
#print axioms ZkcSecurity.FiatShamir.Typed.chargedCostBound_iff
#print axioms ZkcSecurity.FiatShamir.Typed.QueryBound.chargedCostBound_of_walk
#print axioms ZkcSecurity.HashChain.callBound_iff
#print axioms ZkcSecurity.Commitment.charged_iff
#print axioms ZkcSecurity.Commitment.commitBound_iff

#print axioms ZkcSecurity.Stage.Relation.comp
#print axioms ZkcSecurity.Stage.Relation.comp_assoc
#print axioms ZkcSecurity.Stage.Relation.transfer
#print axioms ZkcSecurity.Stage.Relation.bounded
#print axioms ZkcSecurity.Stage.Relation.ofPrunesImage
#print axioms ZkcSecurity.Stage.chargedRelation
#print axioms ZkcSecurity.FiatShamir.Provider.Simulation.toRelation
#print axioms ZkcSecurity.VCVio.Pruning.prEvent_le_of_prunes_image
#print axioms ZkcSecurity.VCVio.Pruning.prEvent_le_of_image

#print axioms ZkcSecurity.Oracle.Renaming.evalSPMF_translate
#print axioms ZkcSecurity.Oracle.Renaming.translate_costBound
#print axioms ZkcSecurity.Oracle.historyToPair_weight

#print axioms ZkcSecurity.Commitment.keyed
#print axioms ZkcSecurity.Commitment.soundness_charged
#print axioms ZkcSecurity.Commitment.soundness_weighted
#print axioms ZkcSecurity.Commitment.soundness

#print axioms ZkcSecurity.HashChain.concrete_soundness_charged
#print axioms ZkcSecurity.HashChain.concrete_soundness
#print axioms ZkcSecurity.HashChain.byte_soundness
#print axioms ZkcSecurity.Examples.FriFiatShamir.typedStep
#print axioms ZkcSecurity.Examples.CommittedFri.soundness
