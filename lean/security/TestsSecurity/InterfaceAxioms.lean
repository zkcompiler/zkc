import ZkcSecurity.Transformations.Stages.Joint
import ZkcSecurity.Transformations.HashChain.Instance
import ZkcSecurity.Transformations.HashChain.Bytes
import ZkcSecurity.ProgramLogic.Transcript.Budget
import ZkcSecurity.ProgramLogic.Transcript.Reduction
import ZkcSecurity.Transformations.FiatShamir.Binding
import ZkcSecurity.Transformations.Commitment.HistoryKeys
import ZkcSecurity.Transformations.Commitment.Repeats
import ZkcTools.DeclarationAudit

/-! Axiom closures and dependency rules of the shared interfaces: the core transcript interface
and path bounds, the keyed endpoint and its transformers, charged reductions, the lifting of law
interfaces, stage relations, the verdict transport lemma, the transport between oracle key forms,
binding, the charged commitment bridge and the hash chain restated through them. Every
declaration of these modules passes the declaration audit. -/

run_cmd do
  ZkcTools.DeclarationAudit.check
    [`Zkc.Transcript, `ZkcSecurity.ProgramLogic.Transcript.Interface, `ZkcSecurity.ProgramLogic.Transcript.Typed,
     `ZkcSecurity.ProgramLogic.Transcript.Keyed, `ZkcSecurity.ProgramLogic.Transcript.Reduction,
     `ZkcSecurity.ProgramLogic.Transcript.Budget, `ZkcSecurity.ProgramLogic.Transcript.Lifting,
     `ZkcSecurity.Transformations.FiatShamir.Binding, `ZkcSecurity.Transformations.Stages, `ZkcSecurity.ProgramLogic.Games, `ZkcSecurity.Mathematics.Oracle, `ZkcSecurity.Transformations.Oracle,
     `ZkcSecurity.Mathematics.Oracle.Pruning, `ZkcSecurity.Mathematics.Oracle.Memo, `ZkcSecurity.Transformations.Commitment,
     `ZkcSecurity.Transformations.HashChain]
    "SHARED-INTERFACES-AUDIT-PASS"
