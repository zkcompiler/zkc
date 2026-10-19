import ZkcSecurity.Stage.Joint
import ZkcSecurity.HashChain.Instance
import ZkcSecurity.HashChain.Bytes
import ZkcSecurity.FiatShamir.Budget
import ZkcSecurity.FiatShamir.Reduction
import ZkcSecurity.FiatShamir.Binding
import ZkcTools.DeclarationAudit

/-! Axiom closures and dependency rules of the shared interfaces: the core transcript interface
and path bounds, the keyed endpoint and its transformers, charged reductions, the lifting of law
interfaces, stage relations, the verdict transport lemma, the transport between oracle key forms,
binding, the charged commitment bridge and the hash chain restated through them. Every
declaration of these modules passes the declaration audit. -/

run_cmd do
  ZkcTools.DeclarationAudit.check
    [`Zkc.Transcript, `ZkcSecurity.FiatShamir.Interface, `ZkcSecurity.FiatShamir.Typed,
     `ZkcSecurity.FiatShamir.Keyed, `ZkcSecurity.FiatShamir.Reduction,
     `ZkcSecurity.FiatShamir.Budget, `ZkcSecurity.FiatShamir.Lifting,
     `ZkcSecurity.FiatShamir.Binding, `ZkcSecurity.Stage, `ZkcSecurity.Oracle,
     `ZkcSecurity.VCVio.Pruning, `ZkcSecurity.Commitment, `ZkcSecurity.HashChain]
    "SHARED-INTERFACES-AUDIT-PASS"
