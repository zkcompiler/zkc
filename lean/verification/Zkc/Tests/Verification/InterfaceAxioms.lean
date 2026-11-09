import Zkc.Verification.Transformations.Stages.Joint
import Zkc.Verification.Transformations.HashChain.Instance
import Zkc.Verification.Transformations.HashChain.Bytes
import Zkc.Protocol.Logic.Transcript.Budget
import Zkc.Protocol.Logic.Transcript.Reduction
import Zkc.Verification.Transformations.FiatShamir.Binding
import Zkc.Protocol.Library.Transformations.Commitment.HistoryKeys
import Zkc.Protocol.Library.Transformations.Commitment.Repeats
import Zkc.Tools.Program.DeclarationAudit

/-! Axiom closures and dependency rules of the shared interfaces: the core transcript interface
and path bounds, the keyed endpoint and its transformers, charged reductions, the lifting of law
interfaces, stage relations, the verdict transport lemma, the transport between oracle key forms,
binding, the charged commitment bridge and the hash chain restated through them. Every
declaration of these modules passes the declaration audit. -/

run_cmd do
  ZkcTools.DeclarationAudit.check
    [`Zkc.Program.Transcript, `Zkc.Protocol.Logic.Transcript.Interface, `Zkc.Protocol.Logic.Transcript.Typed, `Zkc.Protocol.Logic.Transcript.Keyed, `Zkc.Protocol.Logic.Transcript.Reduction, `Zkc.Protocol.Logic.Transcript.Budget, `Zkc.Protocol.Logic.Transcript.Lifting, `Zkc.Verification.Transformations.FiatShamir.Binding, `Zkc.Protocol.Library.Transformations.Stages, `Zkc.Verification.Transformations.Stages, `Zkc.Protocol.Logic.Games, `Zkc.Protocol.Library.Mathematics, `Zkc.Verification.Mathematics, `Zkc.Protocol.Library.Transformations.Oracle, `Zkc.Verification.Mathematics, `Zkc.Protocol.Library.Mathematics.Oracle.Memo, `Zkc.Protocol.Library.Transformations.Commitment, `Zkc.Protocol.Library.Transformations.HashChain, `Zkc.Verification.Transformations.HashChain]
    "SHARED-INTERFACES-AUDIT-PASS"
