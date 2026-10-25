module

@[expose] public section

/-! The registry of named hypotheses, cryptographic models and trusted links.

An assurance report lists every assumption a claim rests on by a registry
identifier. Each entry carries a *proposition schema*: a constant that,
applied to the claim's own data, is the proposition actually assumed, so the
report can show the instantiated statement next to its identifier and its
discharge (a proof, or assumed). A model entry names the definition that
embodies the idealization instead of a proposition. Entries whose obligation
has no Lean statement yet have no schema and say so.

Categories:
- a *library hypothesis* is an open mathematical statement, owned by a named
  library or by this package, that a theorem takes as a premise;
- a *model* is a cryptographic model or idealization: the random oracle on
  typed histories, challenges answered as exactly uniform field elements, and
  commitments read in the clear;
- a *law* is the realized law of a challenge decoder relative to the ideal
  sampler, discharged per decoder;
- a *trusted link* is an implementation correspondence outside Lean. Its schema
  states the correspondence over the uninterpreted native component, so an
  endpoint that takes it as a premise names the component it trusts;
- the *binding* obligations are the four distinct ones: statement
  determination, with the serialization of the typed representation and its
  native absorption recorded separately; collision-bounded identity;
  authenticated configuration; and verification-key correctness;
- *budget* premises bound adversary resources;
- a *family property* is an obligation a protocol family proves: a
  certificate's local step, its doomed set, or a property of a Sigma protocol;
- an *event* is a condition on a claim's statement or outcome, such as a false
  claim, a far word or acceptance;
- *well-formedness* premises state structural conditions and invariants of a
  lemma's data.

The declaration audit (`ZkcTools.DeclarationAudit.checkRegistry`, run by the
package audit) checks that every schema constant exists, that proposition
schemas are proposition-valued, and that every proposition-valued declaration of
this package heading a premise of one of its theorems is registered. Schema
names are written as plain names so that this module imports nothing that
defines them; the audit, not elaboration, finds a stale name.
Registration describes a theorem premise; it neither proves that premise nor
authorizes its use as an assumption in a claim receipt.

Registered endpoints map a covered semantic endpoint, a property and a statement
form to the theorem that states that property for artifact-indexed evidence. An
assurance report applies only a registered endpoint; a claim with no registered
endpoint is `unresolved`. -/

set_option autoImplicit false

namespace ZkcSecurity.Registry
open Lean (Name)

/-- The four binding obligations, with statement determination's two
representation steps recorded separately. -/
inductive Binding where
  /-- The initial transcript of a statement, followed by any events, determines
  the statement, malformed statements included. -/
  | statementDetermination
  /-- The canonical serialization of the typed public representation is
  injective and prefix-free (proved per codec). -/
  | serialization
  /-- The native transcript absorbs that serialization. A trusted link until a
  theorem about native transcript bytes exists. -/
  | nativeAbsorption
  /-- Digests in the scope identify programs and assets up to a collision
  event over every relevant hashing operation. -/
  | collisionBoundedIdentity
  /-- Configuration is authenticated by the deployment and fixed before the
  adversary runs. -/
  | authenticatedConfiguration
  /-- A verification key is the one the statement determines: checked
  recomputation, a certificate or a realization theorem. -/
  | verificationKey
  deriving DecidableEq, Repr

inductive Category where
  | libraryHypothesis
  | model
  | law
  | trustedLink
  | binding (obligation : Binding)
  | budget
  | familyProperty
  | event
  | wellFormedness
  deriving DecidableEq, Repr

def Binding.label : Binding → String
  | .statementDetermination => "statement-determination"
  | .serialization => "serialization"
  | .nativeAbsorption => "native-absorption"
  | .collisionBoundedIdentity => "collision-bounded-identity"
  | .authenticatedConfiguration => "authenticated-configuration"
  | .verificationKey => "verification-key"

def Category.label : Category → String
  | .libraryHypothesis => "library-hypothesis"
  | .model => "model"
  | .law => "law"
  | .trustedLink => "trusted-link"
  | .binding obligation => "binding/" ++ obligation.label
  | .budget => "budget"
  | .familyProperty => "family-property"
  | .event => "event"
  | .wellFormedness => "well-formedness"

/-- Whether an entry's schema must be a proposition-valued declaration. A model
names the definition that embodies it. -/
def Category.proposition : Category → Bool
  | .model => false
  | _ => true

structure Entry where
  identifier : String
  category : Category
  /-- The proposition schema, or the model definition; `none` when the
  obligation has no Lean statement yet. -/
  schema : Option Name
  statement : String

section Links
variable {Input Operation Result Context Bytes Value Program : Type}

/-- Runtime acceptance inclusion: every input the native runtime accepts, host
validation accepts. Soundness needs only this direction. -/
def RuntimeAcceptanceInclusion (runtime host : Input → Prop) : Prop :=
  ∀ input, runtime input → host input

/-- Installed native kernels implement their Lean meanings. -/
def KernelsImplement (native meaning : Operation → Result) : Prop :=
  ∀ operation, native operation = meaning operation

/-- The native codec is a function of a message's bytes and type alone: it does
not depend on the invocation context. -/
def CodecDeterministic (codec : Context → Bytes → Value) : Prop :=
  ∀ first second bytes, codec first bytes = codec second bytes

/-- The renderer of program bytes reads them as the runtime's program loader
does. -/
def ProgramReaderAgrees (loader renderer : Bytes → Option Program) : Prop :=
  ∀ bytes, loader bytes = renderer bytes

/-- The structured exporter and its renderer denote the original program. -/
def ExportDenotes (exported original : Program) : Prop :=
  exported = original

/-- The exporter prints the checked candidate. -/
def ExportsChecked (printed checked : Program) : Prop :=
  printed = checked

/-- The suite's framing, labels and payload codecs encode typed histories
injectively, so a typed history stands for the absorbed bytes. -/
def TranscriptEncodingInjective (encode : Value → Bytes) : Prop :=
  Function.Injective encode

/-- Proof bytes decode canonically to the typed messages in order: a decoded
message list encodes back to the bytes it was decoded from. -/
def ProofDecodingCanonical (encode : Value → Bytes) (decode : Bytes → Option Value) : Prop :=
  ∀ bytes value, decode bytes = some value → encode value = bytes

/-- The managed transcript absorbs the invocation's public values injectively:
two statements with the same absorbed bytes are equal. -/
def PublicAbsorptionInjective (absorb : Value → Bytes) : Prop :=
  Function.Injective absorb

/-- A verification key equals its checked recomputation from the statement. -/
def VerificationKeyRecomputed (key recomputed : Value) : Prop :=
  key = recomputed

end Links

/-- The registry. Identifiers are stable: a report or manifest names them. -/
def entries : List Entry := [
  ⟨"model.history-oracle", .model, some `OracleSpec.randomOracle,
    "The transcript challenge on an absorbed history is a uniformly random function of the \
    typed history, shared by the prover and verification (a lazily sampled random oracle)."⟩,
  ⟨"model.exact-uniform-challenges", .model, some `ZkcSecurity.FiatShamir.FieldOracle,
    "The oracle answers field challenges directly, as exactly uniform elements; the suite's \
    reduction of squeezed bytes to a field element is treated as exact."⟩,
  ⟨"model.ideal-commitments", .model, some `ZkcSecurity.Commitment.withTables,
    "Committed tables are received in the clear and reads return their entries."⟩,
  ⟨"model.exact-uniform-regime", .model, some `ZkcSecurity.Endpoint.Regime.exact,
    "The endpoints' challenge regime in which the oracle answers field elements and a challenge is \
    the answer itself, exactly uniform."⟩,
  ⟨"model.history-oracle-replay", .model, some `ZkcSecurity.Endpoint.Sigma.historyOracle,
    "The transcript challenge on a typed history is a lazily sampled, exactly uniform field \
    element, shared by the prover and verification, drawn through VCVio's replay oracle."⟩,
  ⟨"law.balanced-decoding", .law, some `ZkcSecurity.FiatShamir.Balanced,
    "Every event of the decoded challenge is at most a stated loss likelier than under the \
    uniform field."⟩,
  ⟨"law.realized-decoding", .law, some `ZkcSecurity.FiatShamir.Realized,
    "A decoder with refusal realizes the ideal law with a factor and a slack."⟩,
  ⟨"law.dominated-decoding", .law, some `ZkcSecurity.FiatShamir.Dominated,
    "Every event of the decoded answer is at most a factor times as likely as under the \
    uniform law of the sort."⟩,
  ⟨"law.exact-decoding", .law, some `ZkcSecurity.FiatShamir.ExactLaw,
    "Every event of the decoded value has its probability under the uniform law of the sort."⟩,
  ⟨"law.point-bound", .law, some `ZkcSecurity.FiatShamir.PointBound,
    "Every value of the decoded answer has probability at most a bound."⟩,
  ⟨"law.point-ratio", .law, some `ZkcSecurity.FiatShamir.PointRatio,
    "Every value is decoded with probability at most a factor times its uniform probability."⟩,
  ⟨"law.exact-with-refusal", .law, some `ZkcSecurity.FiatShamir.Obligations.ExactWithRefusal,
    "A successful decoding lands in every event with the success probability times the \
    event's ideal probability."⟩,
  ⟨"runtime.acceptance-inclusion", .trustedLink,
    some `ZkcSecurity.Registry.RuntimeAcceptanceInclusion,
    "The runtime accepts proof bytes for the admitted validator only when host validation \
    accepts them under the Entry's checked occurrence context, binding, data inputs and \
    challenge function."⟩,
  ⟨"runtime.installed-kernels", .trustedLink, some `ZkcSecurity.Registry.KernelsImplement,
    "Installed native kernels implement the meanings of the installed operations at the \
    admitted representations."⟩,
  ⟨"runtime.codec-function", .trustedLink, some `ZkcSecurity.Registry.CodecDeterministic,
    "The native codec is a function of a message's bytes and type."⟩,
  ⟨"runtime.program-reader", .trustedLink, some `ZkcSecurity.Registry.ProgramReaderAgrees,
    "The renderer of zkc.program/0 bytes reads them as the runtime's program loader does."⟩,
  ⟨"exporter.structured-denotation", .trustedLink, some `ZkcSecurity.Registry.ExportDenotes,
    "The structured exporter and its renderer denote the original program."⟩,
  ⟨"exporter.checked-candidate", .trustedLink, some `ZkcSecurity.Registry.ExportsChecked,
    "The exporter prints the checked candidate, and native field, group and transcript \
    kernels implement their mathematical meanings."⟩,
  ⟨"transcript.encoding-injective", .trustedLink,
    some `ZkcSecurity.Registry.TranscriptEncodingInjective,
    "The suite's framing, labels and payload codecs encode typed histories injectively."⟩,
  ⟨"transport.canonical-decoding", .trustedLink,
    some `ZkcSecurity.Registry.ProofDecodingCanonical,
    "Proof bytes decode canonically to the typed messages in order."⟩,
  ⟨"binding.statement-determination", .binding .statementDetermination,
    some `Zkc.Transcript.Determined,
    "The initial transcript of a statement, followed by any events, determines the \
    statement, malformed statements included."⟩,
  ⟨"binding.statement-determination.participant", .binding .statementDetermination,
    some `ZkcSecurity.FiatShamir.Determined,
    "Statement determination over the histories of the common participant actions."⟩,
  ⟨"binding.statement-coverage", .binding .statementDetermination,
    some `ZkcSecurity.FiatShamir.StatementBinding.Covers,
    "Every policy statement false for the application is false in the model or denotes no \
    model statement. Rejection of the latter is the separate obligation \
    binding.unmapped-rejection."⟩,
  ⟨"binding.unmapped-rejection", .binding .statementDetermination,
    some `ZkcSecurity.FiatShamir.StatementBinding.RejectsUnmapped,
    "The validator of every policy statement that denotes no model statement is doomed."⟩,
  ⟨"binding.event-implication", .binding .statementDetermination,
    some `ZkcSecurity.FiatShamir.EventImplication,
    "The application's false-acceptance event implies the modeled event."⟩,
  ⟨"binding.serialization", .binding .serialization,
    some `ZkcSecurity.FiatShamir.Obligations.PrefixFreeEncoding,
    "The serialization of the typed public representation is injective and prefix-free."⟩,
  ⟨"binding.native-absorption", .binding .nativeAbsorption,
    some `ZkcSecurity.Registry.PublicAbsorptionInjective,
    "The managed transcript absorbs the invocation's public values injectively; a typed \
    public-value binding does not discharge this."⟩,
  ⟨"binding.collision-bounded-identity", .binding .collisionBoundedIdentity, none,
    "Digests in the scope identify programs and assets outside a collision event over the \
    adversary's queries, setup, verifier recomputation and pre-existing digests. No Lean \
    statement yet."⟩,
  ⟨"binding.authenticated-configuration", .binding .authenticatedConfiguration,
    some `ZkcSecurity.FiatShamir.Obligations.AuthenticatedConfiguration,
    "Configuration is fixed by the deployment before the adversary runs."⟩,
  ⟨"binding.verification-key", .binding .verificationKey,
    some `ZkcSecurity.Registry.VerificationKeyRecomputed,
    "A verification key equals its checked recomputation from the statement."⟩,
  ⟨"budget.total-queries", .budget, some `OracleComp.IsTotalQueryBound,
    "The adversary makes at most the stated number of oracle queries on every path."⟩,
  ⟨"budget.selected-queries", .budget, some `OracleComp.IsQueryBoundP,
    "The adversary makes at most the stated number of queries selected by a predicate."⟩,
  ⟨"budget.weighted-cost", .budget, some `WorstCaseCostBound,
    "The adversary's oracle queries cost at most the stated budget on every path, each query the \
    weight of its key, repeats and cache hits included."⟩,
  ⟨"budget.participant-queries", .budget, some `ZkcSecurity.FiatShamir.QueryBound,
    "At most a budget of challenge queries on every path of a participant validator."⟩,
  ⟨"budget.typed-queries", .budget, some `ZkcSecurity.FiatShamir.Typed.QueryBound,
    "At most a budget of queries on every path of a validator over a typed interface."⟩,
  ⟨"budget.typed-cost", .budget, some `ZkcSecurity.FiatShamir.Typed.CostBound,
    "The queries on every path charge at most a cost, each the error of its occurrence."⟩,
  ⟨"budget.typed-charged-cost", .budget, some `ZkcSecurity.FiatShamir.Typed.ChargedCostBound,
    "The queries on every path charge at most a cost, each the charge of its key."⟩,
  ⟨"budget.process-cost-wp", .budget,
    some `ZkcSecurity.Obligations.WeakestPrecondition.CostTriple,
    "The process satisfies the selected cost precondition and return/stop postconditions, \
    charging each reached query at its actual history against remaining ENNReal credit."⟩,
  ⟨"budget.committed-charge", .budget, some `ZkcSecurity.Commitment.Charged,
    "Every path of a verifier with committed tables charges at most a budget, with \
    admissible committed shapes."⟩,
  ⟨"budget.commitments", .budget, some `ZkcSecurity.Commitment.CommitBound,
    "At most a budget of commitments on every path."⟩,
  ⟨"budget.hash-chain-calls", .budget, some `ZkcSecurity.HashChain.CallBound,
    "The chain verifier's primitive calls on every path: one per received or sent event and \
    the width plus one per query."⟩,
  ⟨"budget.provider-family-queries", .budget, some `ZkcSecurity.FiatShamir.Provider.FamilyQueryBound,
    "At most a budget of calls of each primitive family on every path."⟩,
  ⟨"family.participant-step", .familyProperty, some `ZkcSecurity.FiatShamir.Step,
    "The local obligation of a doomed set at one residual of a participant validator."⟩,
  ⟨"family.participant-step-to", .familyProperty, some `ZkcSecurity.FiatShamir.StepTo,
    "The local obligation of a doomed set of sub-validator residuals with a postcondition."⟩,
  ⟨"family.typed-step", .familyProperty, some `ZkcSecurity.FiatShamir.Typed.Step,
    "The local obligation of a doomed set over a typed interface, with an error per event."⟩,
  ⟨"family.typed-charged-step", .familyProperty, some `ZkcSecurity.FiatShamir.Typed.ChargedStep,
    "The local obligation of a history-indexed doomed set, with a charge per key."⟩,
  ⟨"family.typed-uniform-step", .familyProperty, some `ZkcSecurity.FiatShamir.Typed.UniformStep,
    "The uniform-sort local obligation of a history-indexed doomed set."⟩,
  ⟨"family.typed-charged-step-to", .familyProperty,
    some `ZkcSecurity.FiatShamir.Typed.ChargedStepTo,
    "The local obligation of a history-indexed doomed set of sub-validator residuals with a \
    postcondition on returned values, with a charge per key."⟩,
  ⟨"family.process-charged-wp", .familyProperty,
    some `ZkcSecurity.Obligations.WeakestPrecondition.ChargedTriple,
    "The process satisfies the selected charged precondition and return/stop postconditions, \
    retaining decoded message paths and the explicit escape obligation at each query."⟩,
  ⟨"family.typed-uniform-event-step", .familyProperty,
    some `ZkcSecurity.FiatShamir.Typed.UniformEventStep,
    "The uniform-sort local obligation of a doomed set that ignores the history."⟩,
  ⟨"family.keyed-resample-bound", .familyProperty, some `ZkcSecurity.FiatShamir.ResampleBound,
    "Under every answer table, resampling the answer at a key makes the key bad with \
    probability at most its charge."⟩,
  ⟨"family.commit-doomed", .familyProperty, some `ZkcSecurity.Commitment.CommitDoomed,
    "A history-indexed doomed set of an ideal reading stays doomed across a commitment, read \
    through every extraction."⟩,
  ⟨"family.stage-bound", .familyProperty, some `ZkcSecurity.Stage.Game.Bounded,
    "Every adversary admissible at a budget has bad probability at most the bound at that \
    budget."⟩,
  ⟨"family.extractor-first-match", .familyProperty,
    some `ZkcSecurity.Commitment.Extractable.FirstMatch,
    "A commitment extractor reads its record only through first matches: records with the same \
    first match for every predicate extract the same tables."⟩,
  ⟨"family.sigma-special-hvzk", .familyProperty, some `ZkcSecurity.VCVio.SigmaAnd.SpecialHVZK,
    "Special honest-verifier zero knowledge of a Sigma protocol."⟩,
  ⟨"family.sigma-correspondence", .familyProperty, some `ZkcSecurity.Endpoint.Sigma.Corresponds,
    "A verifier asks one challenge, at the initial transcript followed by the commitment's events \
    and the challenge occurrence, and returns the Sigma protocol's verification of the answer."⟩,
  ⟨"event.accepted", .event, some `Zkc.Transcript.Accepted,
    "A returned value satisfies the acceptance predicate; stops never accept."⟩,
  ⟨"event.returned-satisfies", .event, some `ZkcSecurity.VCVio.Execution.returnedSatisfies,
    "An execution returned a value satisfying a predicate; stops are nonaccepting."⟩,
  ⟨"event.committed-false-acceptance", .event, some `ZkcSecurity.Commitment.FalseAcceptance,
    "The verifier accepts and the statement is false for its tables extracted at the \
    checkpoint of one of its transcript queries."⟩,
  ⟨"event.unmapped-policy", .event, some `ZkcSecurity.FiatShamir.StatementBinding.Unmapped,
    "A policy statement denotes no model statement."⟩,
  ⟨"event.false-statement", .event, some `ZkcSecurity.Endpoint.ApplicationFalse,
    "A policy statement the claim's application contract counts as false."⟩,
  ⟨"event.unmapped-statement", .event, some `ZkcSecurity.Endpoint.ModelRelation.Unmapped,
    "A policy statement that denotes no model statement under the evidence's statement relation."⟩,
  ⟨"event.committed-opening-accepts-far", .event,
    some `ZkcSecurity.Examples.CommittedOpening.AcceptsFar,
    "The validator accepts and the frozen extraction at its checkpoint key is far."⟩,
  ⟨"event.committed-opening-far", .event, some `ZkcSecurity.Examples.CommittedOpening.Far,
    "No table was extracted, or a fraction of the extracted table's rows is not accepted."⟩,
  ⟨"event.committed-opening-far-rows", .event,
    some `ZkcSecurity.Examples.CommittedOpeningBridge.FarRows,
    "A table a fraction of whose rows are rejected."⟩,
  ⟨"wellformed.commitment-good-from", .wellFormedness, some `ZkcSecurity.Commitment.GoodFrom,
    "Every hash call new to a record is answered outside the targets recorded before it."⟩,
  ⟨"wellformed.leaf-hashing-climbs", .wellFormedness,
    some `ZkcSecurity.Commitment.LeafHashing.Climbs,
    "Every node call of a climb is in the log with its answer."⟩,
  ⟨"wellformed.hash-chain-agrees", .wellFormedness, some `ZkcSecurity.HashChain.Agrees,
    "Trace and tables are consistent, and unrouted cache entries are the auxiliary cell."⟩,
  ⟨"wellformed.hash-chain-caches-agree", .wellFormedness, some `ZkcSecurity.HashChain.CachesAgree,
    "Two caches answer the bytes of each classification alike."⟩,
  ⟨"wellformed.hash-chain-consistent", .wellFormedness, some `ZkcSecurity.HashChain.Consistent,
    "A trace and the simulator's tables agree on what the validator can read."⟩,
  ⟨"wellformed.hash-chain-generating", .wellFormedness, some `ZkcSecurity.HashChain.Generating,
    "A call generates a state: it binds an event or absorbs at a reached state."⟩,
  ⟨"wellformed.hash-chain-new-history", .wellFormedness, some `ZkcSecurity.HashChain.NewHistory,
    "The history whose state a generating call determines."⟩,
  ⟨"wellformed.hash-chain-organized", .wellFormedness, some `ZkcSecurity.HashChain.Organized,
    "Every key with a read cell is among the read keys."⟩,
  ⟨"wellformed.hash-chain-routed", .wellFormedness, some `ZkcSecurity.HashChain.Routed,
    "A request served by the history table: at a reached state, with a block below the width."⟩,
  ⟨"wellformed.hash-chain-encodable", .wellFormedness,
    some `ZkcSecurity.HashChain.Encoding.Encodable,
    "A chain input with a counter below 2^64."⟩,
  ⟨"wellformed.hash-chain-frame-bounded", .wellFormedness,
    some `ZkcSecurity.HashChain.Encoding.Frame.Bounded,
    "Label and data lengths below 2^64, as the eight-byte length fields require."⟩,
  ⟨"wellformed.hash-chain-event-bounded", .wellFormedness,
    some `ZkcSecurity.HashChain.Encoding.NativeEvent.Bounded,
    "Native event lengths below 2^64."⟩,
  ⟨"wellformed.handler-total-consistent", .wellFormedness,
    some `ZkcSecurity.FiatShamir.Obligations.TotalConsistentHandler,
    "Every selected call of a handler returns a fixed function of the operation and never \
    stops."⟩,
  ⟨"wellformed.execution-reaches", .wellFormedness, some `ZkcSecurity.VCVio.Execution.Reaches,
    "Reachability of returned values of an execution."⟩,
  ⟨"wellformed.execution-same-distribution", .wellFormedness,
    some `ZkcSecurity.VCVio.Execution.SameDist,
    "Equality of two complete output distributions."⟩,
  ⟨"wellformed.renaming-related", .wellFormedness, some `ZkcSecurity.Oracle.Renaming.Related,
    "Two caches agree through a renaming of oracle cells: a source key with a target cell \
    holds that cell's answer read back, and cells no source key reaches are empty."⟩,
  ⟨"wellformed.obligation-discharged", .wellFormedness,
    some `ZkcSecurity.FiatShamir.ObligationStatus.Discharged,
    "An obligation's status is a proof."⟩,
  ⟨"wellformed.claim-endpoint-hypotheses", .wellFormedness,
    some `ZkcSecurity.Claims.HypothesesProved,
    "Every legacy Evidence hypothesis admitted by a claims endpoint adapter carries its actual proof."⟩,
  ⟨"wellformed.provider-constituents", .wellFormedness,
    some `ZkcSecurity.FiatShamir.Provider.Simulator.Constituents,
    "Calls that belong to one concrete attempt of a provider simulator."⟩,
  ⟨"wellformed.provider-runs", .wellFormedness,
    some `ZkcSecurity.FiatShamir.Provider.Simulator.Runs,
    "The runs of a provider simulator from a tape."⟩,
  ⟨"family.sumcheck-message-laws", .familyProperty,
    some `ZkcSecurity.Families.Sumcheck.MessageLaws,
    "Every wire message denotes a polynomial within the stated degree bound, with boundary \
    and challenge evaluation equal to the wire operations."⟩,
  ⟨"family.sumcheck-reference-laws", .familyProperty,
    some `ZkcSecurity.Families.Sumcheck.ReferenceLaws,
    "At every admissible reference state, the round polynomial has the stated degree bound, \
    its boundary is the current total, and evaluation gives the restricted total; every \
    challenge preserves admissibility."⟩,
  ⟨"family.sumcheck-honest-message", .familyProperty,
    some `ZkcSecurity.Families.Sumcheck.HonestMessageLaw,
    "Every message satisfying the caller's delivery predicate denotes the reference round \
    polynomial at the represented state."⟩,
  ⟨"family.sumcheck-honest-execution", .familyProperty,
    some `ZkcSecurity.Families.Sumcheck.HonestRunLaws,
    "At reached invariant states, message receipt succeeds and establishes delivery; the \
    actual query and challenge delivery both return, preserving the next invariant with \
    their full handler states and observations."⟩,
  ⟨"family.sumcheck-conditional-agreement", .familyProperty,
    some `ZkcSecurity.Families.Sumcheck.QueryInterface.ConditionalBound,
    "For every admissible represented state, arbitrary message and history, agreement of \
    distinct polynomials within the two degree bounds under the actual decoded raw challenge \
    has probability at most the charge of that history and query event."⟩,
  ⟨"event.sumcheck-reference-true-claim", .event,
    some `ZkcSecurity.Families.Sumcheck.Representation.Yes,
    "The represented reference state is admissible and the implementation's scalar claim \
    equals its reference total."⟩,
  ⟨"event.sumcheck-reference-false-claim", .event,
    some `ZkcSecurity.Families.Sumcheck.Representation.No,
    "The represented reference state is admissible and the implementation's scalar claim \
    differs from its reference total."⟩,
  ⟨"event.honest-pair-relation", .event,
    some `ZkcSecurity.Claims.HonestPair.Subject.Relation,
    "The retained target's selectors read the subject's source inputs and its selected \
    formula returns true on those arguments; a stopped formula does not satisfy this relation."⟩,
  ⟨"event.honest-pair-success", .event,
    some `ZkcSecurity.Claims.HonestPair.Subject.Success,
    "Input preparation produces an observed pair execution in which both phases return, \
    the validator consumes the entire generated proof, and its selected Boolean result is true."⟩,
  ⟨"wellformed.sumcheck-admissible", .wellFormedness,
    some `ZkcSecurity.Families.Sumcheck.Representation.Allowed,
    "The mathematical reference state represented by the implementation state is admissible."⟩,
  ⟨"wellformed.sumcheck-active-independent", .wellFormedness,
    some `ZkcSecurity.Families.Sumcheck.FactorReference.ActiveIndependent,
    "At every Boolean vertex, the caller's weight is independent of the active field \
    challenge, including challenges outside the Boolean cube."⟩,
  ⟨"wellformed.domain-reading", .wellFormedness,
    some `ZkcSecurity.FiatShamir.DomainReduction.ReadingTo,
    "A derivation relates an actual Domain process to its typed transcript presentation \
    at the given history, retaining query keys, typed replies and decoding, and establishing \
    the specified postcondition on returned values."⟩,
  ⟨"wellformed.domain-coherence", .wellFormedness,
    some `ZkcSecurity.FiatShamir.DomainReduction.CoherentTo,
    "Every actual Domain query uses the reached observation history and a supported draw \
    request; the derivation establishes the specified postcondition at each returned value."⟩,
  ⟨"wellformed.domain-bridge", .wellFormedness,
    some `ZkcSecurity.FiatShamir.DomainReduction.Bridge,
    "The actual Domain process has both the specified typed reading with its return \
    postcondition and observation-history coherence with that same postcondition; \
    source-to-artifact binding is separate."⟩,
  ⟨"family.sumcheck-readback-helpers", .familyProperty,
    some `ZkcSecurity.Families.Sumcheck.TableComponent.ReadbackRound.HelperLaws,
    "The actual admitted message, fold, projection and append helpers compute their \
    specified mathematical results on every input admitted by their stated laws."⟩,
  ⟨"wellformed.sumcheck-readback-loop", .wellFormedness,
    some `ZkcSecurity.Families.Sumcheck.TableComponent.ReadbackRound.loopInvariant,
    "Both carried environments encode the same dimension-indexed prefix state and \
    original table, with the remaining dimension bounded and the scalar equal to the residual sum."⟩,
  ⟨"wellformed.sumcheck-source-helper-bodies", .wellFormedness,
    some `ZkcSecurity.Realizations.Sumcheck.DomainHelpers.Bodies,
    "The admitted source program contains the exact sumcheck, prefix, terminal-check \
    and table-check helper bodies with their complete checked dependencies."⟩,
  ⟨"wellformed.honest-pair-pointwise-wp", .wellFormedness,
    some `ZkcSecurity.FiatShamir.HonestCompiled.pairWP,
    "On one fixed shared answer table, the actual producer and validator both return, \
    the validator consumes exactly the generated proof and accepts at the selected position. \
    This pointwise runner property supplies no probabilistic or adversarial assumption."⟩,
  ⟨"wellformed.honest-readback", .wellFormedness,
    some `ZkcSecurity.FiatShamir.Readback,
    "A derivation aligns producer sends with typed validator receives and identical \
    history/origin queries for every shared reply, retaining checkpoints and observations \
    and requiring both processes to return values satisfying the paired postcondition."⟩,
  ⟨"wellformed.honest-sampling-prefix", .wellFormedness,
    some `ZkcSecurity.FiatShamir.SamplingPrefix,
    "Every authorized private reply follows the actual producer prefix to its stated \
    postcondition, retaining checkpoints and ordered local requests."⟩,
  ⟨"wellformed.honest-sampled-readback", .wellFormedness,
    some `ZkcSecurity.FiatShamir.SampledReadback,
    "An authorized producer-private prefix aligns with the actual deterministic paired \
    continuation for every reply, including its exact public transcript and returned values."⟩,
  ⟨"law.honest-private-service-return", .law,
    some `ZkcSecurity.FiatShamir.SampledReadback.Returns,
    "Every supported outcome of an allowed producer-local service invocation returns a \
    reply; this handler law does not restrict the sampled value or honest input."⟩,
  ⟨"wellformed.honest-private-service-allowed", .wellFormedness,
    some `ZkcSecurity.FiatShamir.SampledReadback.Allowed,
    "The reached local request is authorized by the fixed subject context and actual \
    admitted participant service ports."⟩,
  ⟨"wellformed.honest-pair-input", .wellFormedness,
    some `ZkcSecurity.Claims.HonestPair.Subject.HonestInput,
    "The fixed request input policy and all retained source input clauses hold, and the \
    exact source input projections encode both selected runtime ABIs with matching sorts."⟩,
  ⟨"wellformed.honest-pair-nonvacuous", .wellFormedness,
    some `ZkcSecurity.Claims.HonestPair.Nonvacuous,
    "Some source input satisfies both the subject's retained target relation and its \
    fixed honest input contract."⟩,
  ⟨"wellformed.gkr-rounds-active-independent", .wellFormedness,
    some `ZkcSecurity.Examples.Components.GkrRoundsReference.independent,
    "At least one of the two retained wire factors is independent of the active challenge \
    at every Boolean vertex."⟩,
  ⟨"wellformed.gkr-rounds-admissible", .wellFormedness,
    some `ZkcSecurity.Examples.Components.GkrRoundsReference.admissible,
    "At every positive remaining dimension and after every possible future challenge \
    prefix, at least one retained wire factor is independent of the active challenge; \
    dimension zero has no further condition."⟩,
  ⟨"wellformed.gkr-rounds-caller-layout", .wellFormedness,
    some `ZkcSecurity.Examples.Components.GkrRoundsLayout.CallerLayout,
    "The retained left and right wire factors are respectively a replicated table on the \
    leading variables and a tiled table on the trailing variables at the stated split."⟩,
  ⟨"wellformed.gkr-rounds-decoding", .wellFormedness,
    some `ZkcSecurity.Examples.Components.GkrRoundsRealization.Decodes,
    "The four raw vectors decode at the exact remaining dimension to the retained add, \
    multiply, left-wire and right-wire factors separately."⟩,
  ⟨"wellformed.gkr-rounds-representation", .wellFormedness,
    some `ZkcSecurity.Examples.Components.GkrRoundsGateRealization.Represents,
    "All four raw vectors decode to the retained factors, the reference is admissible for \
    every future challenge prefix, and its cube size is below the logical index limit."⟩,
  ⟨"wellformed.canonical-model-admission", .wellFormedness,
    some `ZkcSecurity.Claims.CanonicalModelAdmission,
    "The request selects the authority's complete model entry and model elaboration \
    succeeds for the same subject and application."⟩,
  ⟨"wellformed.canonical-property-admission", .wellFormedness,
    some `ZkcSecurity.Claims.CanonicalAdmission,
    "Subject admission succeeds and the resolved property entry is exactly the \
    authority's entry for the selected canonical property key."⟩,
  ⟨"wellformed.author-extension-admission", .wellFormedness,
    some `ZkcSecurity.Claims.AuthorExtensionAdmission,
    "Subject admission succeeds and the requested author property identifier is not \
    reserved by the canonical security authority."⟩,
  ⟨"wellformed.gkr-rounds-prefix", .wellFormedness,
    some `ZkcSecurity.Examples.Components.GkrRoundsResidual.Prefix,
    "The state is reached from the fixed caller state by successive factor restrictions \
    under arbitrary received coefficient triples and challenges."⟩,
  ⟨"event.gkr-rounds-false-residual", .event,
    some `ZkcSecurity.Examples.Components.GkrRoundsResidual.NoReturn,
    "The complete returned ABI encodes a state at the fixed residual dimension that \
    retains the caller-anchored prefix, factor representation and false residual."⟩,
  ⟨"wellformed.original-presentation-alignment", .wellFormedness,
    some `ZkcSecurity.FiatShamir.Original.Alignment,
    "The source and target presentations have the same operations and all reply branches, \
    retain stops, and satisfy the fixed relation at every return."⟩,
  ⟨"law.original-lossless-interface", .law,
    some `ZkcSecurity.FiatShamir.Original.LosslessInterface,
    "Receive and query reply maps are bijective with representable payloads, and send \
    operations have only the selected reply, permitting full-result presentation transport."⟩,
  ⟨"wellformed.sumcheck-original-validator-routes", .wellFormedness,
    some `ZkcSecurity.Realizations.Sumcheck.ArtifactBinding.Routes,
    "The validator's source message, draw and delivery sites resolve at the given frames \
    to the selected nominal origins, service handle and validator mode."⟩,
  ⟨"wellformed.sumcheck-original-validator-return", .wellFormedness,
    some `ZkcSecurity.Realizations.Sumcheck.ArtifactBinding.VerifierReturns,
    "The full optional validator callback ABI agrees with the selected live point and \
    scalar slots, transcript history and source occurrence frames."⟩,
  ⟨"wellformed.sumcheck-original-root-return", .wellFormedness,
    some `ZkcSecurity.Realizations.Sumcheck.ArtifactRoot.ValidatorReturns,
    "The original Boolean return agrees with the artifact's complete returned values, \
    selected live Boolean and transcript slots, reached history and empty source frames."⟩,
  ⟨"wellformed.sumcheck-original-producer-return", .wellFormedness,
    some `ZkcSecurity.Realizations.Sumcheck.OriginalProducer.Returns,
    "The complete optional producer callback ABI agrees with its five selected live \
    carried slots, reached transcript history and source occurrence frames."⟩,
  ⟨"wellformed.sumcheck-original-producer-routes", .wellFormedness,
    some `ZkcSecurity.Realizations.Sumcheck.OriginalProducer.Routes,
    "The producer's source message and challenge-delivery sites resolve at the given \
    frames to the selected nominal origins and producer mode."⟩,
  ⟨"wellformed.sumcheck-original-pair-postcondition", .wellFormedness,
    some `ZkcSecurity.Realizations.Sumcheck.OriginalRoot.ActualPost,
    "The actual producer and validator results satisfy their complete original return \
    relations and the accepting honest source-pair postcondition."⟩,
  ⟨"wellformed.sumcheck-original-security-routes", .wellFormedness,
    some `ZkcSecurity.Realizations.Sumcheck.OriginalSecurity.Routes,
    "At every reached source loop index and outer frame, source messages, draw and \
    delivery resolve to the selected schedule and service handle in validator mode."⟩
]

/-- The registry as data of core types, for the declaration-record emitter:
identifier, category, schema constant and statement. -/
def table : List (String × String × Option Name × String) :=
  entries.map fun entry => (entry.identifier, entry.category.label, entry.schema, entry.statement)

/-- The registry as the declaration audit reads it: identifier, schema
constant and whether the schema must be proposition-valued. -/
def audited : List (String × Option Name × Bool) :=
  entries.map fun entry => (entry.identifier, entry.schema, entry.category.proposition)

/-- Registered endpoints: covered semantic endpoint (`ideal-meaning` or
`executable-bytes`), property, statement form (`fixed` or `adaptive`) and the
endpoint theorem over artifact-indexed evidence (`ZkcSecurity.Endpoint`).
Knowledge soundness is registered for fixed statements only. -/
def endpoints : List (String × String × String × Name) := [
  ("ideal-meaning", "soundness", "fixed", `ZkcSecurity.Endpoint.fixed_soundness),
  ("ideal-meaning", "soundness", "adaptive", `ZkcSecurity.Endpoint.adaptive_soundness),
  ("executable-bytes", "soundness", "fixed", `ZkcSecurity.Endpoint.fixed_soundness_bytes),
  ("executable-bytes", "soundness", "adaptive", `ZkcSecurity.Endpoint.adaptive_soundness_bytes),
  ("ideal-meaning", "knowledge-soundness", "fixed", `ZkcSecurity.Endpoint.knowledge_soundness),
  ("executable-bytes", "knowledge-soundness", "fixed", `ZkcSecurity.Endpoint.knowledge_soundness_bytes)
]

end ZkcSecurity.Registry
