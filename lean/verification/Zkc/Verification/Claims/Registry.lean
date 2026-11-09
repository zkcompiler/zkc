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
- a *law* states a realized decoder distribution or a semantic connection
  between execution stages, discharged by the selected implementation;
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
  ⟨"wellformed.query-tree-cache", .wellFormedness,
    some `ZkcSecurity.FiatShamir.QueryTree.Consistent,
    "Every recorded macro-answer table agrees with the fixed complete oracle table."⟩,
  ⟨"wellformed.batch-verification-shape", .wellFormedness,
    some `ZkcSecurity.Commitment.BatchVerification.ValidShape,
    "The selected table has positive width and height, admissible height, and a representable \
    element count within the fixed resource ceiling."⟩,
  ⟨"model.history-oracle", .model, some `OracleSpec.randomOracle,
    "The transcript challenge on an absorbed history is a uniformly random function of the \
    typed history, shared by the prover and verification (a lazily sampled random oracle)."⟩,
  ⟨"model.ideal-commitments", .model, some `ZkcSecurity.Commitment.withTables,
    "Committed tables are received in the clear and reads return their entries."⟩,
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
  ⟨"event.accepted", .event, some `Zkc.Transcript.Accepted,
    "A returned value satisfies the acceptance predicate; stops never accept."⟩,
  ⟨"event.returned-satisfies", .event, some `ZkcSecurity.VCVio.Execution.returnedSatisfies,
    "An execution returned a value satisfying a predicate; stops are nonaccepting."⟩,
  ⟨"event.committed-false-acceptance", .event, some `ZkcSecurity.Commitment.FalseAcceptance,
    "The verifier accepts and the statement is false for its tables extracted at the \
    checkpoint of one of its transcript queries."⟩,
  ⟨"event.finite-selection-bad", .event,
    some `ZkcSecurity.Probability.FiniteSelection.SelectedBad,
    "The first admitted value in the complete bounded attempt history satisfies the bad event."⟩,
  ⟨"event.committed-opening-far-rows", .event,
    some `ZkcSecurity.Examples.CommittedOpeningBridge.FarRows,
    "A table a fraction of whose rows are rejected."⟩,
  ⟨"wellformed.commitment-good-from", .wellFormedness, some `ZkcSecurity.Commitment.GoodFrom,
    "Every hash call new to a record is answered outside the targets recorded before it."⟩,
  ⟨"wellformed.leaf-hashing-climbs", .wellFormedness,
    some `ZkcSecurity.Commitment.LeafHashing.Climbs,
    "Every node call of a climb is in the log with its answer."⟩,
  ⟨"wellformed.batch-opening-layer", .wellFormedness,
    some `ZkcSecurity.Commitment.BatchOpening.Layer,
    "One ordered frontier layer consumes its boundary siblings and records each shared compression."⟩,
  ⟨"wellformed.batch-opening-reduction", .wellFormedness,
    some `ZkcSecurity.Commitment.BatchOpening.Reduction,
    "The verifier-fixed depth reduces the recorded frontier to one root and consumes every sibling."⟩,
  ⟨"wellformed.batch-opening-rows", .wellFormedness,
    some `ZkcSecurity.Commitment.BatchOpening.RowsRecorded,
    "Every ordered requested row, including repeats, has its leaf call and active frontier label."⟩,
  ⟨"event.batch-opening-collision", .event,
    some `ZkcSecurity.Commitment.BatchOpening.Collision,
    "Two distinct complete hash queries in the recorded execution have the same answer."⟩,
  ⟨"wellformed.hash-chain-agrees", .wellFormedness, some `ZkcSecurity.HashChain.Agrees,
    "Trace and tables are consistent, and unrouted cache entries are the auxiliary cell."⟩,
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
  ⟨"wellformed.sumcheck-admissible", .wellFormedness,
    some `ZkcSecurity.Families.Sumcheck.Representation.Allowed,
    "The mathematical reference state represented by the implementation state is admissible."⟩,
  ⟨"wellformed.sumcheck-active-independent", .wellFormedness,
    some `ZkcSecurity.Families.Sumcheck.FactorReference.ActiveIndependent,
    "At every Boolean vertex, the caller's weight is independent of the active field \
    challenge, including challenges outside the Boolean cube."⟩,
  ⟨"event.proximity-far", .event,
    some `ZkcSecurity.Families.Proximity.Far,
    "The word has at least the fixed normalized Hamming distance from every codeword; the \
    threshold determines the gap."⟩,
  ⟨"event.gkr-output-difference", .event,
    some `ZkcSecurity.Families.Gkr.Output.Differ,
    "The output-difference polynomial is nonzero on some Boolean suffix of the current \
    dimension-aligned challenge prefix."⟩,
  ⟨"wellformed.gkr-circuit-shape", .wellFormedness,
    some `ZkcSecurity.Realizations.Gkr.CircuitEncoding.Shape,
    "The input and stacked wiring vectors have their declared dimensions, and the layer \
    count fits the selector domain."⟩,
  ⟨"wellformed.gkr-circuit-admission", .wellFormedness,
    some `ZkcSecurity.Realizations.Gkr.CircuitEncoding.Admitted,
    "Circuit shape, output length, configured width and layer bounds, and the logical index \
    limit hold before execution."⟩,
  ⟨"event.gkr-circuit-outputs", .event,
    some `ZkcSecurity.Realizations.Gkr.CircuitEncoding.Outputs,
    "The shaped circuit encoding decodes the claimed outputs to the mathematical evaluation \
    of the circuit at its final layer."⟩,
  ⟨"event.gkr-residual-relation", .event,
    some `ZkcSecurity.Realizations.Gkr.Relations.Residual,
    "The raw factors decode at one common dimension, and the claim equals their Boolean sum \
    after the retained prefix restriction."⟩,
  ⟨"wellformed.gkr-source-representation", .wellFormedness,
    some `ZkcSecurity.Realizations.Gkr.Source.Represents,
    "The invocation dimensions, input and output tables, wiring blocks and source index \
    bounds represent the specified mathematical circuit."⟩,
  ⟨"wellformed.gkr-source-admission", .wellFormedness,
    some `ZkcSecurity.Realizations.Gkr.Source.Invocation.Admitted,
    "The concrete source invocation meets its fixed circuit admission bounds and output \
    shape, independently of target truth."⟩,
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
  ⟨"budget.repeated-component-step", .budget,
    some `ZkcSecurity.Obligations.RepeatedComponent.CostContract,
    "One component step retains the continuation's history-dependent budget under its \
    frame invariant; the charge uses the actual reached history and query."⟩,
  ⟨"budget.process-weakest-precondition", .budget,
    some `ZkcSecurity.Obligations.WeakestPrecondition.costWP,
    "The process satisfies its successful and stopping postconditions for all recovered \
    replies while accounting for history-dependent charges and the available budget."⟩,
  ⟨"law.hash-decoder-consistency", .law,
    some `ZkcSecurity.Commitment.DecoderConsistent,
    "Equal recorded labels within one decoding role determine the same decoded value; cross-role aliases are allowed."⟩,
  ⟨"event.permutation-fiber-hit", .event,
    some `ZkcSecurity.Probability.PermutationExposure.FiberHit,
    "The sampled rate or capacity coordinate belongs to its fixed pre-sampling target set."⟩,
  ⟨"wellformed.permutation-cached-query", .wellFormedness,
    some `ZkcSecurity.Probability.PermutationExposure.State.cached,
    "The shared partial bijection already exposes the query in its selected direction."⟩,
  ⟨"wellformed.permutation-target-bound", .wellFormedness,
    some `ZkcSecurity.Probability.PermutationExposure.TargetBound,
    "Before each fresh reply the two coordinate target sets have total cardinality at most five times the exposed-pair count plus the root budget and four."⟩,
  ⟨"wellformed.permutation-same-pair", .wellFormedness,
    some `ZkcSecurity.Commitment.PoseidonRows.SamePair,
    "Two oriented record entries have the same full primitive input and output."⟩,
  ⟨"wellformed.permutation-local-good", .wellFormedness,
    some `ZkcSecurity.Commitment.PoseidonRows.LocalGood,
    "The exposure avoids its local rate and capacity coincidences in the correct query direction."⟩,
  ⟨"wellformed.permutation-ordered-good", .wellFormedness,
    some `ZkcSecurity.Commitment.PoseidonRows.OrderedGood,
    "A later exposure avoids the chronological coordinate coincidences needed for extraction."⟩,
  ⟨"wellformed.permutation-good-record", .wellFormedness,
    some `ZkcSecurity.Commitment.PoseidonRows.Good,
    "The normalized chronological record satisfies the local and ordered exposure conditions."⟩,
  ⟨"wellformed.permutation-sponge-trace", .wellFormedness,
    some `ZkcSecurity.Commitment.PoseidonRows.SpongeTrace,
    "The recorded full permutation inputs follow the fixed overwrite-sponge equations for the entire row."⟩,
  ⟨"wellformed.permutation-node-climb", .wellFormedness,
    some `ZkcSecurity.Commitment.PoseidonRows.NodeClimb,
    "The recorded compression inputs connect the selected leaf to the root at the supplied index."⟩,
  ⟨"wellformed.permutation-consistent-permutation", .wellFormedness,
    some `ZkcSecurity.Commitment.PoseidonRows.Consistent,
    "Every record entry is an equation of the selected full-state permutation."⟩,
  ⟨"wellformed.permutation-capacity-safe", .wellFormedness,
    some `ZkcSecurity.Commitment.PoseidonRows.CapacitySafe,
    "The new exposure cannot complete a previously missing capacity predecessor."⟩,
  ⟨"wellformed.permutation-good-history", .wellFormedness,
    some `ZkcSecurity.Commitment.PoseidonRows.GoodHistory,
    "The chronological record is good and every earlier accepted allocation root remains protected."⟩,
  ⟨"wellformed.permutation-active-frontier", .wellFormedness,
    some `ZkcSecurity.Commitment.PoseidonRows.Active,
    "Every active frontier label has a forward-born recorded primitive exposure."⟩,
  ⟨"wellformed.permutation-primitive-rows", .wellFormedness,
    some `ZkcSecurity.Commitment.PoseidonRows.PrimitiveRows,
    "Recorded overwrite traces cover all requested rows in order, retaining repeated positions."⟩,
  ⟨"wellformed.permutation-monitor-association", .wellFormedness,
    some `ZkcSecurity.Commitment.PoseidonRows.Monitored.Associated,
    "The normalized record and the exposed partial bijection contain exactly the same oriented pairs."⟩,
  ⟨"wellformed.permutation-monitor-invariant", .wellFormedness,
    some `ZkcSecurity.Commitment.PoseidonRows.Monitored.Invariant,
    "The handler state is associated with its actual record and registrations, and a clear bad flag implies a good history."⟩,
  ⟨"wellformed.permutation-recorded-opening", .wellFormedness,
    some `ZkcSecurity.Commitment.PoseidonRows.Monitored.OpeningRecorded,
    "A scalar opening has concrete recorded sponge and path witnesses at the first allocation, with fixed depth and actual-height bounds."⟩,
  ⟨"wellformed.permutation-recorded-batch", .wellFormedness,
    some `ZkcSecurity.Commitment.PoseidonRows.Monitored.BatchRecorded,
    "A batch has a recorded frontier reduction and complete ordered row coverage at the first allocation, with actual-height bounds."⟩,
  ⟨"event.permutation-extraction-disagreement", .event,
    some `ZkcSecurity.Commitment.PoseidonRows.Monitored.Disagreement,
    "A concretely recorded scalar or batch opening differs from the request-fixed first-allocation extractor, including its fixed zero completion."⟩,
  ⟨"budget.permutation-primitive-calls", .budget,
    some `ZkcSecurity.Commitment.PoseidonRows.Monitored.PrimitiveBudget,
    "The structural budget counts all primitive calls, including cache hits and inverse calls; allocation attempts are uncharged."⟩,
  ⟨"model.monitored-lazy-permutation", .model,
    some `ZkcSecurity.Commitment.PoseidonRows.Monitored.handler,
    "One finite lazy partial bijection answers both query directions and records actual calls and root allocations with explicit root-budget refusal."⟩
]

/-- The registry as data of core types, for the declaration-record emitter:
identifier, category, schema constant and statement. -/
def table : List (String × String × Option Name × String) :=
  entries.map fun entry => (entry.identifier, entry.category.label, entry.schema, entry.statement)

/-- The registry as the declaration audit reads it: identifier, schema
constant and whether the schema must be proposition-valued. -/
def audited : List (String × Option Name × Bool) :=
  entries.map fun entry => (entry.identifier, entry.schema, entry.category.proposition)

/-- No concrete source or byte endpoint is currently installed. Independent mathematical
theorems do not certify an admitted native artifact. Actual-source installation is separate. -/
def endpoints : List (String × String × String × Name) := []

end ZkcSecurity.Registry
