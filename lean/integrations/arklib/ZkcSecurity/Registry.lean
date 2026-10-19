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

Registered endpoints map a covered semantic endpoint, a property and a statement
form to the theorem that states that property for artifact-indexed evidence. An
assurance report applies only a registered endpoint; until one is registered for
a claim, the claim's report is `unresolved`. -/

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
  -- Models.
  ⟨"model.history-oracle", .model, some `OracleSpec.randomOracle,
    "The transcript challenge on an absorbed history is a uniformly random function of the \
    typed history, shared by the prover and verification (a lazily sampled random oracle)."⟩,
  ⟨"model.exact-uniform-challenges", .model, some `ZkcSecurity.FiatShamir.FieldOracle,
    "The oracle answers field challenges directly, as exactly uniform elements; the suite's \
    reduction of squeezed bytes to a field element is treated as exact."⟩,
  ⟨"model.ideal-commitments", .model, some `ZkcSecurity.Commitment.withTables,
    "Committed tables are received in the clear and reads return their entries."⟩,
  -- Laws of challenge decoders.
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
  -- Library hypotheses.
  ⟨"hypothesis.fri-folding-proximity", .libraryHypothesis,
    some `ZkcSecurity.ArkLib.Fri.FoldingProximity,
    "Mutual correlated agreement of the line generator on every folded Reed-Solomon code at \
    the radius; proved at the unique-decoding radius, and for folding up to the cube-root \
    radius, and open beyond."⟩,
  -- Trusted links.
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
  -- Binding obligations.
  ⟨"binding.statement-determination", .binding .statementDetermination,
    some `ZkcSecurity.FiatShamir.Typed.Determined,
    "The initial transcript of a statement, followed by any events, determines the \
    statement, malformed statements included."⟩,
  ⟨"binding.statement-determination.participant", .binding .statementDetermination,
    some `ZkcSecurity.FiatShamir.Determined,
    "Statement determination over the histories of the common participant actions."⟩,
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
  -- Budget premises.
  ⟨"budget.total-queries", .budget, some `OracleComp.IsTotalQueryBound,
    "The adversary makes at most the stated number of oracle queries on every path."⟩,
  ⟨"budget.selected-queries", .budget, some `OracleComp.IsQueryBoundP,
    "The adversary makes at most the stated number of queries selected by a predicate."⟩,
  ⟨"budget.participant-queries", .budget, some `ZkcSecurity.FiatShamir.QueryBound,
    "At most a budget of challenge queries on every path of a participant validator."⟩,
  ⟨"budget.typed-queries", .budget, some `ZkcSecurity.FiatShamir.Typed.QueryBound,
    "At most a budget of queries on every path of a validator over a typed interface."⟩,
  ⟨"budget.typed-cost", .budget, some `ZkcSecurity.FiatShamir.Typed.CostBound,
    "The queries on every path charge at most a cost, each the error of its occurrence."⟩,
  ⟨"budget.typed-charged-cost", .budget, some `ZkcSecurity.FiatShamir.Typed.ChargedCostBound,
    "The queries on every path charge at most a cost, each the charge of its key."⟩,
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
  -- Family properties: certificate obligations, doomed sets and protocol properties a
  -- protocol family proves.
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
  ⟨"family.upstream-realization", .familyProperty, some `ZkcSecurity.FiatShamir.Upstream.Realizes,
    "A participant process realizes an upstream process-form residual operation by \
    operation."⟩,
  ⟨"family.fri-round-by-round", .familyProperty, some `ZkcSecurity.ArkLib.Fri.RoundByRound,
    "The round-by-round soundness certificate of the FRI verifier at the ideal \
    interpretation, with errors per folding round and for the query block."⟩,
  ⟨"family.fri-step", .familyProperty, some `ZkcSecurity.ArkLib.Fri.Step,
    "The local obligations of a doomed set of the FRI verifier."⟩,
  ⟨"family.fri-folding-escapes", .familyProperty, some `ZkcSecurity.ArkLib.Fri.FoldingEscapes,
    "At every folding round and for every committed word, a fresh challenge escapes with \
    probability at most the round's error."⟩,
  ⟨"family.fri-doomed", .familyProperty, some `ZkcSecurity.ArkLib.Fri.Doomed,
    "The doomed residuals of the FRI certificate."⟩,
  ⟨"family.sumcheck-doomed", .familyProperty, some `ZkcSecurity.Examples.SumcheckFiatShamir.Doomed,
    "The doomed residuals of the Sumcheck certificate: phases satisfying the invariant."⟩,
  ⟨"family.sumcheck-doomed-any", .familyProperty,
    some `ZkcSecurity.Examples.SumcheckFiatShamir.DoomedAny,
    "The doomed residuals of the Sumcheck certificate for every table and claim."⟩,
  ⟨"family.sigma-special-hvzk", .familyProperty, some `ZkcSecurity.VCVio.SigmaAnd.SpecialHVZK,
    "Special honest-verifier zero knowledge of a Sigma protocol."⟩,
  -- Events: conditions on a claim's statement or outcome.
  ⟨"event.accepted", .event, some `ZkcSecurity.FiatShamir.Accepted,
    "A returned value satisfies the acceptance predicate; stops never accept."⟩,
  ⟨"event.returned-satisfies", .event, some `ZkcSecurity.VCVio.Execution.returnedSatisfies,
    "An execution returned a value satisfying a predicate; stops are nonaccepting."⟩,
  ⟨"event.committed-false-acceptance", .event, some `ZkcSecurity.Commitment.FalseAcceptance,
    "The verifier accepts and the statement is false for its tables extracted at the \
    checkpoint of one of its transcript queries."⟩,
  ⟨"event.fri-far", .event, some `ZkcSecurity.ArkLib.Fri.Far,
    "A word at relative distance at least the radius from every codeword."⟩,
  ⟨"event.gkr-false-claim", .event, some `ZkcSecurity.ArkLib.Gkr.FalseClaim,
    "A GKR round claim is false at the challenge prefix."⟩,
  ⟨"event.gkr-layer-false", .event, some `ZkcSecurity.Examples.GkrFiatShamir.LayerFalse,
    "A false claim about a GKR layer at its point."⟩,
  ⟨"event.gkr-outputs-differ", .event, some `ZkcSecurity.Examples.GkrFiatShamir.OutputsDiffer,
    "The claimed outputs and the circuit's outputs differ at some Boolean completion."⟩,
  ⟨"event.sumcheck-false-claim", .event, some `ZkcSecurity.Examples.SumcheckFiatShamir.FalseClaim,
    "A Sumcheck claim is false at the point."⟩,
  ⟨"event.causal-table-terminal", .event,
    some `ZkcSecurity.ArkLib.Sumcheck.Multilinear.Causal.tableTerminal,
    "The terminal check of the causal multilinear Sumcheck against a table."⟩,
  ⟨"event.committed-opening-accepts-far", .event,
    some `ZkcSecurity.Examples.CommittedOpening.AcceptsFar,
    "The validator accepts and the frozen extraction at its checkpoint key is far."⟩,
  ⟨"event.committed-opening-far", .event, some `ZkcSecurity.Examples.CommittedOpening.Far,
    "No table was extracted, or a fraction of the extracted table's rows is not accepted."⟩,
  ⟨"event.committed-opening-far-rows", .event,
    some `ZkcSecurity.Examples.CommittedOpeningBridge.FarRows,
    "A table a fraction of whose rows are rejected."⟩,
  -- Well-formedness: structural conditions and invariants of lemmas.
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
  ⟨"wellformed.fri-compatible-roots", .wellFormedness, some `ZkcSecurity.ArkLib.Fri.Compatible,
    "The roots used along the folds are compatible."⟩,
  ⟨"wellformed.fri-honest-layers", .wellFormedness, some `ZkcSecurity.ArkLib.Fri.Honest,
    "Each committed word after the first is ArkLib's fold of the previous word."⟩,
  ⟨"wellformed.committed-fri-admissible", .wellFormedness,
    some `ZkcSecurity.Examples.CommittedFri.Admissible,
    "The admissible committed shapes: words of bounded size."⟩,
  ⟨"wellformed.committed-fri-matches", .wellFormedness,
    some `ZkcSecurity.Examples.CommittedFri.Matches,
    "The committed tables from a handle on are the layers' words, in order."⟩,
  ⟨"wellformed.gkr-statement", .wellFormedness,
    some `ZkcSecurity.Examples.CompiledGkrFiatShamir.WellFormed,
    "A GKR statement whose raw public inputs decode to the circuit the plain verifier reads."⟩,
  ⟨"wellformed.gkr-line-coefficients", .wellFormedness,
    some `ZkcSecurity.Examples.GkrFiatShamir.CoefficientsFrom,
    "The remaining coefficients of a line polynomial with a given constant term."⟩,
  ⟨"wellformed.handler-total-consistent", .wellFormedness,
    some `ZkcSecurity.FiatShamir.Obligations.TotalConsistentHandler,
    "Every selected call of a handler returns a fixed function of the operation and never \
    stops."⟩,
  ⟨"wellformed.execution-reaches", .wellFormedness, some `ZkcSecurity.VCVio.Execution.Reaches,
    "Reachability of returned values of an execution."⟩,
  ⟨"wellformed.execution-same-distribution", .wellFormedness,
    some `ZkcSecurity.VCVio.Execution.SameDist,
    "Equality of two complete output distributions."⟩,
  ⟨"wellformed.provider-constituents", .wellFormedness,
    some `ZkcSecurity.FiatShamir.Provider.Simulator.Constituents,
    "Calls that belong to one concrete attempt of a provider simulator."⟩,
  ⟨"wellformed.provider-runs", .wellFormedness,
    some `ZkcSecurity.FiatShamir.Provider.Simulator.Runs,
    "The runs of a provider simulator from a tape."⟩,
  ⟨"wellformed.causal-msb-chronology", .wellFormedness,
    some `ZkcSecurity.ArkLib.Sumcheck.Multilinear.Causal.MSBChronology,
    "Chronological challenges are in the table's most-significant-first coordinate order."⟩
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
endpoint theorem. Empty until an endpoint over artifact-indexed evidence
exists. -/
def endpoints : List (String × String × String × Name) := []

end ZkcSecurity.Registry
