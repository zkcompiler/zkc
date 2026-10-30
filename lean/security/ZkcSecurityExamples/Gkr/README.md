# GKR canonical claims

The canonical subject fixes the actual authored pair and the registered
`circuit_outputs` target. The source verifier, honest producer, compiled
correspondence and claim receipts use that same pair. The mathematical circuit
is `Zkc.Protocols.Gkr.Circuit`; it is independent of the producer's working
arrays and proof messages.

## Independent target and admission

`RootEncoding` derives the input/output decoding, wiring blocks, selector
capacity and machine bounds from `CircuitEncoding.Admitted`. Its output
predicate is `CircuitEncoding.Outputs`. A malformed circuit shape has a false
target, including unused malformed wiring at zero layers. A shape-valid false
output remains admitted.

`ZkcExamples.Construction.Generated.GkrPair` retains the current native producer
and validator exports in the core examples package.
`Canonical` and `Generated.Subject` select the source's registered output
clause through `Relations.registry`. `Canonical.holds_all` identifies its
meaning for every typed adversarial statement. Soundness reads the actual
validator's seven public inputs. The honest-input policy supplies circuit
admission and role agreement for completeness.

## Actual source and compiled correspondence

`GkrSourceAdmission` accounts for every raw admission branch. `SourceRoot`
composes those branches with the source-reading theorem and the existing GKR
component soundness laws; `SourceValidator` supplies the complete validator
process, including malformed inputs and stopped helpers. `CanonicalSource` gives fixed-target
rejection for all typed public statements without a supplied representation.
The generated normal forms use the current eight-input Pending ABI, including
the prefix carried into the right rounds, and the actual terminal input call.

`ZkcExamples.Structured.Generated.Connections.Gkr` supplies both production
`RootCertificate`s, independent
reached-source coverage, full source/physical returns, history, frames and the
method-independent `Connected` propositions. `CanonicalInstallation` consumes
`RootConnection.claimsInstallation` and its public-source losslessness rule.
The shared reading/coherence and checked endpoint selection supply acceptance
agreement. The source ABI fixes the selected validator capability at coordinate
7; it is not an arbitrary caller-selected handle.

`CanonicalReading` uses `RootConnection.publicPresentation` directly. Its
constant-price rejection and pathwise costs reuse the scalar mathematics through
`FiatShamir.FieldSourceProperties`, a generic theorem for field-only exchanges.
A finite `FieldSourceSupport` check establishes that premise from source syntax.
This transports properties to the ordinary nominal presentation; root coverage,
reading and the full compiled simulation remain independently checked. It does
not introduce another typed simulation wrapper or an assumed routing law.

`CanonicalVerifier` associates the nominal validator with the mathematical
honest replay. `CanonicalReadback.actual` relates the actual source producer to
that validator: the producer computes its proof, both sides share the exact
history, and both full source returns remain in the postcondition. Its premises
are independent admission and circuit outputs. `CanonicalConnection` reuses this
mathematics at the production root ABI. Role masking and template filtering use
generic, kernel-checked congruence laws in `OriginalRoutingCongruence`.
`CanonicalCompleteness` transports that pair through both root certificates and
selects acceptance only after obtaining both `CompleteReturns` facts.

The old `OriginalCertificates`, GKR-specific compiled callback/frame equations,
their duplicate validator and alternate layout views, the old occurrence-reading
route, and the GKR-specific connection driver/templates are removed. The
coordinate refusal tests now use the source templates directly. The alternate
layout's pure syntax/provenance controls remain; no alternate full connection
or native byte association is claimed here.

This migration preserves the circuit/layer and Sumcheck mathematics. Scalar
mathematical presentations are derived from the single Structured meaning;
the independent Common frontend is retired. Shared Lean role-view generation
replaces the four Python GKR presentations. Remaining helper, reference and
honest-source proofs still count as authored work: removing the compiled
linkage and generator does not establish zero mechanical proof overhead.
Core connection generation is selected
in `Tests.ConnectionGeneration`; both artifact views use
`Tests.Constructed.Generate`. The common printers own the emitted proof syntax.
The retired GKR-specific generator manifests are no longer current ownership
records; the landing account measures authored and generated work separately.

## Generated endpoints

`checks/GenerateGkrCanonical.lean` uses the shared fixed-subject, ABI,
soundness, completeness and registration printers. `Generated.ABI` fixes
public positions, role projections and public-binding history before evidence
is supplied. `CanonicalPolicy` proves independent target and admission laws at
that ABI and supplies an admitted nonvacuous circuit.

`CanonicalSoundness` gives the charged export at the four actual selected
challenge sites. Each site has price `4 / cardinality(bls12-381.fr)`. The
validator has at most 40 draws, and the scalar adaptive bound is
`4 * (Q + 40) / cardinality(bls12-381.fr)`. `CanonicalCompleteness` transports
the actual producer's readback through both shared root connections and proves
perfect compiled-ideal completeness.

The scalar and charged soundness requests are authored in
`examples/projects/gkr/main.zkc`. The common subject driver binds the native
source export to the unchanged original/participant bytes and emits
`Generated.SubjectSoundnessClaims` through the configured typed library.
There is no GKR request-construction script. The library computes the fixed
meaning before applying a proof; the source method cannot select another
subject or weaker property. The separately generated perfect-completeness
request remains in `Generated.SubjectCompletenessClaims`.

## Validation and maintained consumers

`TestsSecurity.GkrCanonicalClaims` checks the complete, scalar-sound and
charged-sound receipt clients for the same fixed subject. Its controls reject
a zero-error soundness request and a different retained target.
`TestsSecurity.GkrCanonical` includes actual producer-generated proof controls,
false outputs and malformed wiring. `GkrRootEncoding`, `GkrSourceAdmission`,
`GkrSourceRoot` and `GkrCurrentReading` cover admission and current source
contracts. These controls supplement the universal theorems.

The maintained coordinate-erased whole compiled route remains available
through `GkrProof.compiled_transform` and the ArkLib compiled GKR soundness
consumers. Its current bodies and imports are
ported directly. Superseded normal-form modules are replaced, without
compatibility aliases. The protection ledger records the selected theorem
statements; source and compiled artifact identities require separate exact
association and receipt checks.
