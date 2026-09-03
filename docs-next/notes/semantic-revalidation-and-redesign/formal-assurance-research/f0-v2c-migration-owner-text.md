# F0-V2C: the migrated PIR owner text

> **Kind:** migration record (formal-assurance research, owner-text pass)
> **State:** Authored 2026-09-03 on the migration branch; both publication
> compilers agree on the migrated tree; the identity-rotating publication and
> the package refreeze remain the user's gate.
> **Inputs:** the decision packet `f0-v2c-decision-inputs.md` (eight decisions
> taken as recommended), the Terminal contract reopening record, and the
> package records named per section below.

## 1. Outcome

The eight migration decisions are now owner text on six pages and eight
profile manifests. The candidate overlay of the migration package was the
measurement instrument; the text below was authored against the pages'
existing structure, in their voice, inside their profile-source regions, with
no research codes or digests.

| Measure | Value |
|---|---|
| Pages changed | `interactive-core.md`, `fiat-shamir.md`, `duplex-sponge-fiat-shamir.md`, `interfaces-and-plans.md`, `endpoint-projection-views.md`, `oir/projection-contract.md` |
| Manifests changed | `interaction`, `canonical-framed-fiat-shamir`, `duplex-sponge-fiat-shamir`, `public-setup`, `interface-plan`, `endpoint-source-view`, `oir-endpoint-graph`, `oir-projection-relation` |
| Compilers | reference and independent publication compilers agree on every profile of the migrated tree; only the published-table and frozen-upstream byte comparisons fail |
| Rotation cone | 17 of 18 profiles; `analysis-kernel` alone is stable |
| Interaction digest | `62464076d1ed690f…` before, `7fca29c72ba111b4…` after |

The cone is one profile larger than the candidate's sixteen because the OIR
endpoint-graph body fragment changes for the Terminal repair (Section 4).

## 2. Decision by decision

1. **Sub-decision A (A2).** Section 13.2's closure law gains the bullet that an
   algorithm, evaluation-contract, or module identity leaf closes to that
   identity alone, its authenticated preimage being part of the Core's
   admitted dependency closure that a consumer must hold; and Section 13.2
   states the formal source of an admitted Protocol for a reader outside PIR.
2. **Sub-decision B (B2).** The same paragraph says a nominal
   `pir.public-coin-law` declaration is a hook, that the distribution is
   bound by Analysis as a named premise, and that a Fiat--Shamir challenge has
   no such premise on the PIR side because Section 7 of the family page fixes
   its value operationally.
3. **Sub-decision C (C1).** Section 12.4 defines `ProtocolOutcomeLane(P)` with
   `Accepted | Rejected | Aborted | InterpretationFailed(...) | StrategyStopped
   | OperationalNoncompletion`, profile-qualified as the consistency review
   required (five lanes for Fresh and duplex-sponge, six for canonical-framed);
   `StrategyStopped` is a lane and not a completed record; the `ExecutionView`
   carries the partition as `outcome_partition`.
4. **D2's five choices.** `Published` receipts carry `fixation`, exactly
   `Fixed(origin, domain_law)` for `LogicalAccess`; `occurrence_receipts` run
   through the active terminal's occurrence inclusive; `PartialRunRecord` has
   an exact body ending in `stopped_before`; `StrategyStopped` stays outside
   `CompletedProtocolRecord`; the field name `run_record_schema` is kept, with
   `interpretation_failure_schema` and `outcome_partition` added beside it.
5. **Section 11 wording.** The transfer paragraph names the node of every
   transfer; `ChallengeTransfer` fixes lattice precedence over the complete
   dependency set; `PCSinks` enumerates the LogicalAccess publication effect
   node and both public-Query coordinates; `AcceptanceSinks` is stated by node.
   These are the readings the integrated-graph and mechanization packages
   implement, transcribed coordinate by coordinate from their code.
6. **FS-family view catalogs.** Both family pages gain a catalog of the same
   form as the Interaction catalog, an `ExecutionView` schema and body of their
   own, body-safe result-view coordinates (the owner-local result reference
   leaves the bodies), and their split envelope compilers. The eleven body
   normalizations remain to be transcribed from the F0-V3B packets
   (`evaluation/formal-source-fs-view-determinacy-f0v3/proposed/`); until then
   those fields stay prose and the F0-V3 obligations stay open.
7. **Identity pin (P2).** Identity is the prose fragment; no transcription
   pin was added. Discrepancies found while transcribing are recorded in
   Section 6 as named reopenings.
8. **Freeze scope.** Only kernel pages and their manifests changed; the
   satellite profiles rotate through the import graph and gain no new claim.

## 3. The Interaction Core page

- **6.4 Terminals.** `TerminalDecl` becomes verdict, public outputs, and three
  sorted-unique sets (`required_true_checks`, `required_applied_reductions`,
  `terminal_claims`); `ClaimDisposition` survives only as
  `DerivedClaimDisposition(verdict)`. The prose states the three obligations
  and the fallback rule.
- **10 Core admission.** Step 9 names the Terminal contract; after
  `GuardImplies` the page fixes `AttemptGuards`, `AttemptedWhenever`, the
  structural `Must`/`MustWhenTrue` law, and `TerminalContract(t)`. The
  required-Check rule holds unconditionally: the research rule's exemption for
  an impossible terminal region is dropped as strictly fail-closed (Section 6).
- **11 Public-coin eligibility.** Transfer coordinates, `ChallengeTransfer`,
  `PCSinks`, `AcceptanceSinks` as in item 5 above.
- **12.4 Records.** Item 4 above, plus the partition prose.
- **13.1--13.3 Views.** The explicit `PIRViewSchemaCatalog` with six
  `StaticViewSchema` entries, `StaticViewBody`, `PIRStaticViewFieldResolution`;
  the normalized six bodies with `PIRProverMoveType`, `PIRPCGraphResult`,
  `PIREffectOccurrenceEntry`, `PIRValueEntry`, `PIRClaimCreationCoordinate`,
  `PIRClaimUseCoordinate` (now `TerminalClaim`), `PIRFreshResolverCoordinate`,
  `PIRRuntimeSchema`; the envelope bodies of the static-view family, the
  `PIRDescriptionBody` grammar, and the `pir.source-*` compilers as closed
  variants over exactly the families the profile issues (static views and the
  confidential initial-Oracle view).
- **13.4 Public setup.** The public-setup profile's own envelope bodies as
  one-arm variants.
- **Appendix A.** `TerminalBody` with five fields; `ClaimDispositionBody`
  removed.

## 4. Dependent pages

- **Interface/Plan.** A two-family envelope split: the interface-correspondence
  view (no-policy) and the confidential Plan witness view (bound policy), with
  the interface view's payload, requirement, no-policy, and closure bodies.
- **Endpoint.** One-arm variants over the supplement family; the anchored
  obligation's terminal arm carries the three sorted-unique sets and the
  required-reference sentence names them.
- **OIR projection contract.** Item 7 and the endpoint terminal body carry
  required reductions and terminal claims; the disposition bodies are removed.
  This changes the `oir-endpoint-graph-bodies` fragment, so the endpoint-graph
  profile rotates.
- **Canonical-framed and duplex-sponge.** Catalogs, execution-view bodies,
  body-safe result coordinates, envelope splits (Section 2, item 6).

## 5. Manifests

Eight manifests were edited by minimal style-preserving deltas and verified by
parsing the edited text back and comparing it with the intended object.
Interaction: revision 1; sixteen new declarations (six view schemas, the
generic view body, the resolution law, three kernel laws, six source
compilers replacing the shared envelope compiler); the six source subjects
re-pointed. Each dependent profile compiles its own four envelope subjects and
imports the Interaction role compilers. Both Fiat--Shamir source-views laws
carry their five schema declarations as dependencies so that the schemas are
reachable, the OIR profiles bump the revisions of the changed body and law.

## 6. Reopenings and defects found while authoring

1. **Impossible-region exemption dropped.** The research rule exempted a
   terminal whose region is impossible from the must-fact requirement; the
   owner text requires the must-fact unconditionally. Any frozen carrier that
   relied on the exemption would now be refused; the terminal-projection and
   integrated-graph refreezes must report whether one exists.
2. **The Schnorr subject declares no claims.** F2-P1 could bind every
   Relations and Plan candidate except the initial-claim meaning, because the
   admitted Schnorr Protocol has an empty claim table. Either the fixture gains
   an initial claim at its refreeze, or the Relations contract admits a
   claim-free binding; this is decided with the fixture refreeze.
3. **OIR endpoint-graph rotation.** The Terminal repair reaches the OIR body
   grammar, so the cone is seventeen profiles, not sixteen.

## 7. What remains before publication

- Transcribe the eleven Fiat--Shamir body families from the F0-V3B packets
  into owner prose on both family pages.
- Refreeze the source-pinning packages against the migrated text. The overlay
  measurement found 21 of 52 research checks pinned to the migrated bytes; the
  authored text is being measured the same way and its set is recorded in the
  lane register.
- Rerun the cold protocol holdouts against the migrated Terminal contract and
  views.
- Take the independent freeze review's findings (a verification lane is
  reviewing the exact diff) into this text.
- Publish the identities. Only the user authorizes the identity-rotating
  publication.

## 8. Non-claims

This record establishes no theorem, property, security, provider
correspondence, or implementation conformance; it does not publish any
identity; and it does not close the F0-V3 obligations or the F2 property
premises.
