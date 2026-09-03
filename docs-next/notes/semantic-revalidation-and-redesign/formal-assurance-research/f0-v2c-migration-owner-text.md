# F0-V2C: the migrated PIR owner text

> **Kind:** migration record (formal-assurance research, owner-text pass)
> **State:** Authored 2026-09-03 on the migration branch and closed by two
> independent review rounds; both publication compilers agree on the migrated
> tree; the identity-rotating publication and the package refreeze remain the
> user's gate.
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
   leaves the bodies), their split envelope compilers, and the eight view
   bodies normalized from the F0-V3B packets
   (`evaluation/formal-source-fs-view-determinacy-f0v3/proposed/`): every
   field is an exact identity, value, natural, closed tag, law reference, or
   record or sequence of those. Where the packets chose an opaque canonical
   value for a field the page already types as a declaration reference (the
   application domain), the page's reference is kept; the packets' frozen
   schema digests therefore describe the candidate and not this text, and
   the F0-V3 refreeze reads the page.
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
4. **First freeze-review round.** The independent review of the first
   migration head found the Section 10 laws not executable as written: it
   named guards for scope openings that Section 4.4 makes deterministic and
   unguarded, used undefined guard accessors, specified `let` by prose
   substitution, and described the liveness argument in the wrong direction;
   it also found `AdmittedModuleEffectAtom` used without an owner definition.
   All of these are repaired in the page (`AttemptGuards` is the occurrence's
   own guard, `GuardInputs` and `GuardTerm` are defined, `Must` runs over the
   de Bruijn environment, an impossible `MustWhenTrue` region is refused, and
   the module-effect atom is defined with boundary arm 9). The review's finite
   oracle found no counterexample to `AttemptedWhenever` over the opaque-guard
   abstraction and confirmed that dropping the impossible-region exemption
   refuses none of the frozen positive carriers. Its family-body finding
   described the first head, before the eight bodies were normalized; the
   second round re-checks closure of the normalized bodies.
5. **Holdout re-adjudication.** Against the migrated text the five cold
   holdouts give five fits and three breaks at the recorded boundaries, with
   no verdict disagreement with the earlier record or the structural-axes
   matrix. The earlier WHIR two-terminal schedule is refused by the exact
   terminal-claim rule; the lane's replacement carrier assumed guarded scope
   openings and is re-authored in the second round with unconditional
   reductions, under the syntactic guard-implication law that Section 10
   already names as this regime's boundary. The axes matrix's meaning of
   interpretation failure is stale against Section 12.4 and is corrected.

## 7. What remains before publication

- Refreeze the source-pinning packages against the migrated text. With the
  authored text in place, 22 of 53 research checks fail: the overlay
  measurement's 21 plus the terminal owner-contracts package, whose rule the
  owner text tightens (Section 6, item 1). The 31 kernel and instrument checks
  stay green. The failures fall into three classes: packages that pin page
  bytes or admitted identities and only need re-pinning under the published
  identities; packages whose synthetic profile overlays now collide with the
  real manifests, which must read the published manifests instead; and
  packages whose models transcribe page text (the constructor census, the
  family field audit, the terminal owner-contract gap demonstration), which
  must be updated to the authored text. None of the failures indicates a
  defect in the text: the publication compiler's own uniqueness and
  reachability checks pass on the new manifests.
  Research checks integrated after that measurement that pin the Interaction
  page, the structural-axes matrix and the family-instance probe, join the
  set in the first class.
- Rerun the cold protocol holdouts against the migrated Terminal contract and
  views.
- The second review round is closed: all seven questions are affirmative on
  the repaired text, every family-body field is exact, and the five
  deviations from the candidate packets are upheld. No owner-page delta
  remains from the review.
- Publish the identities. Only the user authorizes the identity-rotating
  publication.

## 8. Non-claims

This record establishes no theorem, property, security, provider
correspondence, or implementation conformance; it does not publish any
identity; and it does not close the F0-V3 obligations or the F2 property
premises.
