# F0-V2C: the migrated PIR owner text

> **Kind:** migration record (formal-assurance research, owner-text pass)
> **State:** Authored 2026-09-03 on the migration branch and closed by two
> independent review rounds; Section 10 then closed the five choices the
> Terminal-contract mechanization found open, and a third round reviews those
> laws; both publication compilers agree on the migrated tree; the
> identity-rotating publication and the package refreeze remain the user's
> gate.
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
5. **Mechanization of the Terminal contract.** The core-Lean transcription
   proved `AttemptedWhenever` sound for every valuation of opaque guard atoms
   and the must-fact analysis sound against the term evaluator for every
   term, and decided the contract on the frozen carriers in agreement with an
   independent Python checker. It found five choices Section 10 left without
   a unique mechanized reading, all now closed in the page: the unnamed term
   constructors contribute no literal, non-Boolean inputs carry no literal,
   a fact set with both polarities is impossible, the impossible-region test
   is a standalone clause, and step 9's forward abstract state is stated as
   closed set laws (`Region`, `Implies`, `Disjoint`, `ClaimStatus`,
   `LiveClaims`). Its one refusal is a fixture consequence: the five
   integrated carriers omit their reusable claim from every terminal claim
   set and are refused by the authored rule, so the carriers change at the
   refreeze. A third review round and a fourth mechanization increment check
   the closed laws.
6. **Holdout re-adjudication.** Against the migrated text the five cold
   holdouts give five fits and three breaks at the recorded boundaries, with
   no verdict disagreement with the earlier record or the structural-axes
   matrix. The earlier WHIR two-terminal schedule is refused by the exact
   terminal-claim rule; the lane's replacement carrier assumed guarded scope
   openings and is re-authored in the second round with unconditional
   reductions, under the syntactic guard-implication law that Section 10
   already names as this regime's boundary. The axes matrix's meaning of
   interpretation failure is stale against Section 12.4 and is corrected.
7. **Region applied to a claim source.** The third review round found
   `ClaimStatus` comparing an occurrence's `Region` against `Region(Source(c))`,
   although a claim source is a binding or a reduction output, not an
   occurrence; a child scope that opens before a guarded occurrence made a
   live claim `Unknown`. Repaired with `BoundaryRegion` over scope openings and
   `ClaimSourceRegion`; the fourth round and M5 confirmed it.
8. **An undefined reference atom.** The refreeze rehearsal found
   `PIRReference`, an arm of the static-view atomic boundary, with no
   definition. It is now the closed union of the Core-local dense-ordinal
   references, `ValueRef`, and the declaration references the selected
   profile recognizes, with its body by delegation; the fifth round found the
   arm too narrow for a family declaration kind and the sixth confirmed the
   generalized arm over all 386 reference leaves.
9. **Law-valued fields that named no declaration.** The same rehearsal
   found the five law-valued fields of the Interaction static views typed as
   exact law references with nothing selecting a declaration; the family
   pages selected most of theirs in prose but not the execution views. Each
   profile now states a `PIRStaticViewLawFieldSelection` table, nine
   declarations were added for laws that had no selector of their own, and
   the fifth round confirmed all 35 fields with stable catalog ordinals.
10. **Cross-contract defects found by the pre-freeze deep review.** The
   independent review of the stacked tree
   (`pre-freeze-deep-review-2026-09-04.md`) asked the composition question
   the page-local rounds had not: whether every producer's output is formable
   as its consumer's input. Six of its findings are repaired on these pages
   and a seventh on the Analysis text:
   - the Interface completion presentation bound the failure receipt's draws
     at a K1 root sequence of capacity `2^20`, which the Foundation's
     constitutional bounds cannot form; the draws are no longer a completion
     coordinate, the five remaining coordinates are shown total for every
     admitted construction, and the coordinate body has five failure arms;
     the draws are a derivation of the presented coordinates under the
     owner's execution and replay laws, not a fact of their own, which is
     why the presentation omits them;
   - the confidential initial-Oracle, confidential Plan-witness, and endpoint
     supplement identity constructors applied `ProfiledSemanticId` to
     family-local bodies while the profile compilers wrap those bodies in a
     family variant, two preimage equations for one subject kind; every
     constructor now applies its profile's compiler to a tagged family value,
     the compilers are written as functions of that tag, and the generic
     static-view constructors dispatch to the compiler the owner profile's
     catalog binds, so a family profile's static views are compiled by that
     profile;
   - the canonical-framed challenge-transition view carried one acceptance
     ABI, one decoder ABI, and one draw bound for a construction whose
     challenge rules may differ; it now carries one rule entry per challenge,
     with the laws shared by every rule stated once;
   - Section 13 of the canonical-framed page redefined `InfluenceAtom` as an
     occurrence-kind record; the required-influence view now carries entries
     over the Section 5.1 atom algebra under a stated static projection law,
     with one symbolic entry per earlier challenge standing for the draw
     atoms only the run counts, so the body states the complete requirement;
   - the Analysis read catalog selected `result_ref`, which the owner
     excludes from the body, and eight further names no owner body declares;
     every selection is re-authored to the owner's field names, and a
     developer-tier control joins the catalog against the owner bodies;
   - the invocation-issued public setup view promised every session and
     parameter binding's value although a binding may name an occurrence
     output; the view's entries are now exactly the invocation-determined
     bindings and its `run_established` sequence names the rest, so every
     admitted Protocol has one setup view that says what it does not fix, a
     consumer needing a fully fixed setup requires that sequence empty as its
     own premise, and the Statement-invariance law is stated exactly;
   - the family-premise source constructor received an asymptotic-family
     subject identity where a property-family declaration reference is
     required; the Analysis text now passes the declaration reference.
   The eighth finding, on the prose-pin reversal test, is the user's decision
   and is carried in the decision packet. Every repair rotates its profile,
   the re-pinning classes of Section 7 apply, and an eighth review round
   checks the repaired text against the review's reversal conditions.

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
  set in the first class. Measured again at the head closed by the fourth
  review round, 27 of 57 research checks fail and 30 pass; the additions are
  the two above, the provider interpretation, whose generator re-derives its
  certificate from the current subject and must refreeze it, and the kernel
  mechanization, which pins a sibling package's frozen findings and Section
  10 before the claim-source repair. The publication check itself fails only
  on the frozen upstream profile digests, which is the publication gate. The
  classes are unchanged, and the publication compiler's uniqueness and
  reachability checks still pass on the manifests.
  After the refreeze rehearsal was rebased and re-pinned to the closed text
  (`f0-v2c-refreeze-rehearsal.md`), the checkpoint tier stands at 59 of 62
  with three red: the publication hold, the provider interpretation, whose
  current round lives on the Analysis branch with the text it pins, and the
  terminal mechanization, re-pinned by Main whenever its inputs move.
- The cold protocol holdouts were re-adjudicated at every review round
  against the migrated Terminal contract and views: five fit, three break at
  named boundaries, no verdict changed from the first re-adjudication to the
  sixth round.
- Two defects the refreeze rehearsal (`f0-v2c-refreeze-rehearsal.md`) reported
  against an earlier base were still present after round four and are now
  repaired: `PIRReference`, an arm of the static-view atomic boundary, had no
  definition and is now the closed union of the Core-local dense-ordinal
  references, `ValueRef`, and the Section 2 declaration references, with its
  body by delegation; and the law-valued fields of the static views named no
  declaration, so each of the three profiles now states a
  `PIRStaticViewLawFieldSelection` table mapping every such field to one
  `pir.semantic-law` declaration of its catalog or, through an imported
  declaration dependency, of the Interaction profile. Nine declarations were
  added across the three manifests for laws that had no selector of their
  own (visible history, prover-view formation, replay qualification, the
  family execution and replay laws, the duplex prover-required prefix and
  checked same-Core construction); pre-existing catalog ordinals did not
  move; the profile revisions advanced. A fifth review round checks both
  repairs; both compilers accept the manifests.
- The independent review is closed at round six: the seven original
  questions and the two added for the reference atom and the law-field
  selection are affirmative on the current text
  (`f0v2c1-migration-text-review.md`). Rounds three and five each found one
  defect that the preceding round had not asked about; Section 6 records
  them and their repairs.
- The pre-freeze deep review (Section 6, item 10) reopened seven contracts
  after round seven. Its repairs rotate sixteen of eighteen profiles again
  and put the family field audit, the migration review's page pins, the
  executor's view projection, and the Analysis review's Fiat--Shamir digest
  into the first re-pinning class; an eighth review round checks the repaired
  text against the review's reversal conditions.
- Publish the identities. Only the user authorizes the identity-rotating
  publication.

## 8. Non-claims

This record establishes no theorem, property, security, provider
correspondence, or implementation conformance; it does not publish any
identity; and it does not close the F0-V3 obligations or the F2 property
premises.
