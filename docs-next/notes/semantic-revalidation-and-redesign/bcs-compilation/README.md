# BCS-style compilation of oracle proofs: entry contract

> **Kind:** entry contract (design program, prerequisite for the
> kernel-scope decision the peer review named)
> **State:** Executed 2026-09-03;
> `CannotAnswer/BCS-C-COMPOSITION-INCOMPLETE`, verdict `bends`.
> **Authority:** None.

## 1. The question

An interactive oracle proof becomes a succinct argument by committing every
oracle string with a vector commitment, answering the verifier's queries with
openings, and fixing the challenges by Fiat--Shamir. The peer review asked how
that compilation enters the kernel: as a construction the kernel owns, as a
composition of things it already owns, or as something outside it. The
kernel already owns the parts: an Oracle with `PublicBinding` publication
(the commitment-opening profile), Query and Answer occurrences, the
canonical-framed Fiat--Shamir construction, and a Compiler whose transitions
are checked changes that re-admit their result under a new identity. The
question is whether their composition is the compilation, exactly, and what
a theorem about the compilation binds to.

## 2. The lane's deliverables

1. **One finite oracle-proof-shaped Core.** A two-round folding protocol in
   the retained fixtures' style: the Prover publishes two `LogicalAccess`
   Oracles, the Verifier draws two Fresh challenges and queries each Oracle at
   challenge-derived indices, one Check consumes the answers, and the
   terminals follow the migrated Terminal contract. Admit it and issue its six
   views.
2. **The commitment step as a transition.** Elaborate every `LogicalAccess`
   Oracle into a `PublicBinding` Oracle under the commitment-opening profile
   with the Query and Answer occurrences becoming opening occurrences, using
   the indexed-core elaboration the repository already carries where it
   applies; admit the result as a new Core with a new identity; record the
   exact change as a Compiler transition with its re-admission, and show that
   the source Core's views and the target Core's views relate by the exact
   map the transition declares.
3. **The Fiat--Shamir step.** Form the canonical-framed construction over the
   target Core and check it with the existing same-Core construction checker;
   record the transcript declaration, required-influence, and
   challenge-transition views.
4. **Identity and cone.** Measure what rotates at each step and confirm that
   nothing in the Interaction kernel changes: the compilation is a composition
   of admitted subjects and transitions, not a new constructor.
5. **Theorem coordinates.** For a BCS-style soundness statement (state
   restoration or round-by-round soundness of the oracle proof, binding of the
   commitment, the Fiat--Shamir transform's loss), write down the exact
   coordinates an applicability judgment would carry under the named-premise
   intake: which premise binds to which owner coordinate, at which step, and
   which premises the family transport profile owns.
6. **Verdict.** Fits (the composition is the compilation and every theorem
   premise has a coordinate), bends (a named reopening condition is needed),
   or breaks (a named boundary), with the exact missing coordinate for any
   premise that has none.

## 3. Package and note

`evaluation/bcs-compilation-probe/` with a check, frozen findings, and the
usual registrations; the record is this directory's `README.md`, extended by
the lane with its evidence and its `## Handoff`. Owner pages are not edited;
underdetermined text becomes a `CannotAnswer` finding with a proposed delta.

## 4. Acceptance

`Affirmative` only when steps 1 to 4 close and step 5 assigns a coordinate to
every premise of the chosen statement; otherwise `CannotAnswer` with the list.
An affirmative result establishes that the compilation is expressible as a
composition of admitted subjects; it establishes no soundness, no binding, no
random-oracle property, and no implementation correspondence.

## 5. Order

After the migration text is reviewed, because step 1 uses the migrated
Terminal contract and views; independent of the family-instance decision,
which it does not constrain.

## 6. Answer

The owner architecture describes the right factorization:

```text
logical-oracle Fresh Core
  -> checked commitment-opening elaboration and target re-admission
  -> canonical-framed construction over that target Core
  -> same-Core Fresh/Fiat--Shamir check on the target
  -> Analysis applicability and quantitative property transport
```

No new Interaction constructor is needed. The probe nevertheless cannot return
`Affirmative/BCS-A-COMPILATION-IS-COMPOSITION`. Its package-local source and
commitment transition close at bounded research resolution, but the retained
canonical-framed executable checker cannot admit the exact migrated target
carrier. The chosen soundness statement also has three absent coordinates and
two coordinate forms with no exact published family. The frozen aggregate is
therefore `CannotAnswer`, not an inferred security or implementation result.

The verdict is **bends**: the ownership split and identity handoffs fit, while
one executable carrier bridge and explicit Analysis premise/theorem
coordinates are still required. The evidence does not show that the
Interaction kernel itself must reopen.

## 7. The finite composition witness

The package contains one exact restricted candidate with two prover-supplied
`LogicalAccess` Oracles. Each has a finite exact domain. Its eleven-occurrence
schedule publishes the first Oracle, samples a Fresh challenge, queries and
answers at that challenge modulo the Oracle domain, then repeats the pattern
for the second Oracle. One Check consumes both answers. An accepting Terminal
requires that Check to be true; the final unconditional Terminal rejects and
discharges no claims. This is the migrated Terminal shape, including the
required-Check set and final fallback rather than an old single Boolean
terminal.

Two separately organized evaluators agree on admission and on six view bodies:
five Core-owned bodies and the Fresh-Protocol-owned `ExecutionView`. The
source's logical-access influence reaches acceptance, so it is intentionally
not eligible for same-Core Fiat--Shamir.

The commitment elaborator creates a seventeen-occurrence target. It changes
both Oracles to `PublicBinding`, publishes both commitments before their
dependent challenges, maps eleven source occurrences and two answer values,
and inserts six decoding, claim-group, and opening-check effects. The accepting
Terminal closes over the original fold Check plus all four inserted checks.
The target is reconstructed independently, re-admitted under a different Core
identity, and related to the source through six declared view relations.

The retained indexed authoring layer admits a fold-depth-two, query-count-two
fiber with fourteen output occurrences. It is used only as evidence that the
finite repeated topology fits the existing authoring layer. Its schema and
live result are not compilation authority and do not enter the target Core's
identity.

## 8. Canonical-framed boundary

The existing executable checker passes its own exact seven-occurrence Oracle
control and issues all three construction views:

- transcript declaration;
- required influence; and
- challenge transition.

The same checker classifies the probe's exact migrated commitment target as
`Malformed`, before same-Core comparison, because its executable carrier is
the older bounded Core class. This is
`CannotAnswer/BCS-C-CANONICAL-FRAMED-EXACT-TARGET`. The owner text itself is
not contradicted: it requires the commitment target to be independently
admitted and then applies plain same-Core Fiat--Shamir to that target. The gap
is that the retained executable packages do not share the current migrated
carrier.

The native folding examples corroborate the intended oracle-proof schedule,
but their logical and committed Core classes are package-specific. They cannot
be substituted for the migrated target or used to manufacture an affirmative
same-Core result.

## 9. Identity and influence accounting

The restricted probe records these handoffs:

| Step | Identity effect | Checked structural fact |
|---|---|---|
| source admission | one source Core and one Fresh Protocol | two logical Oracles, two Fresh challenges, six views |
| commitment elaboration | Core identity rotates | target body differs, is independently re-admitted, and retains total source/target maps |
| target Fresh formation | new Protocol identity over the target Core | target commitment influence reaches acceptance |
| canonical-framed formation | construction and Fiat--Shamir Protocol identities rotate | both Protocol interpretations are intended to retain one literal target Core |
| Compiler intake | no additional semantic identity is asserted by this probe | Compiler would consume the PIR-owner checked transition; Compiler activation is not claimed |

Both commitment publication cones reach the accepting Terminal. The target
graph has 25 direct dependency edges. The earlier commitment's cone reaches
all later challenge, opening, Check, and Terminal coordinates; the second
reaches its own challenge/opening path and both Terminals. The Interaction
profile label is unchanged. These are package-local finite graph facts, not
owner-issued identities or a universal influence theorem.

## 10. Theorem-coordinate ledger

The chosen candidate statement is: for this exact two-round public-coin oracle
proof, a round-restoration soundness bound, commitment binding, and a classical
random-oracle Fiat--Shamir theorem with its quantitative loss imply the
corresponding bound for the compiled noninteractive protocol.

| Premise | Step | Owner coordinate | Family transport | Result |
|---|---|---|---|---|
| source round-restoration soundness | source oracle proof | none | none | missing |
| commitment binding | commitment-opening transition | none | none | missing |
| sampler adequacy | Fiat--Shamir | `AnalysisFamilyPremiseCoordinate(exact-family, SamplerAdequacy)` | Analysis Fiat--Shamir family | provisional: no exact family identity |
| oracle process | Fiat--Shamir | `AnalysisFamilyPremiseCoordinate(exact-family, OracleProcess)` | Analysis Fiat--Shamir family | provisional: no exact family identity |
| quantitative Fiat--Shamir loss | Fiat--Shamir | none | Analysis Fiat--Shamir family | missing theorem source, applicability result, and typed loss result |

The named-premise branch's proposed `analysis-model.md`, Section 4.1, lines
2085--2110, closes nine premise kinds and their admissible coordinate forms.
It names sampler adequacy and oracle process, but neither oracle-proof
round-restoration soundness nor commitment binding, and it contains no
concrete family identity for this statement. Its accompanying owner-text
record also says that no premise is proved and no identity is published.
Consequently a coordinate form is not counted as an exact coordinate.

## 11. Proposed delta

- **Owner page and section:** `docs-next/analysis/analysis-model.md`, Section
  4.1, immediately after `AnalysisNamedPremiseKind` and
  `AnalysisPremiseCoordinate`.
- **Exact change:** add named premise kinds for oracle-proof
  round-restoration soundness and commitment binding, plus one coordinate arm
  that refers to an exact prior qualified Analysis judgment. Admission must
  require the referenced judgment's exact proposition, subject tuple, model,
  polarity, profile, and live applicability authority; the round-restoration
  judgment must name the source Fresh Protocol, while the binding judgment
  must name the exact commitment profile and checked source/target
  construction. Keep sampler adequacy and oracle process under the exact
  Fiat--Shamir family. Keep the theorem source, applicability judgment, and
  typed quantitative loss as separate Analysis coordinates rather than
  treating a premise name as theorem evidence.
- **Identity effect:** the Analysis kernel profile and every direct or
  transitive dependent profile rotate. Any question, goal, support,
  proposition, or judgment that selects either new premise also rotates; PIR
  Core, commitment construction, and transcript construction identities do
  not.
- **Evidence:** `research.bcs-compilation-probe`, findings
  `BCS-C-SOUNDNESS-PREMISE-COORDINATES` and
  `BCS-C-COMPOSITION-INCOMPLETE`. The package freezes three absent coordinates
  and two family placeholders rather than accepting them.
- **Reversal condition:** do not add these kinds if independent owner review
  shows that an existing exact Analysis premise kind and coordinate already
  represent both judgments without loss of subject, model, or property
  identity, or if the selected BCS theorem classifies either item as a theorem
  conclusion rather than a consumed premise. In that case bind the existing
  coordinate explicitly and rerun this probe.

No PIR or Compiler owner-page delta is proposed. The canonical-framed page
already states the correct post-commitment same-Core boundary, and the Compiler
page already marks its foundational authority reconciliation as deferred.

## 12. Nonclaims

The affirmative subfindings are bounded structural evidence only. They do not
establish source soundness, state restoration, round-by-round soundness,
commitment correctness or security, random-oracle behavior, Fiat--Shamir
security or loss, theorem truth or applicability, compiled-protocol security,
host implementation correspondence, backend correctness, Compiler activation,
or deployment validity. No owner page or profile identity was changed.

## Handoff

Main may commit this working tree with subject:
`test: probe oracle-proof compilation as a checked composition`.

Files changed:

- added `evaluation/bcs-compilation-probe/README.md`, `run.py`, `model.py`,
  `independent.py`, `fixture.json`, and `expected-findings.json`;
- extended this entry-contract note with the evidence, verdict, premise ledger,
  proposed Analysis delta, nonclaims, and handoff;
- registered `research.bcs-compilation-probe` in `checks/manifest.json`,
  `evaluation/lifecycle.json`, and `evaluation/README.md`; and
- moved the lifecycle test pins to 58 research checks, 60 packages, and 18
  retained checks.

Validation snapshot after the alternate index included this note and every new
package file:

| Command | Exit | Wall time |
|---|---:|---:|
| focused package check | 0 | 0.68 s |
| manifest and fixture JSON syntax checks | 0 | under 0.1 s |
| alternate-index inventory validation | 0 | 0.04 s |
| alternate-index developer tier (9 checks) | 0 | 1.84 s |
| alternate-index focused registered check | 0 | 0.77 s |

Aggregate outcome: `CannotAnswer/BCS-C-COMPOSITION-INCOMPLETE`, verdict
`bends`. Three bounded subfindings are affirmative; the exact-target
canonical-framed step and theorem-coordinate step remain `CannotAnswer`.

Surprises and places where the brief was wrong or imprecise:

- the dedicated clone omits `AGENTS.md` and `.claude/CLAUDE.md`; their
  read-only primary-checkout copies were used as instructed by the private
  workflow;
- the “six Core views” are five Core-owned views plus one Protocol-owned
  `ExecutionView`;
- the existing canonical-framed checker is executable only over its older
  bounded carrier, not the migrated target Core carrier;
- the native folding package's Oracle Cores are package-specific and cannot be
  treated as migrated Core authority;
- the Compiler model says foundational authority reconciliation is deferred,
  so this probe records a Compiler-consumable owner transition but does not
  claim Compiler activation; and
- commitment opening is not a simple Query/Answer rename: the target needs
  decoded asserted answers, separate evidence, claim-group checks, opening
  checks, and acceptance closure over all of them; and
- one failed diagnostic redirection briefly created an empty
  `/tmp/bcs-report.json` before the command failed. It was deleted immediately;
  no report content or other lane artifact was written outside the clone.

The clone-local alternate index, alternate object store, and UV cache used for
validation were deleted after use. They were disposable validation state and
are not recoverable; the real Git index was never written.
