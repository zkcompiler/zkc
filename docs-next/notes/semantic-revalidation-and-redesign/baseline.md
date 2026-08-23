# R0 Live Baseline

> **Document kind:** Temporary reconstruction record
> **Document state:** Active
> **Owner:** `project`
> **Authority:** None. This page freezes the observed input to R1; it changes
> no target contract, current authority, implementation claim, or Stage 4B
> state.
> **Observed:** 2026-08-23T02:54:05+09:00
> **Disposition:** Retain until the cycle's conclusions and provenance have
> durable owners, then delete with this package.

## Checkout and authority

| Item | Frozen value |
|---|---|
| Branch | `feat/value-profiles` |
| HEAD | `6cea581c45dffe48f8ee1123c8066f10aa650d73` |
| `docs-next` tree digest | `2ce9cc2fbbc0205685dab15c9049b4bc3f03941103eaaf93a2c41f0313a460d1` |
| Program position | Stages 0--4A recorded complete; Stage 4B inactive |
| Current authority | `docs/`; `docs-next` remains a non-authoritative target workspace |

The tree digest is SHA-256 over the sorted output of `sha256sum` for every
Markdown path under `docs-next/`, before this page and the activation-header
edits were added. It names the input snapshot, not a claim that the workspace
will remain unchanged.

## Corpus boundary

| Surface | Pages | Lines |
|---|---:|---:|
| Entire `docs-next` snapshot | 113 | 75,767 |
| Durable manifest | 37 | 23,833 |
| Durable pages outside `notes/` | 36 | 23,689 |
| Temporary notes | 76 | 51,934 |
| Physical `notes/` tree, including its durable index | 77 | 52,078 |

The durable manifest is enumeratively exact: its 37 unique entries correspond
to the 37 durable pages, and their kind and owner fields match the page
headers. The historical Stage 4A count of 112 pages was correct for its frozen
snapshot; the revalidation charter created page 113. Historical audit counts
are therefore not rewritten.

One manifest-listed page, `pir/protocol-lifecycle.md`, is explicitly
superseded but retained as historical evidence. The active target surface is
thirteen semantic specifications: four PIR, two Relations, four Analysis, and
three Compiler pages.

## Version-control boundary

| State | Live result |
|---|---:|
| Tracked live files under `docs-next` | 13 |
| Tracked deletions under `docs-next` | 2 |
| Untracked files under `docs-next` | 100 |
| Lines in those untracked files | 73,206 |

All 77 physical files under `docs-next/notes/` are untracked. The workspace's
deletion rationale currently assumes that Git history preserves temporary
records, so that premise is false for the live checkout. This is a preservation
and cutover blocker, not evidence that either the current `docs/` corpus or the
non-authoritative target is presently a second normative truth. No staging,
commit, branch change, or cleanup is authorized by this record. The unrelated
dirty change in `emit/Cargo.lock` remains user-owned and out of scope.

## Review inputs

| Input | Lines | SHA-256 | Handling |
|---|---:|---|---|
| Private review note | 831 | `144232423206798c4c644e2ba112b8087417cfb32e9df31891c85cbee50be0e1` | Falsification input only; never copied verbatim into the tracked corpus |
| Attached companion review | 414 | `ec8e91faa011d61f8e25ecc71f393eadd1289d07be9d2ae0a8991011f699d59d` | External input; independently adjudicate every claim |
| Cycle charter at activation | 132 | `ca6c2441f448592e587b1946e310030ff75f97d0b924a02ac491897c130c0cd5` | Agreed method, no semantic authority |
| Durable documentation manifest | 82 | `72dd7791408369029047fe27f6a17c9ef1789c2b087bd0b94d64dcc006ea00e2` | Workspace inventory only |

Private material is consulted under `docs/private/README.md`: R1 records
independently reconstructed evidence and neutral conclusions, not review prose
or competitive framing.

## Frozen research artifacts

The principal Stage 3 and Stage 4A target, candidate, scenario, matrix,
convergence, and peer-reconciliation artifacts still match the hashes recorded
by their own exit audits. The fourteen Stage 4A promoted semantic pages and two
peer pages also match that audit's recorded hashes. Later Stage 4A promotion
changed three Stage 3 downstream index pages; those old index hashes are
historical snapshot evidence rather than live-tree assertions.

This establishes preservation of the recorded research inputs. It does not
independently validate their conclusions.

## Closure findings at R0

- No durable page links directly to an individual temporary note. Durable
  navigation reaches only the durable `notes/README.md` boundary.
- `realization/README.md` nevertheless relies semantically on
  `BelowOirPlanBasis` and `CheckedBelowOirPlanPlacement`, whose exact identity,
  result ABI, and checker contract exist only in the inactive Stage 4B entry
  note. This is a durable-closure and future-cutover defect, not a violation of
  the manifest's exactly-once enumeration rule.
- All 113 frozen pages had one H1, a final newline, and no trailing whitespace.
  Structural hygiene says nothing about semantic adequacy.

## R0 non-claims

This baseline establishes the observed corpus, provenance boundary, authority
firewall, and frozen-input integrity. It establishes no vocabulary
completeness, real-protocol inhabitance, clean-room implementability,
Fiat--Shamir adequacy, theorem applicability, implementation conformance, or
security property. Those are R1 and later questions.
