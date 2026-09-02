# F1-R formal-source package feasibility evaluator

This bounded evaluator tests the two-layer portable source-package boundary
selected provisionally by the
[formal-assurance F0 program](../../docs-next/notes/semantic-revalidation-and-redesign/formal-assurance-research/README.md).
It is an executable research falsifier, not a compiler component, current or
target semantic authority, public artifact format, formal proof, security
result, or implementation-conformance claim.

Run the focused gate from the repository root with Python 3.12+ and a Rust
toolchain:

```sh
python3 -B evaluation/formal-source-package-f1r/run.py --check
```

The runner creates every package in a temporary directory, compiles the
standalone Rust checker there, executes both checkers over the complete corpus,
compares their checker-independent results, and removes generated packages and
the binary. The producer deliberately writes pretty JSON in noncanonical
object-key order, so agreement exercises decode-and-canonicalize behavior
rather than agreement with wire order. No generated fixture or build output is
committed.

## What is under test

The required positive subject is a manually formed bounded Fresh Schnorr
verifier package containing:

- complete authentication preimages for Foundation types, Schnorr relation
  definition/model/instance, `InteractiveCore`, Fresh `Protocol`, and exact
  Protocol--relation correspondence;
- public binding, public-coin, effect, claim-reduction, execution, Protocol,
  and relation read closures;
- a one-to-one source-coordinate ledger; and
- no `ProverPlan`, live witness value, confidential carrier, mutable state, or
  causal capability.

Every fixture-only profile is explicitly namespaced `f1r-manual-*`; none is a
published target-profile identity.

Two auxiliary positive packages do not broaden the F1-R claim. They are
discriminators that make otherwise untestable mutations concrete:

- an interleaved two-reduction subject with one shared challenge; and
- a canonical Fiat--Shamir subject with exact statement/commitment transcript
  influence and typed sampling failure.

The temporary wire and identity contract is specified in
[`FORMAT.md`](FORMAT.md). The untrusted producer is
[`exporter.py`](exporter.py). [`python_checker.py`](python_checker.py) uses the
Python standard-library JSON and SHA-256 implementations but has its own schema
and canonical encoder. [`rust_checker.rs`](rust_checker.rs) uses a separately
written parser, canonical encoder, JSON Pointer evaluator, and SHA-256 with no
crate dependencies. Neither checker imports or executes the exporter, and they
share no package parser or canonical encoder.

## Current bounded result

The focused gate passes **18/18 cases**:

- 3 affirmative packages, for which both checkers independently reproduce the
  exact same root IDs, closed manifest, package ID, proposition ID, and result
  ID; and
- 15 mutations with exact expected classes and stable local research codes.

The frozen Fresh agreement controls are:

| Coordinate | Identity |
|---|---|
| contract | `sha256:008da473e9269f2881bbcd1cc7ae8ae38fa7b758d4e2d88f512686671dedccfe` |
| manifest | `sha256:83b591a623c27bab62573a223e6768633df832ae6ab0f48a19ebc7c74b2c8b0e` |
| package | `sha256:47df9f9a435f46894d4f2293768def9be2b3f414746f95cdfa7d6f1195d68b2e` |
| proposition | `sha256:5a0cedb2ac9572c1bd63fe4663a3b9e9081490dfd99f78ddcfc582d5629b17da` |
| result | `sha256:5f488dc4c64940c6bd52812e8a65b4b290f24e403821d83cf4c9e7e0ab6bab91` |

[`expected-agreements.json`](expected-agreements.json) freezes the corresponding
five identities for all three positive controls. It is a regression sentinel,
not independent evidence that the manually formed bodies match a live owner.

The mutation ledger is [`cases.json`](cases.json). It includes all nine F0
required boundaries:

| Mutation family | Required outcome |
|---|---|
| alter a canonical root body while retaining its asserted ID | `Negative/F1R-N-AUTH-ID` |
| omit a required order/read dependency | `Negative/F1R-N-MISSING-READ` |
| add a phantom provider read | `Negative/F1R-N-EXTRA-READ` |
| alias equal-valued, equal-typed occurrence coordinates | `Negative/F1R-N-COORDINATE-BINDING` |
| replace one shared challenge with two equal-valued draws | `Negative/F1R-N-SHARED-CHALLENGE` |
| reorder two interleaved occurrences | `Negative/F1R-N-EXECUTION-ORDER` |
| replay under another semantic profile | `KindMismatch/F1R-K-PROFILE` |
| omit one Fiat--Shamir transcript input | `Negative/F1R-N-MISSING-READ` |
| serialize confidential support or a causal capability | `Refused/F1R-R-EXCLUDED-SUPPORT` |

Additional controls reject a retained package ID, duplicate JSON key,
contract-level source alias, dormant read-catalog row, and protected
observation whose exact reads do not cover the manifest.

## Design findings

The provisional two-layer topology survives this bounded pass: complete
authentication preimages let an independently released checker recompute
source identities, while a separate exact read projection catches omissions,
extras, equal-content coordinate aliasing, schedule changes, challenge
duplication, and transcript-input loss.

F1-R also sharpened the minimum contract. A protected-observation name alone
is not checkable. Each protected observation must bind a nonempty exact read
set; their union must equal the required-read fixed point. The read catalog
must itself equal that closure, and source-node/pointer bindings must be
one-to-one. These are package-contract refinements inside the F0 A/S/C
topology, not evidence for a new semantic owner or a change to
`InteractiveCore`.

The common affirmative output authenticates a formed agreement proposition.
The checker name remains in the outer envelope, not in that common semantic
body. A durable Analysis result must additionally bind its validation basis,
environment, residual trust, policy, source authorities, and any capability it
mints. A caller must pin the proposition it requested; internal consistency of
another coherently formed package is not authority to substitute it.

## Exact limits and next gate

- The source bodies and reads are manual target-shaped fixtures. They are not
  emitted from admitted live owner handles and do not establish Q1 for the
  implementation. F1-R1 is the next exact-package gate; F1-I remains the live
  source-correspondence gate.
- The two checkers are diverse finite programs, not verified checkers. Their
  agreement and mutation performance are bounded evidence only.
- The package authenticates static portable values. It deliberately excludes
  live secret witnesses, confidential Oracle carriers, mutable Plan state, and
  causal capabilities.
- No provider-native formal artifact exists here. Q2 VCVio/ArkLib
  correspondence, theorem environment/truth/applicability, a cryptographic
  property, Compiler preservation, OIR projection, and realization remain
  open.
- This focused evaluator requires Rust, but it is not added to the compiler's
  ordinary semantic-check tier or dependency floor. Product integration is a
  later decision after F1-I.

F1-R1 should preserve this frozen reference corpus while replacing the manual
source bodies and selectors with exact durable target bodies and views. Its
durable identities are not expected to equal this temporary JSON package's
identities. F1-I then requires the offline exact package and the live admitted
owner-issued package to agree under the same durable contract. Any unavoidable
missing owner observation reopens F0; ordinary wire adaptation or
implementation plumbing does not.
