# Protocol verification in Lean

This package holds independent Lean models of zkc programs and proves claims
about the programs the compiler actually exports. Two imports connect it to the
compiler: the scalar common-source profile, and the structured profile, which
admits original protocol-stage PIR with shared helpers, participants, services,
protocol applications and repeats. Lean checks each import's typed admission;
for selected imports it proves open-process contracts from checked derivations
and local mathematical laws. Optional packages then apply ArkLib and VCVio
security theorems to those subjects.

The [formal reference](docs/README.md) defines the models, and
[support](docs/support.md) states the exact scope and assumptions of each claim.
Native compilation below the original stage is outside these claims except
where a checked rule relates a later artifact: the constructed validators of
compiled proof Entries and the executable Schnorr validator the runtime admits.
Providers and production arithmetic are outside them. Fiat–Shamir claims cover
the Schnorr family (for Schnorr, the transform of the imported interactive
verifier, the compiled proof Entry and its executable validator; for Schnorr AND
and Chaum–Pedersen, the transforms of the imported interactive verifiers) and
the transform of any validator with a round-by-round soundness certificate,
applied to the imported Sumcheck verifier and to the ideal interpretation of the
compiled Sumcheck proof Entry, under named assumptions. The Schnorr-family
claims fix the statement; the multi-round ones also cover statements chosen
after the oracle queries when the initial transcript determines them, which for
the compiled Sumcheck Entry remains a premise because the host's binding of its
vector and count inputs is not modelled. The [common](bridges/common/README.md)
and [structured](bridges/structured/README.md) bridges test the native boundary
with independent execution and negative controls.

## What is proved

| Subject | Result | Owner |
|---|---|---|
| Scalar imports | Admission and open-process contracts of exported scalar programs; Schnorr completeness, special soundness and rejection; the two-round degree-two Sumcheck bound `4 / \|F\|` | [Scalar import](docs/spec/common-source.md), [support](docs/support.md) |
| Structured import | Independent admission, declaration linking, checked primitives, maps and realizations, protocol applications and repeats | [Structured source](docs/spec/structured-source.md), [support](docs/support.md) |
| Interactive Schnorr | Verifier contracts over the actual export; an honest prover derived from checked sends; VCVio Sigma completeness, special soundness and fresh-challenge simulation | [Schnorr subject](docs/support.md#interactive-schnorr), [security integration](integrations/arklib/README.md) |
| Compiled Schnorr proof | Checked transcript-construction and participant projection rules accept the actual compiled validator; by their composed soundness, the ideal interpretation of the exported validator is the Fiat–Shamir transform of the original verifier, with a fixed-statement extraction-probability bound in the random-oracle model via VCVio | [Fiat–Shamir construction](docs/spec/fiat-shamir.md), [participant projection](docs/spec/participant-projection.md), [support](docs/support.md) |
| Executable Schnorr proof | A checked lowering rule accepts the `zkc.program/0` validator the runtime admits against that constructed validator; its meaning, with proof framing, any decoder, an instruction budget, frames and transcript custody, reflects acceptance at every budget, and the extraction bound transfers to provers of proof bytes through the general construction, projection and lowering rules, with no Entry-specific equation about the compiled program | [Executable stage](docs/spec/executable.md), [support](docs/support.md) |
| Compiled Sumcheck proofs | The same composed rules accept the actual compiled validators of the Sumcheck example, with a protocol application and a repeat, and of its composed variant, with two applications; the ideal interpretation of each is the Fiat–Shamir transform of the original verifier, for the first the source rounds followed by the multilinear check. Composed with the multi-round bound, the first's ideal interpretation accepts a false claim with probability at most `(Q + n) / \|F\|` in the random-oracle model for a fixed well-formed statement, attained on a concrete instance, and adaptively chosen statements are bounded under a determining binding; the composed variant has no security theorem | [Participant projection](docs/spec/participant-projection.md#the-compiled-sumcheck-proof-entry), [multi-round security](docs/spec/fiat-shamir-security.md#the-compiled-sumcheck-proof-entry), [support](docs/support.md) |
| Multi-round Fiat–Shamir | Soundness over typed query sites: for any validator signature with a transcript interface whose sites decode key-dependent raw answers, possibly refusing, each oracle key is charged its site's error under the site's realized decoding law (exact, masking with refusal, KoalaBear low-bit masks, BLS12-381 reduction, proof-of-work-gated and compound sites). As instances, soundness of the transform of any validator from round-by-round soundness, `(Q + budget) * error` in a random oracle on all typed histories, also for adaptively chosen statements and decoded challenges; the imported Sumcheck verifier's transform at `(Q + n) / \|F\|`, with composition theorems whose only premise about a compiled verifier is its construction equality, discharged for the compiled Sumcheck proof Entry | [Multi-round security](docs/spec/fiat-shamir-security.md#typed-query-sites), [support](docs/support.md) |
| Sigma compositions | Actual Schnorr AND and Chaum–Pedersen subjects; shared and independent witness contexts over the retained `DLog` relation; a generic shared-challenge composition theorem; VCVio completeness, special soundness and HVZK of both imported Σ-protocols, and fixed-statement Fiat–Shamir knowledge soundness of their transforms; the composed construction and projection check accepts both compiled proof Entries, whose ideal interpretations are the transforms of their original verifiers | [Sigma compositions](docs/support.md#sigma-compositions), [participant projection](docs/spec/participant-projection.md#the-compiled-sigma-proof-entries) |
| Logical contexts | Port-independent binders whose atoms transport along port maps; the existing contract layer is an instance; the Sumcheck residual bound holds on the retained and a port-repacked Reduction export | [Logical contexts](docs/design/logical-contexts.md), [support](docs/support.md) |
| Multilinear Sumcheck | Table laws for any round count; ArkLib `n / \|F\|` complete and `k / \|F\|` residual bounds | [Mathematics](docs/spec/multilinear-sumcheck.md), [security](docs/spec/multilinear-sumcheck-security.md) |
| Imported Sumcheck and Reduce | Plain verifier and prover equations; the prover's per-round fold invariant; honest-prover completeness of both actual pairs for every challenge tape that supplies the rounds; `n / \|F\|` bounds on the actual admitted roots under the uniform query service | [Verifier equations](docs/support.md#source-only-sumcheck-verifier), [honest prover](docs/support.md#honest-sumcheck-prover), [uniform queries](docs/spec/uniform-query-service.md#actual-imported-roots) |
| Authored DSL target | The imported Schnorr relation denotes discrete logarithm; two accepting transcripts yield a witness for it | [Verification](docs/spec/verification.md) |
| Clean AIR | A flat AIR export preserves its constraints and selected specification | [Clean integration](integrations/clean/README.md) |

## Architecture

- `Zkc`: typed mathematics and role-local PIR semantics, a shared multi-result
  [structured carrier](docs/design/structured-computations.md), exact refinement,
  specification certificates, protocol contracts and finite security models.
- `ZkcExamples`: actual imported programs, equivalent source forms, composed
  residual/opening clients, effectful structured endpoint examples and a
  downstream custom property.
- `ZkcTools`: executable scalar and structured references, header parser and
  declaration audit.
- [Security integration](integrations/arklib/README.md): optional ArkLib/VCVio
  consumers. The core does not import these libraries.
- [Clean integration](integrations/clean/README.md): isolated finite AIR export
  and native fixture producer; independent of protocol security consumers.

## Build and use

The [toolchain](lean-toolchain) and the three owning Lake manifests pin a coherent
Lean 4.34.1 dependency closure. See the [dependency rationale](docs/dependencies.md).
From `lean/`, `lake build` builds all maintained core libraries, examples, controls,
executables and declaration audits. The optional packages each use `lake build`
from their own directories. [Development](../docs/development/README.md) describes
Nix and the `just fetch-lean`, `just test-lean`, `just test-lean-integration`, and
`just test-lean-clean` entry points.

`just test-lean-native` additionally checks the native import and authored
specification boundary, including differential execution and negative controls.

### Verify an authored property

From the repository root, after preparing the native compiler and Lean packages:

```sh
python3 lean/bridges/common/verify.py \
  --module=example=examples/projects/schnorr/main.zkc \
  --module=schnorr=libraries/schnorr/lib.zkc --entry=example::Interactive \
  --compiler=build/compiler/zkc-compile \
  --spec=lean/bridges/common/requests/schnorr-dsl.json \
  --output=build/reports/lean/schnorr
```

A successful receipt says `verified-in-model`, records exact requested properties,
premises, source/request/certificate identities and dependency manifest identity.
An unsupported contract or an unproved correspondence remains `unresolved`.
The [verification specification](docs/spec/verification.md) explains author input,
proof generation, checked subjects and extension points.

### Reproduce from source

For an isolated build from exact dependency source checkouts, with no prior
project or dependency Lean objects:

```sh
cd lean
python3 reproduce.py --with-arklib --with-clean \
  --dependency-cache .lake/packages \
  --integration-dependency-cache integrations/arklib/.lake/packages \
  --integration-dependency-cache integrations/clean/.lake/packages \
  --output /tmp/zkc-formal-reproduction
```

Use a fresh output directory. The reproducer records source drift, toolchains,
builds, audits, standalone consumers and the Clean fixture comparison. Omit cache
arguments to fetch exact sources. The installed Lean/Std toolchain is trusted.

## Further reading

- Bridges: [common](bridges/common/README.md), [structured](bridges/structured/README.md),
  [transcript construction](bridges/construction/README.md),
  [executable](bridges/executable/README.md)
  and [participant comparison](bridges/structured/participant.md).
- [Dependencies](docs/dependencies.md) and the
  [design rationale](docs/design/protocol-verification.md).
