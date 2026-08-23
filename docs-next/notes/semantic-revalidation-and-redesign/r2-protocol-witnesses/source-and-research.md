# FRI-Grind-1 Source Reconstruction and Primary Research

> **Kind:** Temporary R2 evidence and research record
> **State:** Active; no target-semantic or theorem authority
> **Boundary:** Public repository and primary sources only; no private review text is reproduced.
> **Charter:** [R2 Real-Protocol Witness Program](README.md)

The first lean refreeze reproduced exactly but failed cold semantic closure.
The authority-centered repair recorded in the adjacent
[cold review and repair decision](cold-review-and-repair.md) now passes its
repaired refreeze and context-isolated non-authoring replay. The first output
remains failed-witness evidence; the passing result closes only this finite
FRI-grinding witness and does not promote the research deductions below into
target or theorem authority.

## 1. Frozen repository evidence

The fixture and current generator were inspected on branch `feat/value-profiles` at commit
`6cea581c45dffe48f8ee1123c8066f10aa650d73`.

| Evidence | SHA-256 | Boundary |
|---|---|---|
| `test/Family/Inputs/frigrind.json` | `cf2e4effc006cae253a77a9f8e0a0d0a3fe024bf3d6af99a75801d4b4765426a` | Authored family fixture |
| Generated current vocabulary | `32e3cab87e1a52adb3f0d752861636a6ff3c5f20d9389b5fa29ffc2fb5f04c95` | Frozen generated-output hash for drift validation; 5,366 bytes |
| Generated current spine | `c19f0ca2e28b9f8a6cbe99f46969e11d663ca76010677070bc7d285c764ede54` | Frozen generated-output hash for drift validation; 17 lines, 2,341 bytes |
| `test/Soundness/Inputs/frigrind-bound.json` | `317258c54a4b8dad0308f552adc2bf0f8ec4fc72ecc5dc765f4ad206c9503858` | Companion with one relation-anchor projection occurrence |
| Generated companion spine | `2b915f6637d1828ca6bcc3f9f74970652f8c7cb32f1a2eb739ee9cbe6f6e1f5d` | Frozen companion-output hash for drift validation only |

The generated artifacts came from the live `build/bin/zkc-family` in an
ephemeral directory. Their hashes freeze the inspected output; they are neither
target inputs nor copied evidence. They detect validation drift; source digests
do not define semantic identity or prove equivalence. “Recovered” below means
present in these objects. “Theorem premise,” “convention,” “local choice,” and
“open” never inherit authority from one another.

The authored fixture fixes field modulus
`340282366762482138490186164457219031041`, query space `2^10`, grinding space
`2^16`, two query draws, `toy_duplex` with `artifact-id` initialization,
`ts_be8` for `pow_value`/`query_index`/`rs`, `ts_be32` for `ext_field`, one
contract and one statement anchor, and Johnson parameters `m=3`, `eta=1/256`,
`delta=9/10`.

The generated spine binds public `f_root` before `fold1`; receives `g1` and
`nonce`; derives `pow` from the monotone prefix through the nonce; checks
`pow==0`; draws two queries after `pow`; performs a toy `f_root==g1` check;
routes FRI then grinding reductions; binds `f_root` to the statement anchor;
and ends at `fri-terminal-not-modeled`. The equality is not a FRI fold law.
There is no opening, authentication, fold-consistency, final-degree, or terminal
acceptance semantics.

## 2. Relation and anchor reconstruction

The contract anchor names a relation lane; the statement anchor names the
public-instance lane; statement slot zero corresponds to `f_root`. The base
fixture material-binds only the statement anchor. Carrying the contract anchor
inside an opaque claim establishes neither relation identity nor authenticated
source meaning or transcript influence.

The fixture supplies an anchor reference and a Protocol Statement occurrence,
but no independently identified relation-side public value. The affirmative
result frozen by the first executable is therefore withdrawn; repair must
return `MissingDependency`. A future positive pointwise bridge requires a
Statement occurrence extracted from a qualified execution, an independently
identified relation-side operand, and an explicit typed map between them. Even
that would not establish a whole-domain embedding, isomorphism, or
source-authentication result.

The companion exposes one frozen 256-to-216-bit contract-anchor projection.
It challenges three deliberately disjoint lanes: exact-domain isomorphism;
injective embedding with an image predicate and inverse on the image; and a
lossy directional projection with authenticated source bytes, collision
relation, exact occurrence ledger, and Analysis loss. Equal projected limbs do
not imply equal digests or meanings. A digest-shaped reference does not supply
the byte preimage required by a byte-string reduction. The grinding nonce is
protocol-local strategy output, not automatically a relation witness.

## 3. Primary-source deductions

### Original FRI

Original FRI separates commit and query phases. Each current oracle exists
before the verifier coin defining the next oracle; terminal coefficients are
sent and reconstruct the terminal function before the random base query. It is
an IOPP with direct oracle access, not a Merkle-root/opening protocol. Its main
theorem is limited to the stated Reed--Solomon family, rate, localization,
field or smooth-domain conditions, distance, and query parameters. It proves a
probabilistic proximity claim for initial oracle `f^(0)`; it neither derives
that oracle from public `f_root` nor proves an outer AIR/R1CS computation.

Source: Ben-Sasson, Bentov, Horesh, and Riabzev,
[Fast Reed-Solomon Interactive Oracle Proofs of Proximity](https://eccc.weizmann.ac.il/report/2017/134/).

### BCS and Fiat--Shamir

BCS assumes public-coin normal form, uniform verifier messages, a stateless
verifier, and oracle queries postponed until after interaction. Section 6 uses

```text
sigma_0 = rho_2(x)
m_i = rho_1(x || sigma_{i-1}); receive f_i; commit it as rt_i
sigma_i = rho_2(rt_i || sigma_{i-1})
r = rho_1(x || sigma_k); derive queries; select their authentication paths
```

Thus instance `x` is explicit in every `rho_1` verifier-message/final-randomness
derivation and remains upstream of intervening `rho_2` updates; every root is
upstream of final query randomness. Paths are chosen after query positions;
their joint packaging in a noninteractive proof does not change causality. BCS
uses restricted state restoration, not unchanged interactive soundness:
Theorem 7.1 gives
`s'(x,m,lambda)=sbar_sr(x,m)+3(m^2+1)2^-lambda`, with prior seen states but not
the empty verifier state restorable after the first iteration.

Source: Ben-Sasson, Chiesa, and Spooner,
[Interactive Oracle Proofs](https://eprint.iacr.org/2016/116).

Static and adaptive claims are not interchangeable. For adaptive statements,
AFK keeps `x` in every random-oracle call, including
the chained form; it does not prove generic absorb-once sponge equivalence. An
initial persistent-state binding instead needs its own injective/authenticated
encoding, transcript-state binding, and collision/reduction argument. Domain
separation alone is insufficient.

Source: Attema, Fehr, and Klooß,
[Fiat-Shamir Transformation of Multi-Round Interactive Proofs](https://eprint.iacr.org/2021/1377).

Public-coin eligibility is only a starting premise. Block et al. Theorem 3.15
gives the classical-ROM form
`epsilon_FS(x,Q,kappa)=Q*epsilon_RBR(x)+3(Q^2+1)2^-kappa`. Their FRI-specific
Theorem 4.1 establishes RBR only under its field, smooth-subgroup, rate, degree,
proximity, and query-count premises; Corollary 4.3 then applies BCS. QROM and
proof-length accounting are further layers. None of these results transports
ordinary interactive soundness losslessly.

Source: Block, Garreta, Katz, Thaler, Tiwari, and Zając,
[Fiat-Shamir Security of FRI and Related SNARKs](https://eprint.iacr.org/2023/1071).

### Grinding

Grinding protects a selected round, not an undifferentiated number of security
bits. The nonce must bind the prior transcript and precede the protected
randomness. Query grinding reduces the protected query term, not independent
field-size, outer-protocol, or random-oracle collision terms. ethSTARK Theorem
6 scales the selected RBR component while Theorem 8 retains a separate
collision term; Section 3.11.3 places the nonce after prior commitments and
before query randomness. Block--Tiwari changes `(1-delta)^ell` to
`(1-delta)^ell*2^-z`; earlier fold/field and collision terms remain.

Sources: StarkWare,
[ethSTARK Documentation 1.2](https://eprint.iacr.org/2021/582), and Block and
Tiwari, [On the Concrete Security of Non-interactive FRI](https://eprint.iacr.org/2024/1161).

These sources determine possible theorem premises and Analysis obligations.
They do not turn a deterministic support-point fixture into evidence that
uniformity, independence, non-anticipation, ROM behavior, or any cited theorem
premise holds.

## 4. Consequences and open boundary

The durable model requires a strategy-parameterized execution relation and an
Analysis quantifier over an admitted causal strategy class. This R2 probe
instantiates one fixed strategy contract per `ScenarioVariant` and checks only
its declared reads and previews against Core order; it does not model arbitrary
or adaptive adversaries.

The witness otherwise requires typed Statements; derived public-coin
eligibility; distinct logical oracles, roots, draws, draw-selected evidence, and
terminal material; draw multiplicity separate from deduplicated openings;
closed identity/evaluation contracts; and separate admission, execution,
correspondence, theorem, and Analysis results. It does not select a universal
ABI, sponge, tree, cap, codec, sampler, grinding profile, or
same-versus-distinct subject policy. Runtime-profile binding is a local
cross-profile obligation; instance binding is theorem/profile-specific.

The repair separates `InputBundleId`, which names the Statement and base prover
inputs, from `ExecutionRequestId`, which binds the scenario, semantic
application context, evaluator basis, realization-local controls, resources,
`CoreDerivationKind`, source fixture, and source package. Admission reconstructs
the package, requires its exact `InputBundle`, and requires either the exact
fixture grinding Core or its exact drop-grinding projection. Request-local
search may intentionally override the package default.

`ApplicationContextId` is intentional semantic FS initialization; changing it
is expected to rotate challenges. Evaluator, source, resource, and search
identities remain validation/provenance controls. Evaluator source digests are
drift evidence, not semantic identities or proofs. The evaluator basis also
binds request-execution caps and separate qualification caps; qualification
pre-admits and records aggregate target-plus-dependency replay work.

Fresh declares Core-derived coin slots, sequential reveal,
conditional-uniformity, and no-future-access laws. The external artifact
demonstrates one valid non-FS-derived support point and no FS-record dependency;
it does not validate the distribution law or artifact-authoring chronology.
FS-coupled Fresh tapes remain separately identified comparison evidence.

The finite witness supports one explicit `SemanticRegimeId` and one local closed
finite-term ABI: null, booleans, integers, UTF-8 text, bytes, canonical
sequences, and sorted string-keyed maps under tagged length-delimited encoding
and explicit byte, node, and depth bounds. Identities bind the regime, an ASCII
domain, and the encoded preimage; unsupported regimes are rejected. This does
not select a universal v0 ABI.

The executable reports no event mass or search-success probability. Such
quantities require a separately admitted random experiment and justified
uniformity, independence, or random-oracle assumptions; neither the external
support point nor deterministic FS replay discharges them. R2 records only
structural ordering, exact finite outcomes, and explicit dependencies. Bounded
FS search exhaustion yields prover `Abort`; a nonzero Fresh pow value yields
verifier `Reject`. Immediate rejection is a witness-local short circuit, not
paper-trace equivalence.

At most, aligned typed challenge words can make mapped source checks, routes,
failures, and the residual commute. That is not protocol equality,
probabilistic bisimulation, FS security, property transport, or theorem
applicability.

The source residual cannot decide native IOP/IOR openings, complete FRI,
outer-relation reduction, general Relations grounding, composition, recursion,
ROM/QROM applicability, or final architecture. Those require later witnesses
or R3 research, not a locally invented accepting completion.
