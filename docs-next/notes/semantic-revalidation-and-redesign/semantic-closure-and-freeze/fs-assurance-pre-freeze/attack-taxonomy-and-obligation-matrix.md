# Fiat--Shamir Attack Taxonomy and Obligation Matrix

> **Kind:** Temporary source-to-obligation research record
> **Baseline:** 808ec2d575da126f1d5cb22ad050ca52696dd75e
> **Authority:** None
> **Interpretation rule:** A listed defense is only the named structural,
> analytic, projection, or realization defense. It is not a security claim.

## 1. Reading the matrix

Fiat--Shamir failures are often grouped under one phrase such as “the
transcript was incomplete.” That is too coarse for architecture. The attacker
may receive freedom at five different boundaries:

1. **declaration freedom:** an application Statement is absent before the
   protocol is formed;
2. **schedule freedom:** a declared value is omitted, delayed, duplicated, or
   reordered around a challenge;
3. **representation freedom:** distinct logical values share one encoded
   query;
4. **transition freedom:** a concrete adapter or state update loses a
   distinction that the logical encoding retained; or
5. **proof-model freedom:** the implementation is faithful, but the selected
   theorem, source property, oracle model, or quantitative premise is absent.

Projection, parsing, deployment, and cross-session composition can reintroduce
the same freedoms after the source protocol is correct. The matrix therefore
uses ten assurance layers rather than one transcript-validity bit.

The executable references below point to the bounded
[pressure instrument](../../../../../evaluation/fs-assurance-pre-freeze/README.md).
Its aliases and mutations are finite class witnesses. They are not
reproductions of deployed exploits.

## 2. Attack-to-obligation matrix

| Case | Bug family and violated condition | Attacker freedom | Current zkc defense | Residual obligation | Executable case and source |
|---|---|---|---|---|---|
| FS-A01 | Weak FS / Frozen Heart: the complete application Statement is not bound before the first dependent challenge | Select or alter a public instance after observing a challenge, or prove a claim under a different instance boundary | Canonical PIR absorbs every declared Statement binding at scope opening; Interface admission covers every Core Statement binding; Relations can require exact whole selected Statement correspondence | The application or consumer must supply the expected closed Statement surface. No semantic layer can infer an external fact omitted from the admitted Core itself | Bounded weak authored schedule versus closed manifest; [BPW](https://eprint.iacr.org/2016/771), [Weak FS Attacks](https://eprint.iacr.org/2023/691), [Frozen Heart](https://blog.trailofbits.com/2022/04/18/the-frozen-heart-vulnerability-in-plonk/) |
| FS-A02 | Missing prior prover message: a challenge does not depend on every active earlier prover-controlled value | Choose the omitted message after learning the challenge | Derived occurrence actions are fixed by InteractiveCore; DerivedPrefix is the exact complete pre-draw transition-input log; runtime equality rejects omission, injection, substitution, duplication, and reordering | Analysis must still show that the concrete transition binds distinct inputs, and Realization must show that code follows the transition | Bounded omitted-frame mutation; [Fiat--Shamir in the Wild](https://eprint.iacr.org/2024/1565), [Plonky3 missing openings](https://github.com/Plonky3/Plonky3/security/advisories/GHSA-vrmm-4mm5-38vm) |
| FS-A03 | Last-Challenge family: final proof elements are not committed before a batching or aggregation challenge | Choose final openings or batching terms after observing the challenge intended to randomize them | Core order includes every prior active action; reduction required-publication rules can require exact publication atoms at the least following challenge; DerivedPrefix closes the actual prefix | The protocol-specific reduction or theorem profile must identify which final elements the challenge must bind; structural chronology cannot invent a missing mathematical dependency | Bounded early batching-challenge mutation; [Last Challenge Attack](https://eprint.iacr.org/2024/398) |
| FS-A04 | Ambiguous concatenation: typed tuples lose field, type, or length boundaries before the primitive | Substitute a distinct logical transcript with the same byte string | PIR has typed owner-qualified frames and canonical semantic values; Foundation canonical encoding separates the logical bodies | Analysis must establish total, canonical, injective query encoding for the theorem domain; Realization must validate the exact concrete codec and reject noncanonical encodings | Bounded a-plus-bc versus ab-plus-c alias; [CFRG draft 03](https://www.ietf.org/archive/id/draft-irtf-cfrg-fiat-shamir-03.txt), [Fiat--Shamir in the Wild](https://eprint.iacr.org/2024/1565) |
| FS-A05 | Missing length marker / trailing-zero alias: absent limbs and explicit zero limbs induce the same transition input | Extend or shorten a transcript without changing the challenge state | Exact algorithm identity and frame presence prevent silent algorithm substitution, but PIR intentionally makes no transition-injectivity claim | Qualify the complete frame-to-primitive adapter, including length and padding law, over the adversarial input domain; reject or account for every alias | Bounded one-limb versus one-limb-plus-zero alias; [Plonky3 binding advisory](https://github.com/advisories/GHSA-vj64-rjf3-w3v7) |
| FS-A06 | Radix, modular-collapse, or high-bit truncation: field or limb conversion discards information or entropy | Change discarded high bits or exploit noninjective base conversion while preserving the observed primitive input | No structural defense is claimed. PIR records the selected algorithms and requested lengths so the exact target of analysis is unambiguous | Prove or falsify injectivity and range preservation for each adapter; separately establish output entropy and sampler adequacy | Bounded 1, 257, and 513 high-bit aliases; [Plonky3 binding advisory](https://github.com/advisories/GHSA-vj64-rjf3-w3v7) |
| FS-A07 | Variable-length sponge alias / padding ambiguity | Choose distinct-length messages that reach one sponge state | Logical framing fixes lengths and types, and construction identity fixes the selected transition family | For variable-length use, establish length-separated state binding for the concrete sponge adapter. A fixed-length-only primitive must be refused outside its declared domain | Bounded variable-length alias class; [Plonky3 PaddingFreeSponge advisory](https://github.com/advisories/GHSA-3g92-f9ch-qjcm) |
| FS-A08 | Biased challenge decoding | Search more effectively over overrepresented challenges or invalidate a theorem's uniform-coin premise | PIR types the decoder, draw namespace, retry limit, and exhaustion result; the current AFK Analysis lane requires exact sampler adequacy | A reusable profile must distinguish exact uniformity, bounded statistical distance, and theorem-specific biased distributions; modulo reduction alone is not evidence | Bounded modulo-three decoder over 256 inputs; [CFRG draft 03](https://www.ietf.org/archive/id/draft-irtf-cfrg-fiat-shamir-03.txt), [Duplex FS](https://eprint.iacr.org/2025/536) |
| FS-A09 | Rejection exhaustion or retry semantics are omitted from the proof model | Force or benefit from an unmodeled failure branch, changed query count, or retry namespace | Canonical PIR makes each draw, namespace, bounded retry, state advance, and SamplingExhausted failure explicit | Analysis must prove total exact uniformity or include conditional distribution, exhaustion probability, state effects, and query/loss terms in the theorem application | Bounded conditional-uniform sampler with and without an explicit failure term; current AFK sampler boundary |
| FS-A10 | Session, protocol, instance, ciphersuite, or challenge-coordinate confusion | Replay proof material across applications, statements, composed protocols, or draws | Construction and Core headers, application domain, scope paths, declared session/Statement values, and challenge namespaces are semantic inputs; composition forms a new Core/construction identity | Deployment must bind the exact ciphersuite, protocol and message types, application context, instance, and session lifecycle. Concrete query encoding must preserve every coordinate | Bounded session/instance/namespace aliases under a weak index; [CFRG draft 03](https://www.ietf.org/archive/id/draft-irtf-cfrg-fiat-shamir-03.txt) |
| FS-A11 | OIR projection drops or substitutes an FS law while retaining a locally coherent endpoint | Compile a weaker prefix, namespace, sampler, or failure contract than the admitted source | Bounded OIR projection uses independent target formation and exact canonical graph equality, retaining static FS construction, frame, prefix, namespace, retry, state, and failure laws | Dynamic receipts, state versions, parsing, and execution remain Stage 4B; future optimization requires a new refinement relation rather than weakening equality | Bounded prefix-law substitution in OIRStaticProjection; current OIR projection contract |
| FS-A12 | Lowering uses a weak query index or reorders transcript effects | Obtain the same concrete challenge for source-distinct sessions, instances, frames, or draw coordinates | OIR preserves the static contract and Realization reserves exact target-specific RealizesOir checking | Implement a state-threaded lowering, validate its complete query ABI and failure behavior, and qualify the provider. Finite vectors alone do not establish the universal relation | Bounded canonical-index versus payload-only lowering; target Realization contract |
| FS-A13 | Parser accepts trailing bytes, alternate encodings, or disagrees with the prover serializer | Smuggle unconsumed proof material or exploit multiple proof-byte representations | Realization owns proof codec, target binding, parser behavior, and exact implementation checking; PIR does not conflate transcript encoding with proof serialization | Require infallible/distribution-preserving codec properties where the theorem needs them, reject noncanonical forms, and require exact end-of-input | Bounded trailing-byte parser mutation; [CFRG draft 03](https://www.ietf.org/archive/id/draft-irtf-cfrg-fiat-shamir-03.txt) |
| FS-A14 | A BCS compiler label is treated as supplying state-restoration, RBR, commitment binding, or source soundness | Exploit a source protocol outside the selected compiler theorem's premise | PIR separates logical Oracle, oracle-commitment construction, same-Core FS, and Analysis; the structural compiler result makes no property claim | Validate the exact interactive source property, commitment/opening assumptions, theorem statement, applicability, query bounds, and loss | Bounded missing interactive-source-property premise; [BCS](https://eprint.iacr.org/2016/116), [IOP soundness notions](https://eprint.iacr.org/2023/1256), [FRI FS](https://eprint.iacr.org/2023/1071) |
| FS-A15 | A classical ROM result is silently promoted to QROM | Use superposition queries against a proof that only controls classical oracle access | Analysis profiles identify the adversary and oracle process; current selected AFK result is explicitly classical | Add a distinct QROM query ABI, source validation, applicability judgment, extractor/reprogramming rights, and quantitative query loss | Bounded missing-QROM-premises check; [Measure-and-Reprogram 2.0](https://eprint.iacr.org/2020/282) |
| FS-A16 | Formally verified wrong specification: code refines an incomplete transcript, lossy codec, or inapplicable theorem model | Rely on a genuine implementation proof whose source semantics already grant the attacker's freedom | zkc separates PIR, Relations, Analysis, OIR projection, Realization, and deployment judgments, so one affirmative result cannot manufacture the others | The consumer must join exact affirmative results and retained assumptions. Mechanization should target theorem truth and implementation refinement separately | Bounded verifier-refinement-only premise set; [VCVio](https://eprint.iacr.org/2024/1819) |

## 3. Incident decomposition

The matrix deliberately separates incident symptoms that are often described
with the same word.

### 3.1 “Missing from the transcript”

This phrase has three non-equivalent meanings:

| Meaning | Correct checker |
|---|---|
| The application never declared an expected Statement | Closed external Statement correspondence |
| The Core declared a value but the challenge prefix omitted or delayed it | DerivedPrefix and runtime receipt equality |
| The logical frame was present but its concrete representation lost the distinction | Encoding and state-transition binding qualification |

Weak FS and Frozen Heart primarily pressure the first row. Missing-opening and
Last-Challenge incidents primarily pressure the second. The 2026 Plonky3
binding advisory primarily pressures the third. One boolean named
StrongFiatShamir would obscure exactly the distinction the architecture needs.

### 3.2 “Hashing all fields”

Even complete field enumeration is insufficient unless:

- the field domain is closed;
- the tuple encoder is canonical and injective;
- every adapter into the primitive preserves the representation;
- message length and padding are domain separated;
- challenge decoding meets the selected distribution;
- repeat and adaptive queries realize the required oracle process; and
- the implementation parses and executes the same contract.

The pressure instrument makes this nonimplication executable: its exact
logical prefix passes while its deliberately length-free limb adapter has an
alias.

### 3.3 “Formally verified”

Mechanization can establish at least three different facts:

| Mechanized object | Possible result | Still external |
|---|---|---|
| Cryptographic reduction | The selected source property implies the selected target property in a formal oracle model | zkc-to-model correspondence, concrete primitive, lowering, deployment |
| Compiler or verifier refinement | Every selected target behavior refines the admitted OIR/source behavior | Completeness and security of the source specification and theorem |
| Per-artifact translation validator | This emitted artifact satisfies the validator's preservation relation | Unchecked artifacts and properties absent from that relation |

Calling each result “verified FS” would be technically true only after its
scope is appended. The architecture should retain the exact proposition and
qualification rather than the slogan.

## 4. Source-to-obligation map

| Source family | Primary obligation pressure | Architectural consequence |
|---|---|---|
| BPW, Weak FS Attacks, Frozen Heart | Strong versus weak Statement binding and adaptive selection | Keep external Statement closure separate from transcript scheduling |
| Fiat--Shamir in the Wild | Missing messages, ambiguity, brute force, and multi-round implementation errors | Require attack-first negative tests across schedule, encoding, and sampler boundaries |
| Last Challenge | Protocol-specific final dependency before batching challenge | Let Core/reduction semantics name the dependency; do not use a generic “hash previous bytes” rule |
| CFRG draft 03 | Session tags, complete instance, prefix-free codecs, sequential API, serialization separation, exact parsing | Carry these as Analysis and Stage 4B requirements, not as an RFC-level theorem |
| BCS and FRI/RBR work | Compiler theorem requires exact source property and quantitative terms | Keep Oracle commitment compilation, FS, source property, and theorem applicability separate |
| AFK multi-round | Classical adaptive multi-round transform with exact loss | Reuse only through a theorem-indexed Analysis profile |
| Measure-and-Reprogram | QROM extraction and reprogramming are model-specific | Refuse classical-to-QROM promotion |
| Duplex FS | Salt, codecs, mutable permutation state, inverse queries, and theorem premises | Retain a sibling construction and separate ideal-permutation profile |
| VCVio | Cryptographic reductions can be machine checked | Mechanization is a theorem-evidence lane, not a universal implementation certificate |
| Plonky3 advisories | Logical transcripts can alias in concrete adapters and sponges | Preserve PIR's explicit nonclaim and add transition-binding/realization checks |
| Solana ZK ElGamal postmortem | Omitted algebraic proof components can make acceptance vacuous | Check complete protocol-specific verification equations as well as transcript influence |

## 5. Nonimplication matrix

An affirmative row does not imply any checked column marked “no.”

| Affirmative result | Prefix exact | Encoding injective | Sampler adequate | Source theorem applies | OIR preserved | Code conforms | Deployment safe |
|---|---:|---:|---:|---:|---:|---:|---:|
| PIR construction admitted | yes, structurally | no | no | no | no | no | no |
| Relations Statement correspondence | only its selected routes | no | no | no | no | no | no |
| Encoding qualification | no | yes, for named domain | no | no | no | no | no |
| Sampler qualification | no | no | yes, for named law | no | no | no | no |
| BCS/FS theorem applicability | consumed premise | consumed premise | consumed premise | yes, exact theorem only | no | no | no |
| OIR projection affirmative | preserves selected static law | preserves selected encoded contract only if present | preserves selected sampler law only if present | no | yes, selected relation | no | no |
| RealizesOir affirmative | no new source fact | implements selected OIR fact | implements selected OIR fact | no | consumed premise | yes, selected target | no |
| Deployment approval | consumed evidence | consumed evidence | consumed evidence | consumed evidence | consumed evidence | consumed evidence | yes, named threat model only |

## 6. Freeze disposition by attack class

| Disposition | Cases | Reason |
|---|---|---|
| Structurally closed in the selected semantic design | FS-A02, FS-A03 at an accurately authored Core, FS-A10 at the semantic query coordinate, FS-A11 for the bounded static projection | The required owner and exact law already exist |
| Closed relative to an explicit external manifest | FS-A01 | Interface/Relations close every represented Statement binding; the application-supplied expected domain remains a premise |
| Representable and partly instantiated in Analysis, but not generically qualified | FS-A04 through FS-A09, FS-A14 | The owner model exists and the AFK lane demonstrates the pattern; reusable profiles and source-specific results remain work |
| Explicitly deferred to Stage 4B | FS-A12, FS-A13 and concrete portions of FS-A05 through FS-A10 | Dynamic OIR, lowering, provider, parser, and deployment are intentionally unactivated |
| Separate research regime | FS-A15 | QROM needs different theorem and adversary coordinates |
| Prevented only by preserving the judgment chain | FS-A16 | No single owner can close an incorrectly specified end-to-end claim |

None of the deferred cases requires reopening the ownership factorization.
They require typed intake and fail-closed activation gates. A semantic-freeze
blocker would arise only if the frozen owners could not name one of these
obligations or if an obligation had no unambiguous owner. This audit found
neither condition.

## 7. What the executable instrument establishes

The 33 tests provide:

- same-boundary positive controls;
- one exact-prefix / lossy-transition cross-layer counterexample;
- finite encoding aliases for boundary concatenation, trailing zeros, and
  high-bit truncation;
- sampler controls that separate total uniformity from conditional uniformity
  with failure;
- static projection and realization mutations; and
- theorem-premise checks that refuse BCS labels, verifier proofs, and
  classical ROM results as substitutes for missing obligations.

They establish no universal injectivity, collision resistance, oracle
correspondence, theorem truth, implementation correctness, or security
property. Their purpose is architectural falsification: any proposed design
that collapses the layers cannot classify all selected cases correctly.
