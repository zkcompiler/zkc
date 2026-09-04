# K1 Executable Validation

> **Document kind:** Temporary validation and falsification record
> **Document state:** Bounded standalone K1 candidate complete; executable gate green
> **Provisional owner:** `foundation`
> **Authority:** None
> **Disposition:** Keep credited observations in the executable K1 package,
> rewrite durable limitations into
> [`executable-foundations.md`](../../../foundation/executable-foundations.md),
> and delete this page with the K1 notes package before cutover.

## 1. Claim under test

The integrated K1 mechanism is constructible over a bounded fixture surface.
Within that surface, canonical values and typed identity are independently
reproducible; module closure, term evaluation, and charging currently have one
reference evaluator:

- a constitutional bootstrap and disjoint prior-meta/semantic identifiers;
- domain-indexed canonical values;
- exact-used acyclic semantic-module closure;
- a small first-order term calculus with one bounded iterator;
- exact primitive references and a derived success/failure ABI;
- deterministic charging, completion preflight, and validation precedence;
  and
- completed semantics separated from qualified noncompletion.

This page credits executed results only. Selection rationale lives in
[`research-and-selection.md`](research-and-selection.md); the durable target
owns the selected rules. The bounded standalone candidate has completed its
strict executable gate and its selected rules are provisionally absorbed into
the durable Foundation target. This does not freeze the integrated kernel:
K2/K3 consumer integration remains open.

## 2. Instrument and trust boundary

The executable package is
[`evaluation/k1-executable-foundations/`](../../../../evaluation/k1-executable-foundations/).
Its intended evidence lanes are:

- a reference typed-value encoder, identity implementation, type checker,
  module-closure checker, and term evaluator;
- a separately written canonicalization and identity oracle that imports no
  reference-model code;
- frozen request and expected-result vectors for the oracle's exact surface;
- positive tests and one-boundary falsifiers; and
- one strict check command that runs the package without regenerating accepted
  output implicitly.

Both identity implementations use the host SHA-256 library. Their agreement
does not independently validate SHA-256. Both run in Python, so independence
means separately written code paths for canonical values and IDs, not runtime,
compiler, or cryptographic diversity. There is only one portable-term
evaluator in K1.

At the initial standalone checkpoint, the strict runner executed 90
reference/parity tests and 26 independently written oracle tests, for 116/116
passing tests. That checkpoint and its `bfe22f86...` regime are historical and
superseded. The post-K3-E repair gate executes 103 reference/parity tests and
26 oracle tests, for 129/129 passing tests. The current 103-test lane contains
101 direct `reference_model` tests, one record-by-record cross-check, and one
exact durable-law transcription check. The record cross-check independently
recomputes exact shared positive constructions and
checks bounded contrasts or declared projections for the remaining records;
it is not an equivalent reference implementation of every raw oracle request.

## 3. Frozen fixture contract

### 3.1 Constitutional value profile

`FoundationMetaProfileV0`, named `zkc.foundation.meta.v0`, is un-IDed. For the
instrument, `u64(n)` is an unsigned 64-bit big-endian integer and
`frame(x) = u64(length(x)) || x`.

| Tag | Structural value | Canonical payload |
|---:|---|---|
| `0x00` | Unit | empty |
| `0x01` | Boolean false | empty |
| `0x02` | Boolean true | empty |
| `0x03` | Natural | framed minimal big-endian magnitude; zero is one zero byte |
| `0x04` | Signed integer | sign byte, then framed minimal magnitude; negative zero refuses |
| `0x05` | Bytes | framed octets |
| `0x06` | Symbol | framed nonempty printable ASCII octets |
| `0x07` | Sequence | count, then each framed child |
| `0x08` | Record | count, then strictly increasing field ordinal and framed child |
| `0x09` | Variant | case ordinal and framed payload |

There is no semantic JSON object, floating point, unordered map, or host
reflection. A map or set is a domain-declared sorted-unique sequence. JSONL is
fixture transport only; object member order is not semantic.

### 3.2 Disjoint identifier constructors

The prior-meta constructor accepts exactly:

```text
foundation.identity-profile
foundation.hash-suite
foundation.semantic-regime
```

For a canonical meta body `B` and one of those kinds `K`:

```text
Pmeta = "zkc/prior-meta-id/v0\0"
        || frame("zkc.foundation.meta.v0")
        || frame(K)
        || frame(B)

PriorMetaId.digest = SHA-256(Pmeta)
```

The ordinary constructor accepts none of those kinds and always carries an
identity-profile `PriorMetaId`, hash-suite `PriorMetaId`, and semantic-regime
`PriorMetaId`. For ordinary kind `K`, canonical body `B`, and typed axes
`I`, `H`, and `R`:

```text
PriorMetaRef(M) = frame(M.foundation_profile)
                  || frame(M.subject_kind)
                  || raw_digest(M)

Psemantic = "zkc/content-id/v0\0"
            || frame("zkc.foundation.meta.v0")
            || frame(PriorMetaRef(I))
            || frame(PriorMetaRef(H))
            || frame(K)
            || frame(PriorMetaRef(R))
            || frame(B)

SemanticContentId.digest = SHA-256(Psemantic)
```

There is no optional or null regime. `id_type`, nested axis kind, subject kind,
and digest are all checked. Semantic modules, primitives, algorithms, value
domains, and evaluation contracts are ordinary semantic subjects.

The current frozen semantic-core law source is exactly 45,669 bytes with
SHA-256
`96bd8574d064e06a4d379c0a4afd82d526186231c3f092f143bf66e482789cfc`.
The complete encoded regime descriptor is exactly 46,606 bytes with SHA-256
`01c0112364714a764d2e287c8b710022d6c3791e34dd7cc5101cfb91293dcf4f`.
The resulting semantic-regime digest is
`a36c5cc0d431a16bd6e96e933101e8f2d20ad5f4f3a770327ddb6362f071203c`.

### 3.3 Regime root and modules

The fixture regime root embeds the minimum structural/term basis and
local-ordinal aggregate rule. It imports no post-root semantic module.
Extension modules are ordinary semantic IDs under that root. Imports must be
same-regime and acyclic; a subject presents canonical sorted-unique direct
roots, and authentication accepts every and only member of their unique-node,
unique-edge transitive closure.

An unrelated module must not change the root or an existing subject preimage.
Changing a module actually cited by an algorithm must change that algorithm's
preimage; the concrete SHA-256 fixtures must also produce distinct IDs.

### 3.4 Portable function surface

The canonical core under test has arguments/constants, `let`, records and
projection, injection/case, conditional, bounded sequence construction and
access, exact primitive calls, typed failure, and one indexed state-passing
`BoundedIterate` over a finite sequence or bounded natural range.

Map, fold, zip, find, sorting, and path traversal are encodings in that core,
not independently privileged constructors. General recursion, effects,
ambient callbacks, implicit randomness, and host exceptions as meaning are
outside the surface.

The type checker derives:

```text
SemanticFunctionType =
  (ordered inputs, success type,
   canonical SemanticFailureType(module, ordinal, payload type) alternatives)
```

Primitive dependencies are exact semantic IDs derived from syntax. A provider
binding and an `ExternalOperationContract` are not portable algorithms.

### 3.5 Evaluation and completion surface

Evaluation order is fixed by the language. An identified evaluation contract
fixes validation precedence, atomic term/iteration charges, exact primitive
work formulas, completion encoding, and the static completion-bound rule. A
request supplies nonnegative mathematical-natural limits for:

```text
term steps
iteration items
primitive work
result bytes
```

The evaluator preflights the maximum tagged completion size across success and
all declared failure payloads before entering the term. It charges exact
completion bytes for both success and typed semantic failure.

The reference fixture distinguishes:

```text
Completed(Success | typed semantic failure)
Malformed
KindMismatch
Unsupported
MissingDependency
Refused
DeterministicLimitExceeded
CheckerFailure
```

The matrix tests exact precedence; the list is not proposed as a universal
Foundation result enum. Incidental host failure must escape without being
reclassified as any semantic or recoverable outcome.

For this selected evaluator, `Malformed` covers invalid carriers,
noncanonical bytes, and failed kind-specific structural formation;
`KindMismatch` covers a valid coordinate of the wrong kind, regime, or exact
type; and `Refused` covers a structurally valid candidate that, after required
authentication, fails a supported closed resolution, typing, owner-admission,
or compatibility predicate. In particular, strict input decode failure is
`Malformed`, while post-decode input owner-admission failure is `Refused`.

## 4. Evidence and falsifier matrix

`passed` means that both the stated positive and falsifying observations were
executed on the instrument's exact surface. `partial` means that a stated law
was exercised only through typed objects or through only part of its negative
surface. `unexercised` marks an explicit surface for which this package grants
no runtime evidence.

### 4.1 Bootstrap, values, and identity

| Obligation | Positive control | Falsifier or contrast | Required observation | State |
|---|---|---|---|---|
| all ten structural tags | strict encode/decode round trip | unknown tag or trailing bytes | one canonical full-value decode only | passed |
| minimal numeric form | zero and boundary magnitudes | leading zero or negative zero | noncanonical input is `Malformed` | passed |
| ordered aggregate form | ordered record and sequence | duplicate/unsorted ordinals or malformed length | refuse before aggregate result | passed |
| cumulative encode/decode limits | exact-limit nested value | declared wide child count or one-less budget | refuse before aggregate construction or child-array allocation | passed |
| prior-meta kind closure | all three exact kinds | fourth kind through prior constructor | constructor refuses | passed |
| ordinary kind disjointness | ordinary semantic subject | prior-meta kind through ordinary constructor | constructor refuses | passed |
| mandatory regime | ordinary ID with exact regime root | null, absent, or wrong-kind regime axis | canonical typed refusal | passed |
| axis typing | exact identity/hash/regime IDs | swapped or coincident-digest wrong axes | mismatch before body digest | passed |
| identity sensitivity | one-axis and body mutations | carrier-only rendering or diagnostic label change | semantic mutations change exact preimages and produce distinct fixture IDs; nonsemantic changes preserve both | passed |
| value-domain and equality separation | equal and unequal admitted values at one exact type | identical bytes under another domain or schema | selected root equality is defined only at one exact `ValueType`; type mismatch refuses | passed |
| hash-binding conflict | exact presented ID/preimage recomputation, typed-axis non-aliasing, and request-local ledger re-observation | synthetic digest substitution makes two strictly canonical descriptor bodies authenticate to one typed ID | ledger emits `CheckerFailure`; no real-collision or global-binding credit | partial |
| optional `CanonicalValueId` | none | none | no executable credit | unexercised |

### 4.2 Modules and extension locality

| Obligation | Positive control | Falsifier or contrast | Required observation | State |
|---|---|---|---|---|
| root closure | frozen import-free root descriptor | post-root imports excluded by the fixed root shape | descriptor and root law agree | partial |
| same-regime imports | linear chain | cross-regime import | refusal at module boundary | passed |
| acyclic closure | chain and shared diamond | forged cycle candidate | diamond counted once; forged cycle is rejected by authentication before traversal | partial |
| exact supplied closure | every and only reachable typed-map entry | missing node, extra node, wrong-kind alias | distinct first-boundary refusal | partial |
| canonical roots | derived sorted-unique direct roots | typed malformed-root contrast only | derivation is canonical; no raw root carrier is decoded | partial |
| unrelated extension locality | add unused module | mutate used module | root/existing preimage and ID stay stable; dependent preimage changes and the fixture ID is distinct | passed |
| raw module-map carrier canonicality | none | duplicate/unsorted raw entries or noncanonical raw module bodies | no executable credit | unexercised |

### 4.3 Terms, primitives, and typed failure

| Obligation | Positive control | Falsifier or contrast | Required observation | State |
|---|---|---|---|---|
| term structural bounds | exact node and root-zero-depth limits | one occurrence or one level over | exact boundaries admit; either excess is `Malformed` before serialization or typing | passed |
| derived function type | admitted closed term | authored label/output contrast | output and failures derive; label has no ID effect | passed |
| binder correctness | nested `let`/`BoundedIterate` | shifted or out-of-range variable | valid nesting agrees; invalid binder refuses | passed |
| structural/admission outcome partition | malformed term carrier and noncanonical input bytes | authenticated ill-typed term, rejected literal, and canonical post-decode rejected input | malformed structure remains `Malformed`; supported closed typing or owner-admission failure is `Refused`; wrong declaration kind is `KindMismatch` | passed |
| recognized declaration formation | exact value-domain, failure, and primitive bodies | malformed primitive/failure body, missing local failure coordinate, and post-lift bound failure | all coordinates resolve before body interpretation; malformed body is `Malformed`, absent formed coordinate or closed lift failure is `Refused`, and valid unknown primitive meaning is `Unsupported` | passed |
| exact primitive dependency | supported exact primitive ID | same name/wrong version or wrong-kind ID | unsupported/kind mismatch, never fallback | partial |
| typed partiality | positive modulus/divisor | zero divisor | declared typed failure completes | passed |
| failure-row integrity | exact declared payload | authored wrong/conflicting declarations and injected runtime undeclared/wrong payloads | authored typing or compatibility defects are refused; malformed declaration structure remains malformed; runtime provider violations are checker failures; none become semantic completion | passed |
| transcript-shaped state fold | finite absorb sequence | changed frame/order | direct calculation agrees; semantic mutation changes the preimage and produces a distinct fixture ID | passed |
| bounded rejection | success before retry bound | no candidate before bound | semantic failure, not evaluator exhaustion | passed |
| nested count-by-retry | multiple bounded draws | inner exhaustion or one-less iteration budget | typed failure distinguished from outer limit | passed |
| strict sequence access | aligned paired traversal | shorter peer sequence | declared strict-index failure | passed |
| authenticated path fold | bounded sibling path | orientation/index mutation | result and algorithm identity change as specified | passed |
| lossy projection | exact declared prefix/projection | wrong output domain or undeclared loss | admitted exact transform or refusal | passed |
| external-operation separation | portable algorithm | supplier contract/binding in algorithm position | exact wrong-namespace subject is `KindMismatch`; malformed carrier is `Malformed`; neither executes | passed |
| raw algorithm dependency carrier | none | direct-primitive field omission, padding, or reorder | no executable credit | unexercised |

### 4.4 Evaluation contracts and resources

| Obligation | Positive control | Falsifier or contrast | Required observation | State |
|---|---|---|---|---|
| contract identity separation | default exact contract | charge-schedule mutation | contract preimage changes and its fixture ID is distinct; algorithm preimage and ID do not change | passed |
| request-limit separation | two sufficient budgets | limit-only mutation | neither semantic ID rotates | passed |
| contract routing | supported exact contract | unknown or wrong-kind contract ID | unsupported distinguished from kind mismatch | partial |
| primitive cost closure | exact cost rule for each call | missing rule, unknown closed-variant tag, and present ABI-incompatible rule | missing rule is `Unsupported`, unknown tag is structurally `Malformed`, and present incompatible rule is `Refused`, all before term entry | passed |
| exact step limit | measured exact budget | one-less step budget | exact completes; one-less exhausts | passed |
| exact iteration limit | measured exact budget | one-less item budget | exact completes; one-less exhausts | passed |
| exact primitive-work limit | measured exact budget | one-less work budget | exact completes; one-less exhausts | passed |
| static completion preflight | sufficient result capacity | one-less maximum completion capacity | evaluator term is not entered | passed |
| exact emitted result charge | success and semantic failure | distinct canonical completion envelopes | recorded charge equals each exact envelope size; runtime one-less actual-result refusal is subsumed by the larger static maximum preflight and is not separately reachable | partial |
| atomic charges | near-limit operation | operation whose delta crosses limit | no partial counter commit | passed |
| limit validation | finite nonnegative integers | negative, Boolean, text, float, NaN, infinity | malformed before subject evaluation | passed |
| validation precedence | typed and encoded-input one-defect controls | typed multi-defect requests | documented first boundary wins on the implemented request subset | partial |
| host failure boundary | ordinary checker defect and exact built-in host carriers | injected `MemoryError` and semantic-override subclasses | no false result record or override dispatch | partial |
| raw request and asserted-ID/body pairing | none | separately supplied algorithm/contract/module ID-body mismatch | no executable credit | unexercised |

### 4.5 Independent-oracle agreement

| Obligation | Positive control | Falsifier or contrast | Required observation | State |
|---|---|---|---|---|
| canonical bytes | all common supported structural values | malformed/noncanonical vectors | reference and oracle agree exactly | passed |
| prior-meta IDs | three exact descriptor constructions | wrong kind/profile/body classified in each lane | positive bytes and digests agree; the full negative request semantics are not replayed through an equivalent reference operation | partial |
| semantic IDs | exact axes and ordinary-body constructions | null/wrong/swapped axes and kind misuse classified in each lane | positive bytes and digests agree; the full negative request semantics are not replayed through an equivalent reference operation | partial |
| local resource edges | exact-limit controls in each lane | one-less input/output/node/depth/work controls | each lane exercises its declared boundary; only the wide-input contrast is related in the parity test, so first-result agreement is not established across the whole row | partial |
| frozen replay | frozen declared JSON projection | a projected generated field differs | the strict projected gate fails rather than silently rewriting its baseline | passed |

## 5. Consolidated result

The bounded standalone K1 candidate is complete and its final executable gate
is green. This is not an integrated-kernel freeze or a claim that the partial
and unexercised surfaces above have been tested. The reconciled matrix contains
36 passed rows, 13 partial rows, and 4 unexercised rows.

| Gate | Command or artifact | Final count/result |
|---|---|---|
| reference and parity suite | `python3 -B evaluation/k1-executable-foundations/run.py --check` | 103/103; 101 direct reference-model tests plus one all-record parity test and one durable-law transcription check |
| independent oracle suite | same strict runner | 26/26 |
| complete strict gate | same strict runner | 129/129 |
| frozen-vector replay | 24-request declared expected projection | passed against the deliberately rotated K1 regime baseline |
| frozen law source | exact bytes and SHA-256 | 45,669 bytes; `96bd8574d064e06a4d379c0a4afd82d526186231c3f092f143bf66e482789cfc` |
| frozen regime descriptor | exact bytes and SHA-256 | 46,606 bytes; `01c0112364714a764d2e287c8b710022d6c3791e34dd7cc5101cfb91293dcf4f` |
| frozen regime identity | semantic-regime digest | `a36c5cc0d431a16bd6e96e933101e8f2d20ad5f4f3a770327ddb6362f071203c` |

The gate above closes only the bounded standalone K1 candidate. Repository
lint, durable-document reconciliation, consumer integration, and cold review
remain separate gates and receive no credit from these counts.

## 6. Explicit nonclaims

The passing bounded gate does not establish:

- correctness, collision resistance, second-preimage resistance, or
  unconditional global binding of SHA-256-derived IDs;
- conformance of any cryptographic primitive provider;
- constant-time, memory-safe, or production-quality implementation;
- completeness of the calculus for all ZK protocols or paper variants;
- PIR admission, causal execution, public-coin validity, or strong
  Fiat--Shamir;
- relation grounding, theorem applicability, security reduction, compiler
  legality, OIR endpoint validity, or realization correctness;
- formal proof of the durable specification;
- independent portable-term evaluation;
- a full raw serialized evaluation-request decoder;
- raw asserted prior-meta ID/body pairing or a well-formed but unsupported
  prior-meta basis in the reference evaluator;
- raw algorithm-body direct-primitive field omission, padding, or reordering;
- separately supplied asserted-ID/body mismatch handling for algorithms,
  contracts, or modules;
- duplicate or unsorted raw module-map carriers, or noncanonical raw module
  bodies, because the reference package receives a typed Python mapping;
- the optional `CanonicalValueId` surface;
- the authenticated-cycle refusal branch without a hash fixed point or
  collision; or
- guaranteed recovery from catastrophic allocation, process death, or
  reflective mutation.

The oracle's independence is limited to canonical structural values and the
two ID constructors. Algorithm, contract, and module bodies are typed Python
objects. Module closure and term evaluation have one K1 reference evaluator
and gain confidence from falsifiers, not independent semantic agreement.

At the host boundary, the reference evaluator copies an exact built-in `dict`
or the package's exact immutable fixture-mapping singleton once and recursively
accepts only exact frozen dataclass shapes. The new
semantic-override falsifier confirms that subclasses cannot override
algorithm, term, module, contract, or charge-formula semantics. The failure-row
suite now also rejects one failure declaration carrying conflicting payload
types. These tests do not cover catastrophic allocation or arbitrary
reflection after the authenticated snapshot.

## 7. Standalone verdict and remaining integration gate

The bounded standalone K1 candidate has satisfied its executable exit gate.
Its exact tested mechanism is present in the provisional durable Foundation
owner, the parent inventories and integrated gate are current, transition
notices delimit the pre-K1 consumer pages, and the cold K1 review is complete.
Final integration still requires:

1. replace pre-K1 consumer placeholders with one exact owner or explicit
   domain-local refinement during K2/K3;
2. demonstrate the same Foundation meaning in at least two consumers and
   confirm that no owner-specific semantics leaked into the shared layer;
3. retain evaluator-relative support and residual implementation trust as
   nonclaims; and
4. delete this temporary package only after no durable page depends on it.

The integrated kernel is not frozen by this verdict. K2 Protocol/Fiat--Shamir
work and K3 consumer co-design remain open, and any contradiction found there
may reopen the narrow K1 decision it falsifies.
