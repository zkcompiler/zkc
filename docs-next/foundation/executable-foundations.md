# Executable Semantic Foundations

> **Document kind:** Target semantic specification
> **Document state:** Active non-normative target
> **Target status:** K1 durable selection; K2/K3 integration remains open
> **Provisional owner:** `foundation`
> **Authority:** None during the transition. Current normative identity,
> encoding, admission, and execution rules remain under
> [`docs/`](../../docs/README.md).

## 1. Contract and boundary

This page defines mechanisms whose meaning must be shared by PIR and at least
one other semantic domain:

- the constitutional bootstrap and disjoint identity classes;
- regime-qualified semantic content and acyclic semantic modules;
- domain-indexed canonical values;
- a small, total, first-order term calculus and exact semantic primitives;
- derived success and typed-failure function ABIs;
- deterministic evaluation control; and
- the boundary between semantic completion and operational noncompletion.

Foundation does not define a universal ZK value algebra, protocol evaluator,
transition system, judgment engine, result type, or resource policy. A domain
continues to own its mathematical objects, admission predicates, semantic
failures, judgments, and domain-specific costs.

A successfully authenticated `(typed identifier, exact preimage)` pair binds
that presented description for the current check. Identifier-wide uniqueness
is conditional on the binding assumptions of the digest law governing that
constructor: constitutional SHA-256 for `PriorMetaId`, and the authenticated
`HashSuiteId` for `SemanticContentId`. Authentication does not establish that
the description is adequate, admitted, supported, implemented, or true.

## 2. Constitutional bootstrap

### 2.1 `FoundationMetaProfileV0`

`FoundationMetaProfileV0` is selected before any content-addressed object
exists. It is constitutional rather than self-identified. It fixes:

- the `MetaValueV0` algebra and injective encoding;
- prior-meta and ordinary semantic-content domain separation;
- typed-reference framing;
- SHA-256 for prior-meta identity; and
- pair-local authentication and fail-closed hash-binding-conflict handling for
  both identity constructors under this foundation epoch; and
- checked-natural arithmetic and the exact `MetaValueV0` encoding, decoding,
  and hashing budgets used while authenticating finite material.

Changing any of these rules creates a new foundation epoch. Existing bytes are
never reinterpreted under a changed constitutional profile.

For the selected v0 profile, let `A(s)` be the nonempty printable-ASCII bytes
of axis symbol `s`, with length at most `2^20` checked before character
conversion or scanning; let `u64(n)` be unsigned 64-bit big-endian, and
`F(x) = u64(length(x)) || x`. `M(v)` is the canonical byte encoding of one
`MetaValueV0` value. Concatenation is `||`; literal prefixes below include
their final zero octet. `MetaValueV0` has exactly these structural forms:

| Tag | Form | Canonical payload |
|---:|---|---|
| `0x00` | Unit | empty |
| `0x01` | Boolean false | empty |
| `0x02` | Boolean true | empty |
| `0x03` | Natural | `F(minimal unsigned big-endian magnitude)`; zero is one zero byte |
| `0x04` | Signed integer | sign octet `0` for nonnegative or `1` for negative, then `F(minimal unsigned magnitude)`; negative zero refuses |
| `0x05` | Bytes | `F(octets)` |
| `0x06` | Symbol | `F(nonempty printable ASCII octets 0x21..0x7e)` |
| `0x07` | Sequence | `u64(count)` then `F(M(child))` for each child in order |
| `0x08` | Record | `u64(count)` then `u64(ordinal) || F(M(value))` in strictly increasing ordinal order |
| `0x09` | Variant | `u64(case) || F(M(payload))` |

In equations, `MetaNatural`, `MetaBytes`, `MetaSymbol`, `MetaSeq`,
`MetaRecord`, and `MetaVariant` denote exactly these tagged forms, not a
second data model.

Lengths, counts, ordinals, and cases fit `u64`. Magnitudes are minimal. A
decoder consumes exactly one value and requires byte-for-byte re-encoding
equality. Unknown tags, trailing bytes, invalid symbols, duplicate or unsorted
fields, overlong magnitudes, and length disagreement are malformed.

The constitutional data limits are exact:

```text
maximum canonical bytes       = 2^20
maximum MetaValue nodes       = 2^14
maximum aggregate child edges = 2^14
maximum root-zero depth        = 384
```

All four are cumulative across one value; a child edge is one sequence item,
record field value, or variant payload. Reaching a bound is allowed and
crossing it refuses. A framed magnitude's conversion work is its octet length
and is preflighted within the same byte bound.

There is no semantic JSON object, floating point, unordered map, host object,
or reflective extension. A domain map or set is represented by a declared
sorted-unique sequence. JSON, MLIR, a database record, or another carrier may
transport canonical material but cannot determine semantic identity or order.

Encoding and decoding preflight cumulative bytes, nodes, depth, child edges,
and declared scalar-conversion work before materializing an aggregate result.
Crossing a deterministic limit produces neither a partial value nor an ID.
Every aggregate-bearing semantic carrier has an explicit cardinality owner.
Admission checks its declared or trusted cardinality against that bound before
member inspection or constructing a derived aggregate. The exact mapping is:

| Aggregate boundary | Owning bound |
|---|---|
| `MetaValueV0` sequence or record | remaining cumulative constitutional child edges and nodes |
| finite-schema record or variant | per-aggregate child-edge ceiling plus remaining cumulative schema-node minimum reservation |
| semantic-function inputs/failures; primitive failures/work indices; evaluation-contract cost rules; module declaration catalogs/bodies; algorithm inputs | per-aggregate constitutional child-edge ceiling |
| canonical-term multi-child constructor | remaining term nodes |
| semantic-module imports | per-module import-edge ceiling, then authenticated-closure remaining-edge reservation |
| direct module roots | module-node ceiling |
| module-preimage bundle | module-bundle entries |
| evaluation-request inputs | exact derived function-input count |

The strict serialized carrier separately owns aggregate raw-byte preflight.
Concrete tuple, map, length, snapshot, and allocation mechanisms belong to the
realization and its evidence, not to this portable semantic law.
The `remaining` owners above are cumulative traversals. The per-aggregate rows
preflight each local carrier against the full constitutional ceiling; the
canonical projection and encoder independently enforce the cumulative
`MetaValueV0` budget over the resulting typed body. A module candidate's local
import sequence must be bounded and authenticated before its imports can count
toward the closure; the closure reserves the remaining cumulative edge budget
before scheduling those authenticated imports. These owners are global
structural work bounds. Local semantic constraints such as an exact primitive
ABI arity or a sequence's declared capacity are checked later, but only after
the enclosing aggregate has passed its global preflight.

The pair-local authentication and `HashBindingConflict` discipline detailed in
Section 3.1 is constitutional. It applies to a `PriorMetaId` before any
identity-profile or hash-suite descriptor exists, as well as to every later
`SemanticContentId`. Changing that discipline creates a new foundation epoch.

### 2.2 Exactly three prior-meta kinds

The constitutional profile can construct `PriorMetaId<K>` for exactly three
disjoint kinds:

```text
IdentityProfileId = PriorMetaId<IdentityProfile>
HashSuiteId       = PriorMetaId<HashSuite>
SemanticRegimeId  = PriorMetaId<SemanticRegime>

IdentityProfile = "foundation.identity-profile"
HashSuite       = "foundation.hash-suite"
SemanticRegime  = "foundation.semantic-regime"
```

Only those three kinds use the prior-meta constructor. Every other subject is
ordinary and carries a mandatory regime axis. For `K` equal to one of the
three kinds and canonical descriptor value `d`, construction is:

```text
PriorPreimageV0(K, d) =
    "zkc/prior-meta-id/v0\0"
    || F(A("zkc.foundation.meta.v0"))
    || F(A(K))
    || F(M(d))

PriorMetaId<K>(d) =
    ("zkc.foundation.meta.v0", K, SHA256(PriorPreimageV0(K, d)))

PriorRefV0(id) =
    F(A(id.foundation_epoch)) || F(A(id.kind)) || id.digest
```

`M(d)` must strictly decode and re-encode byte-for-byte before hashing. The
digest field is exactly one 32-octet byte string; no bytes-like host carrier
or coercion is accepted. It commits to the foundation epoch, exact kind, and
exact descriptor.
The three ID types do not alias even if digest octets coincide. `PriorRefV0`
is an internal typed-reference payload; every embedding of it in another
preimage is itself framed.

The identity-profile descriptor fixes ordinary subject-preimage framing and
ID construction. The hash-suite descriptor fixes the exact digest operation
and output domain. A semantic-regime descriptor fixes the minimum language
needed to authenticate meaning within that regime. Its exact authenticated
law exposes base declarations through kind-indexed local ordinals; as a
prior-meta root, its descriptor need not use the ordinary module envelope. A
mutually recursive strongly connected group is one finite aggregate
declaration with local ordinals, not a content-hash fixpoint.

The regime root embeds this finite base grammar directly. It imports no
ordinary semantic module and does not enumerate later extensions. Therefore
the root cannot participate in a root--module identity cycle.

### 2.3 Prior-meta authentication before ordinary identity

An ordinary object is authenticated only relative to:

```text
PriorMetaAuthenticationBasis = {
  identity_profile: (IdentityProfileId, exact descriptor bytes),
  hash_suite:       (HashSuiteId, exact descriptor bytes),
  semantic_regime:  (SemanticRegimeId, exact descriptor bytes)
}
```

The descriptor bytes are preimages, not citations or cached claims. For basis
`B`, before any ordinary digest is recomputed, evaluator `E` must:

1. check the three typed headers and require exactly one entry of each kind;
2. strictly decode each descriptor as one `MetaValueV0`, require exact
   re-encoding, and recompute its `PriorMetaId` with the equation above;
3. establish
   `Supports(E, B.identity_profile.id, OrdinaryPreimageV0)`,
   `Supports(E, B.hash_suite.id, SHA256-32)`, and
   `Supports(E, B.semantic_regime.id,
   RootDeclarationResolution(B.semantic_regime.id))` for those exact
   authenticated IDs.

Support is granted only after `E` recognizes and validates the complete exact
descriptor contract for that ID. In particular, regime support must establish
the root's kind-indexed declaration law and no-ordinary-import property; an
unknown descriptor is not interpreted through a guessed common shape.

For the selected v0 evaluator, the first two support checks require the exact
descriptor IDs for `OrdinaryPreimageV0` and 32-octet SHA-256 below. Multiple
regime IDs may be supported if each exact root law is implemented. A different
well-formed prior-meta ID can authenticate as prior metadata yet remain
unsupported for ordinary evaluation. Appendix A.1 fixes the three selected
descriptor bodies and derived digest vectors.

An ID alone, a familiar descriptor label, or earlier support for another ID
is not a basis. Unsupported prior semantics yield operational noncompletion;
malformed or mismatched descriptor preimages do not authenticate. This basis
grants no domain admission or transferable authority.

## 3. Ordinary semantic identity

### 3.1 Mandatory independent axes

Every non-prior semantic object has a `SemanticContentId<K>`:

```text
SemanticContentId<K> = {
  foundation_epoch,
  identity_profile_id: IdentityProfileId,
  hash_suite_id: HashSuiteId,
  semantic_regime_id: SemanticRegimeId,
  subject_kind: K,
  digest: Digest<HashSuiteId>
}
```

`K` cannot be one of the three prior-meta kinds. The digest commits, under the
selected identity and hash profiles, to every field above except itself and to
the exact canonical semantic body. For a successfully authenticated
`PriorMetaAuthenticationBasis B`, canonical `MetaValueV0` body `b`, and
ordinary kind `K`, the selected v0 identity profile fixes:

```text
OrdinaryPreimageV0(B, K, b) =
    "zkc/content-id/v0\0"
    || F(A("zkc.foundation.meta.v0"))
    || F(PriorRefV0(B.identity_profile.id))
    || F(PriorRefV0(B.hash_suite.id))
    || F(A(K))
    || F(PriorRefV0(B.semantic_regime.id))
    || F(M(b))

SemanticContentId<K>(B, b) = {
  foundation_epoch = "zkc.foundation.meta.v0",
  identity_profile_id = B.identity_profile.id,
  hash_suite_id = B.hash_suite.id,
  semantic_regime_id = B.semantic_regime.id,
  subject_kind = K,
  digest = Digest[B.hash_suite.id](OrdinaryPreimageV0(B, K, b))
}

ContentRefV0(id) =
    F(A(id.foundation_epoch))
    || F(PriorRefV0(id.identity_profile_id))
    || F(PriorRefV0(id.hash_suite_id))
    || F(A(id.subject_kind))
    || F(PriorRefV0(id.semantic_regime_id))
    || id.digest
```

The selected v0 hash-suite descriptor makes `Digest` SHA-256 with a 32-octet
output. `M(b)` must strictly decode and re-encode before hashing. Stored IDs
are untrusted and are recomputed; embedded ordinary references use
`F(ContentRefV0(id))`. A text spelling, URI, carrier encoding, or
implementation object is not part of abstract identity unless its semantic
body explicitly says so.

Kinds and axes are invariant. An identity-profile ID cannot inhabit the hash
or regime axis. A protocol, module, primitive, algorithm, contract, or value
domain cannot inhabit another kind merely because bytes or record shapes
match. One ordinary authentication graph uses the exact identity-profile,
hash-suite, and regime IDs in its prior-meta basis throughout; a dependency
cannot switch any axis mid-graph.

Identity, evaluator support, and translation are separate relations:

```text
SameId(x, y)      := exact typed-tuple equality
Supports(E, x, o) := evaluator E declares operation o for exact object x
Translate(A,B,x)  := explicit directed checked transformation from A to B
```

For either identity constructor, let `p` be its complete typed preimage,
including the canonical descriptor or body. Define:

```text
Authenticates(id, p) :=
  p has the exact constructor, kind, and axes required by id
  and its canonical value strictly decodes and re-encodes
  and recomputing the selected digest from p yields id

HashBindingConflict(id, p1, p2) :=
  Authenticates(id, p1)
  and Authenticates(id, p2)
  and exact_bytes(p1) != exact_bytes(p2)
```

One closed validation scope is exactly one top-level admission, check, or
evaluation transaction, from prior-meta-basis authentication through its final
decision. It contains every exact preimage captured from that request and every
registry, resolver, or cache preimage actually consulted and successfully
authenticated while deciding it. A checker keeps an idempotent request-local
map from exact typed ID to canonical descriptor/body bytes and groups by
`SameId` before owner admission. The typed key fixes the constructor, kind,
and axes, so equality of those recorded bytes is equivalent to equality of the
complete typed identity preimage. Re-observing equal bytes is a no-op.
If it observes a `HashBindingConflict`, it reports a dedicated checker or
conformance failure and admits neither preimage as the uniquely named object;
no capability is minted from the conflicting group. The K1 reference evaluator
names this refusal `K1-HASH-BINDING-CONFLICT` and creates a fresh ledger for
each `evaluate` or `evaluate_encoded` transaction. A realization that retains
an authenticated resolver or cache entry across transactions MUST either
extend grouping and conflict quarantine across that retained scope or
reauthenticate it inside each transaction. This rule is unconditional. The
stronger global statement that one identifier has only one possible preimage
is conditional on the collision and second-preimage binding assumptions of the
digest law governing that constructor: constitutional SHA-256 for
`PriorMetaId`, and `B.hash_suite.id` for `SemanticContentId`.
An unobserved collision is therefore an Analysis assumption or quantified loss,
not a theorem of structural authentication. Because `SameId` includes the
typed kind and every axis, coincident digest octets across different typed IDs
remain unconditionally non-aliasing and are not a `HashBindingConflict`.

On this page, “rotates an ID” is shorthand for two statements: the complete
typed preimage changes unconditionally, and the derived typed identifier is
distinct conditional on the binding assumption of the digest law governing
that constructor. A change that is excluded from the preimage unconditionally
does not rotate that ID.

Decode success, common schemas, equal digest octets, or successful execution
establishes none of the other relations. If two evaluators claim the same
operation for the same authenticated inputs, disagreement is a conformance
failure; it does not create two meanings for the object.

### 3.2 Ordinary semantic modules

Every extensible semantic module is an ordinary, regime-qualified semantic
object. Its Foundation envelope has one exact canonical body:

```text
SemanticModuleCandidate = {
  imports: CanonicalSortedUniqueSeq<SemanticModuleId>,
  declaration_catalogs: CanonicalSortedUniqueSeq<DeclarationCatalog>,
  domain_payload: MetaValueV0
}

DeclarationCatalog = {
  kind: Symbol,
  bodies: CanonicalSeq<MetaValueV0>
}

SemanticModuleBody(m) = MetaRecord {
  0: MetaSeq(map(m.imports, i -> MetaBytes(ContentRefV0(i)))),
  1: MetaSeq(map(m.declaration_catalogs, c -> MetaRecord {
       0: MetaSymbol(c.kind), 1: MetaSeq(c.bodies)
     })),
  2: m.domain_payload
}

SemanticModuleId = SemanticContentId<"foundation.semantic-module">
```

A container or diagnostic module label is outside `SemanticModuleBody` and
cannot affect portable authentication, admission, declaration resolution,
evaluation, or completion. Tooling may use that metadata only after, and
outside, every portable semantic decision.

All imports must carry the module's exact `SemanticRegimeId` and are ordered by
ascending full `ContentRefV0` bytes with no duplicate. Cross-regime meaning
uses an explicit translation or bridge; it is never a module import. Catalogs
are sorted by `A(kind)` and kinds are unique. The zero-based position of a body
within its kind's catalog is its local ordinal; declaration bodies do not
repeat that ordinal. Local declarations refer to one another by typed local
ordinal.

The selected module value-domain declaration kind is exactly
`"value-domain"`, with one exact body grammar:

```text
ValueDomainDeclarationBody(name) = MetaRecord {
  0: MetaSymbol(name)
}
```

Structural formation requires exactly that kind, exactly the one-field body,
and a valid `MetaSymbol`. The body declares one opaque nominal domain; its name
and body are identity-bearing, but declaration admission does not establish
evaluator `DomainSupport`, domain membership, or canonicalization. No other
module declaration kind or body can be used as a value domain.

For every recognized declaration kind, strict decoding into that kind's exact
typed-body grammar is structural formation. A wrong outer constructor, tag,
record field set or order, or field carrier is `Malformed`. Only after an exact
typed body exists may owner-context interpretation run. An absent resolved
coordinate, a failed context-bound lift or ordinary durable body bound, or a
failed typing, owner-membership, or compatibility predicate is `Refused`,
unless the typed coordinate instead triggers the separately defined
`KindMismatch` or `Unsupported` rule. This sequence recurs at each recognized
body boundary: first form that complete body grammar and every immediate
reference carrier; then classify and resolve its complete explicit coordinate
set for owner, kind, regime, scope, and exact local position; only then
interpret any selected target body. A selected nested declaration body repeats
the same sequence. In particular, one declaration-local value type first forms
its complete recursive `DVTB`/`DSB` carrier tree, then resolves every contained
domain coordinate, and only then runs value-domain body interpretation and
schema/lift admission. Scalar, worst-case-value, schema-depth, and outward
durable-body bounds are closed schema/lift admission and refuse after
formation; malformed constructors, tags, records, and field carriers never
reach that admission predicate.

Raw typed-coordinate formation is deliberately weaker than slot admission.
Before routing, every `PriorRefV0` or `ContentRefV0` carrier must have its exact
host constructor, canonical foundation and nested prior-meta axes, and exact
32-byte digest. A malformed carrier is `Malformed`. Only a fully formed
carrier is compared with the consuming slot's required namespace, subject
kind, semantic regime, owner kind, or other semantic axis; disagreement there
is `KindMismatch`. This split applies uniformly to value-domain, failure,
primitive, module-bundle, and evaluation-contract coordinates.

Durable declaration references are the tagged union:

```text
RootDeclarationRef<K>   = (SemanticRegimeId, K, local_ordinal)
ModuleDeclarationRef<K> = (SemanticModuleId, K, local_ordinal)
DeclarationRef<K>       = Root(RootDeclarationRef<K>)
                        | Module(ModuleDeclarationRef<K>)

DeclarationRefBody(Root(r, K, n)) = MetaVariant(0, MetaRecord {
  0: MetaBytes(PriorRefV0(r)), 1: MetaSymbol(K), 2: MetaNatural(n)
})
DeclarationRefBody(Module(m, K, n)) = MetaVariant(1, MetaRecord {
  0: MetaBytes(ContentRefV0(m)), 1: MetaSymbol(K), 2: MetaNatural(n)
})

LocalDeclarationRef<K> = (K, local_ordinal)
LocalDeclarationRefBody(K, n) = MetaRecord {
  0: MetaSymbol(K), 1: MetaNatural(n)
}
```

The root and module tags are identity-bearing and never inferred from a
digest. Durable and local references are structurally distinct.
`LocalDeclarationRef` is context-local, never a `DeclarationRef`; it is valid
only while admitting a declaration body inside its containing authenticated
module, and `n` must be an exact `u64` position that exists in that same
module's `K` catalog. It carries no owner ID, cannot cross an import, escape
its aggregate, or be independently content-addressed, and may refer across
catalog kinds within that aggregate. The supported kind-specific admission law
owns finite local-reference SCC and cycle legality. Kind-specific declaration
grammars must distinguish local from durable references. A module body contains
no asserted self-ID.

Declaration bodies need a localizable type grammar because spelling a durable
reference to their own not-yet-identified module would create a content-hash
cycle. Its exact domain-reference union is:

```text
DeclarationDomainRef = Local(LocalDeclarationRef<Kd>)
                     | Durable(DeclarationRef<Kd>)

DeclarationDomainRefBody(Local(K, n)) = MetaVariant(
  0, LocalDeclarationRefBody(K, n))

DeclarationDomainRefBody(Durable(d)) = MetaVariant(
  1, DeclarationRefBody(d))

DeclarationValueTypeBody(DT) = MetaRecord {
  0: DeclarationDomainRefBody(DT.domain),
  1: DeclarationSchemaBody(DT.schema)
}
```

`DeclarationSchemaBody` has the same nine tags, scalar bounds, finite-tree
limits, and canonical field/case order as `SchemaBody`, but every recursive
child type is another `DeclarationValueTypeBody`. A local domain reference
must have kind `"value-domain"` and resolve in the same aggregate to an exact
admitted `ValueDomainDeclarationBody`; a local reference of any other kind
cannot inhabit the domain position.

After module `m` and its transitive import closure authenticate, `LiftType_m`
recursively produces an outward durable `ValueType`:

```text
LiftRef_m(Local(K,n)) = Module(m,K,n)
LiftRef_m(Durable(Root(r,K,n))) = Root(r,K,n), only when
  r = m.semantic_regime_id
LiftRef_m(Durable(Module(t,K,n))) = Module(t,K,n), only when
  t != m and t is in m's authenticated transitive import closure

LiftType_m(DT) = ValueType(
  LiftRef_m(DT.domain),
  LiftSchema_m(DT.schema))
```

`LiftSchema_m` preserves the exact schema constructor and scalar parameters
and applies `LiftType_m` to every nested type. A durable spelling of `m` from
inside `m`, a missing local target, or a durable target outside the allowed
root/import scope refuses. Every resulting
`CanonicalValueTypeBody(LiftType_m(DT))`, including every recursively lifted
nested type, must independently pass the ordinary same-regime, schema,
canonical-body, and constitutional bounds. A compact
`DeclarationValueTypeBody` fitting its own envelope is insufficient. Lifting
is context-bound admission, not a semantic object or content-addressable
translation. Supported kind-specific declaration bodies use this localizable
form wherever they carry types and compare the lifted result with their
outward semantics. Foundation still does not scan an unknown declaration body
for reference-shaped bytes.

For a strictly decoded algorithm candidate `alg` and its term `t`, define
structurally, before owner typing:

```text
DirectPrimitiveRefs(t) =
  CanonicalSortedUniqueSeq of every exact SemanticPrimitiveRef occurring
  in a PrimitiveCall node of t

DirectDeclarationRefs(alg) =
  all declaration references explicitly present in alg's input types,
  constants, term type annotations, failure constructors, and the
  declaration component of DirectPrimitiveRefs(alg.term)

DirectModuleRoots(alg) =
  CanonicalSortedUniqueSeq {
    r.owner | r in DirectDeclarationRefs(alg), r is Module(...)
  }

AuthenticatedImports_B(m, P) = imports decoded from P[m], defined only if
  P[m] strictly decodes and authenticates as m under basis B

RequiredModuleClosure_B(alg, P) = least X such that
  X = set(DirectModuleRoots(alg)) union
      { imported | m in X, imported in AuthenticatedImports_B(m, P) }
```

`SemanticPrimitiveRef` contains both an exact
`SemanticContentId<"foundation.semantic-primitive">` and its exact
`ModuleDeclarationRef<"semantic-primitive">`; therefore its owner is available
without guessing or scanning an ambient registry. Primitive IDs are direct
algorithm dependencies, but primitive candidates are not nodes in the
module-import closure. The derived list retains every distinct exact
`(primitive ID, declaration reference)` pair and deduplicates only an exactly
repeated pair. Each retained pair authenticates before primitive support
lookup. A failed asserted ID/body pair is `Malformed`; two distinct
pair-authenticated declaration bodies under one typed ID are a
`HashBindingConflict`; and the same declaration body cannot authenticate as
two IDs under one fixed deterministic identity basis.

Authentication receives one canonical `ModulePreimageBundle P`, a finite map
from asserted `SemanticModuleId` to the exact canonical bytes of its
`SemanticModuleBody`, sorted by full `ContentRefV0` bytes with no duplicate
key. The typed bundle contains at most `2^14` entries; its entry count is
checked before any key is iterated or the map is copied. This is an observable
regime-owned admission bound. The future serialized request carrier must add
its own aggregate byte bound; K1's typed-candidate instrument does not claim
that raw-carrier limit. Every map key's complete ID carrier, semantic-module
kind, and selected regime are checked before the map is copied or its key set
is compared with the required closure. This inspects no unreferenced module
body: an extra fully formed same-regime module key still refuses solely by the
key-set comparison. Canonical depth-first traversal visits sorted direct roots and each
module's sorted imports. It authenticates a reached candidate before its
imports become `AuthenticatedImports_B`; undefined authenticated imports stop
the traversal. It then requires
`keys(P) = RequiredModuleClosure_B(alg, P)` after traversal. Every reached key
has therefore been recomputed from its body before its imports can affect the
closure. An unreferenced extra key is rejected by that exact key-set comparison
without decoding, authenticating, or otherwise interpreting its body. This
ordering rejects:

- a missing or extra node;
- a duplicate, unsorted, or wrong-kind import;
- a cross-regime import;
- a stored-ID mismatch; or
- a cycle.

For each reached key, strict body decode and ID recomputation precede reading
that body's `imports`; an unauthenticated candidate cannot steer missing-node
or cycle classification.

Nodes and edges are counted uniquely. A shared diamond is authenticated once,
not expanded once per path. A genuinely mutually defined extension must be a
single aggregate module with local ordinals. The selected closure limit is
`2^14` unique module nodes and `2^14` import edges; reaching either exact bound
is allowed and crossing it deterministically refuses.

Declared imports are the only generic structural authority for a module's
dependency closure. Foundation does not scan an arbitrary declaration body for
bytes that resemble references. After module authentication, a supported
kind-specific declaration-admission law may interpret references in that
kind's body. A local reference must resolve inside the same module under the
rule above; every durable reference it recognizes must target the same regime
root or a module already in the declaring module's authenticated import
closure.
An unrecognized kind in a generic extension-capable declaration position is
`Unsupported` rather than receiving a guessed reference grammar. A formed
coordinate in an exact `K`-typed slot that carries another kind is instead
`KindMismatch`. An unreferenced unknown catalog is inert: it confers no
semantics and is not interpreted. An unused import remains identity-bearing
module content, but a consuming algorithm cannot add an unrelated module
outside the closure selected by its direct roots.

Only after the basis and module bundle authenticate may a declaration
reference resolve. `Root(r)` resolves against the exact authenticated regime
descriptor; `Module(r)` resolves against `P[r.owner]`. Resolution requires an
existing ordinal of exactly kind `K`, then returns that declaration's exact
canonical semantic body. For a primitive reference, recomputing the ordinary
primitive ID from its exact declaration-reference body must equal the carried
primitive ID; the authenticated owner module then commits the declaration
body at that ordinal. Value-domain and failure references likewise acquire
meaning only from their authenticated owner declaration. Names, registry
search, equal digest octets, or evaluator support cannot resolve a reference.
Owner typing may derive success and failure references only by propagation
from those resolved declarations; an inferred reference outside the
authenticated root and `RequiredModuleClosure_B` is a checker defect.

A subject cites only the modules it uses. Adding, retiring, or replacing an
unrelated module does not rotate the regime root or unrelated subject IDs.
Changing a used module does rotate dependent identities.

## 4. Domain-indexed canonical values

An exact value-domain reference is the following closed refinement of the
declaration-reference union in Section 3.2:

```text
ValueDomainRef = Root(RootDeclarationRef<
                   "foundation.root-value-domain">)
               | Module(ModuleDeclarationRef<"value-domain">)

Root value-domain ordinals are exactly 0..8.
Each module value-domain reference must resolve to an exact admitted
ValueDomainDeclarationBody.

ValueDomainRefBody(d) = DeclarationRefBody(d)
RegimeOf(Root(r, _, _))   = r
RegimeOf(Module(m, _, _)) = m.semantic_regime_id

FiniteSchema := FiniteValueSchema
ValueType = (domain: ValueDomainRef, schema: FiniteSchema)

CanonicalValue<T: ValueType> = {
  type: T,
  value: admitted mathematical Value<T.domain>,
  datum: T.domain's unique admitted MetaValueV0 representative,
  canonical_bytes: M(datum)
}

CanonicalValueIdBody(T, datum) = MetaRecord {
  0: ValueDomainRefBody(T.domain),
  1: SchemaBody(T.schema),
  2: datum
}

CanonicalValueId<K>(B, T, datum) =
  SemanticContentId<K>(B, CanonicalValueIdBody(T, datum))
```

`CanonicalValueId` is defined only after exact domain admission of `datum` at
`T`; carrier-shape checking alone cannot mint it. `K` is an ordinary,
non-prior subject kind and `B.semantic_regime.id = RegimeOf(T.domain)`.
Private or otherwise unaddressed values need no ID. Content addressing never
authorizes exposure.

For exact resolved declaration body `body(d)`, define the support gate:

```text
DomainSupport(E, d) :=
  Supports(E, (d, body(d)), PortableValueDomainAdmissionV0)
```

`PortableValueDomainAdmissionV0` means that `E` implements the exact
declaration-owned, total deterministic schema-admission, datum-membership,
canonical decode/encode, and equality laws for that exact reference and body.
Support for another ordinal, owning module, or body does not transfer. The
selected regime provides this operation intrinsically for the nine root
structural domains in Appendix A.2. A module-owned domain is opaque: its
`FiniteValueSchema` is only a finite carrier-shape bound and never proves owner
membership. It can be admitted only after `DomainSupport(E,d)`; otherwise use
of it is operationally unsupported before its payload is domain-interpreted or
owner-admitted.

The root/module tag, complete typed owner ID, exact declaration kind, and
ordinal therefore have the single encoding already defined by
`DeclarationRefBody`; a human domain name is not an identity. The selected v0
base-value catalog kind is exactly `"foundation.root-value-domain"`; the
module-owned value-domain catalog kind is exactly `"value-domain"`. A
root-owned reference is valid only when its owner equals the consumer's exact
`SemanticRegimeId`. A module-owned reference is valid only when its module ID
carries that same regime and its declaration resolves through the exact
authenticated module closure. Mere resolution establishes none of its domain
laws. The selected root laws provide those laws intrinsically. A module
declaration establishes only its opaque nominal identity; exact
`DomainSupport` supplies membership, mathematical equality, the unique mapping
to an admitted structural datum, strict decoding, and semantic decode failures
for that exact declaration. Exposure policy remains owner policy, and a domain
wire codec remains separate from this portable semantic encoding.

Every type and declaration reference reachable from one portable algorithm,
including nested sequence/record/sum members, primitive signatures, failure
payloads, and the derived success type, must have exactly that algorithm's
regime. Same digest octets, the same schema, or a checked translation do not
satisfy this same-regime rule.

Foundation requires:

1. every admitted value has exactly one canonical semantic encoding;
2. strict decode of that encoding returns the same domain value;
3. a noncanonical value carrier refuses as malformed before execution; a
   domain algorithm parsing an already admitted canonical byte value may
   instead complete with an exact declared semantic failure;
4. matching bytes under different domain IDs do not establish equality;
5. private values are neither content-addressed nor exposed without an owning
   contract; and
6. a wire codec depends on an already identified value domain, never the
   reverse.

The shared schema vocabulary contains unit, Boolean, bounded natural and
signed integers, bounded bytes and symbols, records, tagged sums, and bounded
sequences. Sorted-unique sequences can represent maps and sets. Fields,
extension fields, groups, polynomials, matrices, proof objects, oracle values,
and transcript states remain domain declarations with exact mathematical
parameters. Root structural records, variants, and sequences may contain
already admitted module-domain values as members; their outer structural shape
does not confer admission on those members.

Every `FiniteSchema` has a finite maximum canonical size, at most `2^14`
schema nodes, and root-zero semantic depth at most `48`; reaching either local
structural bound is allowed only if the schema's exact canonical type body and
every structurally shaped value also fit the constitutional byte, node, child-
edge, and depth bounds. These are refinements of the direct `ValueType`
carrier, not a later predicate over an otherwise exact direct type. A schema
that violates a scalar, ordinal, finite-tree, `Worst`, or canonical type-body
bound therefore cannot form a `CanonicalValueTypeBody`; if presented directly
in an algorithm or value header, it is `Malformed`. A raw declaration-local
`DeclarationSchemaBody` is intentionally different: its complete grammar
forms before contextual lift and closed schema admission, whose failure is
`Refused`. A maximum completion schema derived from already admitted types can
likewise be `Refused` if the tagged union does not fit its separate bound.
These semantic-schema limits are distinct from the `384`-deep `MetaValueV0`
carrier envelope needed to encode nested schema and term wrappers. Appendix
A.2 fixes the selected schema and payload bodies.

## 5. Portable semantic functions

### 5.1 Denotation boundary

Only a portable term and its admitted exact primitive calls determine a
portable semantic-function result. A domain predicate, checker, or external
operation may expose the same ABI, but it cannot occupy a portable-algorithm
position without a separately identified checked correspondence to that exact
portable denotation.

### 5.2 One small canonical calculus

A portable algorithm contains an algorithm kind, ordered typed input context,
one canonical term, and the exact semantic dependencies induced by that term.
The selected core grammar contains only:

- argument references and constants;
- `let`;
- record construction and projection;
- tagged injection and exhaustive case;
- Boolean conditional;
- explicitly capacitated sequence construction, length, strict index, and
  bounded append;
- calls through exact `SemanticPrimitiveRef` values;
- typed semantic failure; and
- one `BoundedIterate` constructor.

Every generic structural constructor and eliminator requires the exact root
outer domain for its shape: root Boolean for conditionals, root record for
construction/projection, root variant for injection/case, root sequence for
construction/length/index/append and sequence iteration, and root natural for
indices and range iteration. These names abbreviate the exact root references
in Appendix A.2; schema-shape equality is insufficient. Nested members may
have any already admitted same-regime domain. A module-owned value can enter a
term only as an admitted literal or input, or as the result of an exact
supported primitive, and every such boundary rechecks its exact domain law.
Richer module-domain introductions are primitives, not generic structural
constructors.

`SequenceConstruct(T, c, [e_0, ..., e_(k-1)])` carries capacity `c` in
authenticated syntax; there is no omitted-capacity default. Its key rule is:

```text
Gamma |- e_i : T for every 0 <= i < k     k <= c <= SequenceCapacityLimit
AdmittedSchema(RootSeq(T,c))
----------------------------------------------------------------------------
Gamma |- SequenceConstruct(T, c, [e_0, ..., e_(k-1)]) : RootSeq<T, c>
```

The authenticated v0 regime root fixes `SequenceCapacityLimit = 2^14`.

`SequenceLength : RootSeq<T,c> -> RootNat[0,c]`; strict index and bounded
append likewise require a root-sequence source and use their declared typed
failures rather than trapping or widening `c`.

Let `ContinueBreak<S,R>` be the exact root tagged sum
`{0: Continue(S), 1: Break(R)}`, and let
`IndexType<N> = RootNat[0,max(0,N-1)]`. An iteration source is either
`xs : RootSeq<T,N>` in canonical sequence order, or `range(n)` with
`n : RootNat[0,N]`, which yields `(i,i)` for `0 <= i < n` and uses
`T = IndexType<N>`. No index value is produced when `N = 0`. The key typing
equation is:

```text
0 <= N <= 2^14
Gamma |- source : IterSource<T,N>       Gamma |- initial : S
IndexType<N>, T, S, Gamma |- body : ContinueBreak<S,R>
----------------------------------------------------------------
Gamma |- BoundedIterate(source, initial, body) : ContinueBreak<S,R>
```

Inside the body, de Bruijn index `0` is the source index, `1` the item, and `2`
the state; indices at least `3` address `Gamma` shifted by three. Each
`Continue(s')` requires `s' : S`; the first `Break(r)` returns
`Break(r) : ContinueBreak<S,R>` immediately. Exhausting the source returns
`Continue(final_state)`. The source's authenticated maximum `N` is the static
iteration bound; an evaluator cannot substitute a guessed or host limit.

Map, zip, fold, find, argmin, pairwise traversal, canonical sort, duplicate
detection, tree traversal, and finite worklists are derived libraries or
domain-owned algorithms. They are not independent core constructors. This
keeps one iteration law and avoids freezing a universal tree, pairing, or
worklist policy into Foundation.

Binders use canonical structural ordinals. The authenticated regime root fixes
the constructor tags and canonical field order for every term form, a maximum
of `4096` term nodes, and root-zero term depth `48`. Reaching either bound is
allowed only when the resulting `CanonicalTermBody` and enclosing
`PortableAlgorithmBody` also fit every constitutional `MetaValueV0` bound; the
local node/depth limits do not promise that every shape at those limits is
representable. Identity follows typed syntax, not source labels, printer
spelling, evaluation traces, compiler normalization, or extensional
equivalence. The language has no general recursion, cyclic calls,
callbacks, exceptions as meaning, dynamic code, ambient registries, I/O,
clocks, implicit randomness, reflection, unordered iteration, or
implementation-defined arithmetic.

Appendix A.3 fixes every selected constructor tag and payload field.

### 5.3 Derived function ABI

Typing derives both the success type and the complete typed-failure row:

```text
SemanticFailureType = {
  declaration: ModuleDeclarationRef<"semantic-failure">,
  payload_type: ValueType
}

LocalSemanticFailureDeclarationBody(name, DT) = MetaRecord {
  0: MetaSymbol(name),
  1: DeclarationValueTypeBody(DT)
}

CanonicalSemanticFailureTypeBody(f) = MetaRecord {
  0: DeclarationRefBody(Module(f.declaration)),
  1: CanonicalValueTypeBody(f.payload_type)
}

SemanticFunctionType = {
  inputs: OrderedSeq<ValueType>,
  success: ValueType,
  failures: CanonicalSortedUniqueSeq<SemanticFailureType>
}
```

The failure row is the canonical union of explicit failure constructors and
the declared failure alternatives of exact primitive calls in the typed term.
It is sorted by `M(CanonicalSemanticFailureTypeBody(f))`; exact duplicates
collapse and conflicting payload types for one declaration refuse. The
declaration module and payload type must both carry the algorithm's exact
regime. A supported `"semantic-failure"` catalog body is exactly
`LocalSemanticFailureDeclarationBody(name, DT)` with one nonempty symbol name.
After its owner module `m` authenticates, `LiftType_m(DT)` must equal
`f.payload_type` exactly; the outward failure type never retains a local
reference.
An authored output or failure manifest and every diagnostic label have no
portable authority. They are excluded from identity and portable evaluators
must ignore them during authentication, admission, evaluation, and completion.
Changing only such metadata therefore cannot rotate the algorithm ID or alter
the semantic outcome.

Semantic completion is one of:

```text
Success(CanonicalValue<success>)
DomainFailure(failure_type, CanonicalValue<failure_type.payload_type>)
```

Both forms are values of the derived ABI. A missing provider, exhausted
evaluation budget, malformed object, or checker defect is not a
`DomainFailure`.

### 5.4 Exact primitive boundary

Every callable leaf is carried as:

```text
SemanticPrimitiveRef = {
  id: SemanticContentId<"foundation.semantic-primitive">,
  declaration: ModuleDeclarationRef<"semantic-primitive">
}

SemanticPrimitiveBody(ref) =
  DeclarationRefBody(Module(ref.declaration))

CanonicalSemanticPrimitiveRefBody(ref) = MetaRecord {
  0: MetaBytes(ContentRefV0(ref.id)),
  1: DeclarationRefBody(Module(ref.declaration))
}

LocalSemanticPrimitiveDeclarationBody = MetaRecord {
  0: MetaSymbol(name),
  1: MetaNatural(version_u64),
  2: MetaBytes(type_rule_source),
  3: MetaBytes(operation_law_source),
  4: MetaSeq(LocalDeclarationRef<"semantic-failure">),
  5: MetaSymbol(state_effect_discipline)
}
```

The primitive ID is recomputed from that exact declaration-reference body
under the declaration module's regime. The referenced module ID already
commits the declaration body, so copying that body into the primitive preimage
would add no meaning. After module authentication, a semantic-primitive
declaration first forms exactly as
`LocalSemanticPrimitiveDeclarationBody`. Every local failure reference must
resolve in the same authenticated module, and its exact failure body and
localizable payload type must form and lift successfully before evaluator
support is consulted. The two source byte strings are immutable normative
sources interpreted only by the selected supported kind law; no ambient text
parser or name registry supplies their meaning. The supported interpretation
then authenticates at least:

- its owning module and local declaration;
- exact input and derived output rules;
- exact typed-failure alternatives;
- normative operation law or immutable normative source;
- semantic dependencies and state/effect discipline; and
- semantic bounds, distribution, canonicality, and side conditions where
  applicable.

Its denotation is a total deterministic function of the exact admitted
arguments, returning either its derived success value or one declared typed
failure. Semantic state is an explicit argument and result. Ambient mutation,
freshness, I/O, and supplier behavior require an external capability contract
and cannot be hidden inside a portable primitive.

A call contains that exact reference; names and versions alone are
insufficient. The type checker derives the call result and failures from the
authenticated resolved declaration. Unknown, wrong-kind, wrong-regime,
unresolved, ID-mismatched, or unsupported primitive references fail closed.

Provider code and build identity are outside primitive denotation unless made
semantic explicitly. Lack of a provider is operational noncompletion. Provider
disagreement with an admitted primitive is a conformance defect, never an
alternative semantic answer.

Hashes, XOF or duplex transitions, field and group operations, MSMs, pairings,
and exact numeric operations belong here only when their complete meaning is
fixed. Prover strategies, fresh-coin supply, witness supply, setup, proof
generation, storage, parsing, and opaque adapters remain external operations.

### 5.5 Totality and direct dependencies

Totality follows from finite syntax, exhaustive cases, exact-root structural
operations, bounded sequences, the single bounded iterator, acyclic module
dependencies, supported total value-domain admission laws, and admitted total
primitives. A mathematically partial primitive returns a declared typed
failure; it never traps. There is no authored “totality evidence” field.

The algorithm's exact primitive references and module roots are the functions
in Section 3.2, not authored assertions. Its canonical semantic body is:

```text
PortableAlgorithmCandidate = {
  algorithm_kind: Symbol,
  ordered_inputs: CanonicalSeq<ValueType>,
  term: CanonicalTerm
}

PortableAlgorithmBody(alg) = MetaRecord {
  0: MetaSymbol(alg.algorithm_kind),
  1: MetaSeq(map(alg.ordered_inputs, CanonicalValueTypeBody)),
  2: CanonicalTermBody(alg.term),
  3: MetaSeq(map(DirectPrimitiveRefs(alg.term),
                 CanonicalSemanticPrimitiveRefBody))
}

PortableAlgorithmId(B, alg) =
  SemanticContentId<"foundation.portable-algorithm">(
    B, PortableAlgorithmBody(alg))

PortableAlgorithmRef := PortableAlgorithmId
```

Here `CanonicalTerm` means strictly decoded canonical structural syntax formed
by Sections 5.2 and A.3 and satisfying the term/body envelope limits. It does
not by itself claim declaration resolution, owner typing, domain support, or
admission; those occur after identity at the precedence boundaries in Section
7.2. It is not a carrier AST or printer output. `algorithm_kind` is an
identity-bearing symbol, not a type parameter or diagnostic label.

`CanonicalSemanticPrimitiveRefBody` contains both fields of the reference.
`DirectPrimitiveRefs` is sorted lexicographically by
`(ContentRefV0(ref.id), SemanticPrimitiveBody(ref))`, with only exact-pair
duplicates removed. `DirectModuleRoots` is sorted by `ContentRefV0(module)`.
The authenticated regime root fixes `CanonicalValueTypeBody` and
`CanonicalTermBody`; implementations may not substitute printer or carrier
bytes. When a `PortableAlgorithmRef` is embedded in another semantic body, it
uses `MetaBytes(ContentRefV0(id))` unless that body's exact schema states a
stronger wrapper.

The direct primitive sequence in the body must equal the syntax-derived
sequence; it cannot omit or pad it. `DirectModuleRoots` is derived only and is
not another authored or hashed summary. The supplied `ModulePreimageBundle`
must equal `RequiredModuleClosure_B` under Section 3.2. There is no mixed
“semantic dependency preimage closure”: primitive references remain exact
direct references resolved through their authenticated module declarations,
while only module imports form the transitive preimage DAG.

Termination does not imply acceptable work, output size, constant-time
behavior, unbiased sampling, native cost, circuit cost, or any security
property. Those remain separate contracts or domain laws.

## 6. Non-aliasing external boundaries

A derived portable function ABI does not become a capability, checker, wire
codec, or endpoint contract through field-shape equality. Those domain-owned
objects add meanings that Foundation does not define. Crossing such a
namespace requires an exact, separately identified checked bridge.

## 7. Evaluation semantics and deterministic control

### 7.1 Order belongs to the language

Evaluation is deterministic, strict, and call-by-value. Subterms are evaluated
in canonical syntax order: binding value before body; record fields by ordinal;
sequence elements and primitive arguments left to right; scrutinee before only
the selected case; condition before only the selected branch; and iterator
source before initial state, then items sequentially in source order. `Break`
ends the iterator immediately.

These order rules are part of the term language and therefore of algorithm
meaning. An evaluation contract cannot change them.

### 7.2 Content-addressed evaluation contract

An `EvaluationContract` is an ordinary regime-qualified semantic object. It
identifies only deterministic control rules. The selected v0 body is:

```text
EvaluationContractV0 = {
  version: 0,
  term_entry_units: Natural,
  iteration_item_units: Natural,
  validation_precedence: PortableEvaluationPrecedenceV0,
  completion_measure: TaggedCanonicalCompletionV0,
  static_bound_rule: MaximumCompletionSchemaV0,
  primitive_work_rules:
    CanonicalSortedUniqueMap<
      SemanticContentId<"foundation.semantic-primitive">,
      PrimitiveWorkFormulaV0>
}

PrimitiveWorkFormulaV0 =
    Fixed(constant: Natural)
  | SumByteLengths(argument_indices: CanonicalSortedUniqueSeq<U64Natural>,
                   constant: Natural)
  | MinByteLengthNatural(byte_argument: U64Natural,
                         natural_argument: U64Natural,
                         constant: Natural)
```

`U64Natural` is the closed interval `0 .. 2^64 - 1`; that positional-index
limit is formula syntax, not a claim that the named primitive has that many
arguments.

Their canonical bodies use variant ordinals `0`, `1`, and `2` in that order:

```text
FormulaBody(Fixed(c)) = MetaVariant(0, MetaNatural(c))
FormulaBody(SumByteLengths(I,c)) = MetaVariant(1, MetaRecord {
  0: MetaSeq(map(I, MetaNatural)), 1: MetaNatural(c)
})
FormulaBody(MinByteLengthNatural(i,j,c)) = MetaVariant(2, MetaRecord {
  0: MetaNatural(i), 1: MetaNatural(j), 2: MetaNatural(c)
})

EvaluationContractBody(C) = MetaRecord {
  0: MetaNatural(0),
  1: MetaNatural(C.term_entry_units),
  2: MetaNatural(C.iteration_item_units),
  3: MetaSymbol("portable-evaluation-precedence-v0"),
  4: MetaSymbol("tagged-canonical-completion-v0"),
  5: MetaSymbol("maximum-completion-schema-v0"),
  6: MetaSeq(map(C.primitive_work_rules, (p,f) -> MetaRecord {
       0: MetaBytes(ContentRefV0(p)), 1: FormulaBody(f)
     }))
}

EvaluationContractId(B, C) =
  SemanticContentId<"foundation.evaluation-contract">(
    B, EvaluationContractBody(C))
```

Here `B` is the already authenticated prior-meta basis. The resulting
`EvaluationContractId(B,C)` has regime axis `B.semantic_regime.id`, and every
primitive key must carry that same regime.

Rules are ordered by ascending full `ContentRefV0` bytes and have no duplicate
key. Each `SumByteLengths` index sequence is ordered by ascending natural value
with no duplicate. `FormulaSyntaxAdmissible` checks the exact tag, natural
constant, u64 positional indices, sorted uniqueness, and constitutional body
bounds without consulting a primitive ABI. The primitive ID already commits
its tagged declaration reference, so repeating the declaration locator in this
charging table would add no meaning.

For admitted primitive arguments `a`, the three formulas return respectively
`constant`, `constant + sum(length(a[i].byte_value))`, and
`constant + min(length(a[byte_argument].byte_value),
a[natural_argument].natural_value)`. Indices must be in range and the named
ABI positions must have the required structural byte or natural schema;
otherwise `FormulaAdmittedFor(formula, primitive_abi)` is false. Boundary 3
requires syntax admission for every contract rule. Boundary 10 requires
`FormulaAdmittedFor` only for rules keyed by exact direct primitives of the
algorithm; an unused rule remains identity-bearing, must be syntax-admissible,
and grants no ABI applicability. Formula arithmetic is over mathematical
naturals. An unknown formula tag fails structural formation and is
`Malformed`.
Extending the formula grammar requires a new evaluation-contract schema
version, body, and ID; no later version may reinterpret this v0 body.

The contract therefore fixes:

- natural-valued term-step and iteration-item charges;
- exact primitive-work formulas keyed by primitive ID;
- validation and preflight precedence;
- static maximum-completion derivation; and
- canonical completion-size measurement.

It does not define term typing, evaluation order, primitive denotation,
semantic failure, or algorithm identity. Changing a charge schedule rotates
the evaluation-contract ID but not an algorithm ID. Per-request limits are
ephemeral inputs and rotate neither ID.

An evaluation request supplies an algorithm candidate with asserted ID,
typed input headers and canonical payload bytes, the exact
`PriorMetaAuthenticationBasis`, the exact module-preimage bundle, an exact
evaluation-contract ID and body, and a finite deterministic budget.
Evaluation consumes one immutable admitted request snapshot. Module and input
material is captured exactly once when its respective validation boundary is
reached; every later semantic step uses only the captured material and never
rereads a mutable producer or source. Capture preserves the validation order
below and cannot make a later boundary observable early. The concrete host
carrier and snapshot mechanism are realization and evidence concerns, not
portable semantic-root law.
That request-local budget and its resulting measurement have exactly the
following four natural-valued dimensions:

```text
PortableEvaluationLimitsV0 = {
  maximum_term_units,
  maximum_iteration_units,
  maximum_primitive_work,
  maximum_completion_bytes
}

PortableEvaluationChargeV0 = {
  term_units,
  iteration_units,
  primitive_work,
  completion_bytes
}
```

They are evaluator-control records, not semantic values, content-addressed
objects, or a universal resource algebra. Each limit is checked before its
counter is advanced; completion bytes remain zero until a complete canonical
envelope exists.
`PortableEvaluationPrecedenceV0` is the following first-observed-boundary
order:

1. validate the request-limit header as finite mathematical naturals;
2. authenticate and establish support for the complete prior-meta basis;
3. validate the evaluation-contract typed header, strictly decode its body,
   authenticate its ordinary ID, validate closed formula syntax, canonical
   key order, and same-regime references, and establish evaluator support for
   that exact contract;
4. validate the subject's outer typed header and require the portable-
   algorithm namespace;
5. strictly decode the canonical algorithm structure, including each literal
   datum's constitutional `MetaValueV0` form and bounds, and authenticate its
   ordinary ID, without yet claiming declaration resolution, schema match,
   or owner typing;
6. derive structural direct references, authenticate the exact required
   module closure, and resolve every declaration reference;
7. establish supported kind-specific interpretation for every resolved
   declaration body; syntax-directly derive carrier types without
   domain-admitting literals, derive the success and complete failure ABI,
   check the canonical direct-primitive sequence, compute the complete set of
   reachable `ValueType` values, require `DomainSupport` for that whole set,
   and only then owner-admit literal data in canonical syntax order;
8. validate input headers in argument order: arity, carrier shape, and exact
   `ValueType`; no input payload is decoded before all headers pass;
9. strictly decode and domain-admit canonical input payloads in argument
   order;
10. establish evaluator support for every exact direct primitive and require
    exactly one ABI-compatible admitted work formula keyed by its ID; unused
    contract rules do not enlarge the algorithm's module closure;
11. derive and preflight the maximum tagged completion size; then
12. enter semantic evaluation.

A failure at one boundary prevents inspection whose semantic interpretation
belongs to a later boundary. In particular, malformed canonical payload bytes
cannot outrank a wrong input domain header, and neither can be interpreted
before algorithm typing has established the expected type. Missing or invalid
owner declarations therefore precede unsupported-domain classification;
unsupported reachable domains precede input arity, header, and payload defects.

On entry to each term node, `term_entry_units` is charged. Before each iterator
item, `iteration_item_units` is charged; before a primitive denotation is
entered, its formula result is charged. Charges are mathematical naturals.
Each combined counter update is checked and committed atomically before the
associated work. No overflow, host integer conversion, or failed operation can
leave a partial charge or semantic result.

For derived function type `(success, failures[0..q))`,
`TaggedCanonicalCompletionV0` encodes success as case `0` and failure `i` as
case `i+1`, each with only its canonical payload. `MaximumCompletionSchemaV0`
is the maximum canonical byte size over the success schema and every failure
payload schema with its exact tag and framing. That maximum is preflighted
before term entry; the exact emitted envelope is charged on completion. An
exact limit may complete, while one less must stop before executing work whose
maximum result cannot fit.

Foundation standardizes only abstract dimensions shared by its consumers:
term steps, iteration items, primitive work under the selected formulas, and
canonical completion bytes. A domain owns field-operation, sponge, pairing,
native, circuit, search, and other cost models. There is no universal
`Resource` value or resource judgment.

An authenticated retry count or traversal length is semantic input. Exhausting
it may yield a declared failure such as `SamplingFailed`. Exhausting an
independent evaluator budget yields no semantic completion.

## 8. Completion and operational noncompletion

Foundation requires consumers to preserve the following distinctions but does
not define one universal `Result`, payload enum, diagnostic vocabulary, or
multi-defect precedence for every domain. Section 7.2 fixes only the selected
portable-evaluation contract's precedence:

- semantic `Success` and typed `DomainFailure` are completed ABI values;
- `Unsupported` means an exact same-kind, same-regime authenticated basis,
  subject, or request pair lacks evaluator-selected interpretation or coverage,
  including an absent primitive provider or cost rule;
- `MissingDependency` means a required exact named preimage is absent after its
  typed coordinate forms;
- `KindMismatch` means an exact formed typed subject, reference, or header has
  the wrong namespace, kind, regime, arity, or exact ABI coordinate;
- invalid carrier, noncanonical bytes, or failed structural formation before
  a closed semantic predicate is defined is `Malformed`, while an exact
  structurally well-formed candidate that, after all required authentication,
  reaches and fails a supported closed resolution, typing, owner-admission, or
  compatibility predicate is `Refused`;
- strict input decode failure is therefore `Malformed`, while post-decode
  input owner-admission failure is `Refused`;
- an absent primitive cost rule is `Unsupported`, while a present admitted
  rule incompatible with the exact call ABI is `Refused`;
- `DeterministicLimitExceeded` means a declared finite request, closure, or
  evaluation bound was exhausted before the associated work and carries no
  semantic answer; and
- `CheckerFailure` means selected evaluator support, a derived ABI, a provider
  postcondition, or one request-local typed-ID binding is internally
  inconsistent; it differs from every domain failure.

The owning evaluator fixes privacy-safe diagnostic payloads without changing
the semantic outcome classes. A provider returning a value outside an
admitted ABI is a checker or conformance defect, not a semantic failure. An
incidental host allocation failure, process death, or unavailable device may
produce no record at all and cannot be relabeled as a domain outcome.

## 9. Authentication, admission, and authority

Sections 2--3 define structural identity and dependency authentication.
Section 7.2 alone defines the portable evaluator's first-boundary order; other
consumers own their admission sequences. None of these mechanisms establishes
that an owner predicate succeeds.

Authentication produces no domain capability. The owner then evaluates its
admission predicate under an explicit policy and, where applicable, evaluation
contract. Only successful owner admission can mint an immutable, narrow,
process-local capability. Serialization, copying, FFI, caching, evidence, or a
prior admission record never transports authority.

No malformed, unsupported, mismatched, refused, over-limit, or checker-failed
attempt returns a partial semantic object or capability.

## 10. Domain ownership and consumer contract

Foundation owns only the mechanisms on this page. Each consumer owns:

- its semantic-regime descriptor under the prior-meta root grammar;
- its extensible declaration catalogs and domain payloads under the Foundation
  module envelope;
- subject semantic-body schemas, adequacy, and admission predicates;
- value-domain mathematics and codecs;
- algorithm kinds, primitive selection, predicates, and failure declarations;
- capability, checker, wire, and endpoint contract bodies;
- domain resource dimensions and policies; and
- migrations and checked cross-domain relations.

## 11. Evolution laws

- A change to a regime root, used module, primitive denotation, function term,
  value-domain membership or canonicalization, identity profile, or hash suite
  changes the complete typed preimage. Conditional on the governing digest
  law's binding assumption, this creates a distinct typed ID. A changed value-domain
  declaration changes the preimages of its owning module (or regime root) and
  every affected value type and dependent subject.
- Adding or changing an unused module does not rotate the regime root or an
  unrelated subject.
- A carrier rendering, diagnostic relabel, provider rebinding, observation
  record, stricter unobservable host/evaluator safety limit, or evaluator bug
  fix does not rotate semantic identity. An admission or evaluation bound made
  observable by an identity-bearing semantic contract rotates that owning
  profile, regime, module, algorithm, or evaluation contract instead.
- Cross-regime preservation is an explicit checked relation. Translation never
  transfers prior admission or authority.
- Unknown extensions refuse or remain unsupported; they are never interpreted
  as the closest known meaning.

## 12. Selected limits and non-claims

The selected model deliberately does not provide:

- a general-purpose VM or arbitrary user code;
- a universal field, group, polynomial, transcript, oracle, proof, theorem,
  result, resource, or judgment algebra;
- intrinsic distribution, independence, constant-time, soundness, zero
  knowledge, or other security guarantees;
- automatic provider conformance or implementation correctness;
- protocol, relation, analysis, compiler, or endpoint admission;
- unconditional global one-ID/one-preimage binding or collision resistance;
- implicit migration compatibility or stable carrier bytes; or
- recovery from every host failure.

## 13. Bounded executable evidence

The non-authoritative research instrument under
[`evaluation/k1-executable-foundations/`](../../evaluation/k1-executable-foundations/)
produces finite fixture observations for this target. Any Evidence claim over
those observations must bind the exact revision, fixtures, supported
primitives, evaluation contracts, limits, and host implementations. Its
separate oracle covers only bootstrap and identity cases, and shared use of a
host SHA-256 library is not independent SHA-256 validation.

The selected instrument currently evaluates an in-memory algorithm object from
which its ID and direct-primitive field are derived, and it may resolve an exact
evaluation-contract ID through its local registry. It therefore does not yet
exercise raw-request mismatch of an asserted algorithm ID, omission, padding,
or reordering of the carried direct-primitive field, or absence/mismatch of an
asserted contract body. Those are target-specification obligations, not
executable observations, until a strict raw request carrier is added.
The module bundle is likewise supplied as a typed host map rather than strict
raw sorted-unique ID/body bytes, so duplicate or unsorted raw carriers and
noncanonical raw module bodies are outside present coverage even though the
instrument exercises ID recomputation, missing/extra nodes, kind and regime
checks, cycles, diamonds, and closure bounds. Its Python realization accepts
inputs only in an exact tuple and accepts module material only in an exact
built-in dictionary or the package's exact immutable fixture-mapping
singleton. It snapshots either accepted carrier into one dictionary and
rejects other sequence or mapping implementations and subclasses. Those choices are bounded
realization evidence for the portable immutable-snapshot law, not universal
host-carrier semantics. Before semantic use, that realization recursively
requires algorithm, module, evaluation-contract, charging-formula, schema,
datum, typed-ID, and term carriers to use their exact frozen base dataclass
constructors; subclass carriers are rejected as `Malformed` before virtual
overrides can participate in authentication or evaluation. This does not claim resilience to reflective
mutation or concurrent host sabotage. Catastrophic allocation remains host
noncompletion and may produce no record.

Each evaluator call that passes boundary 1 creates one fresh authentication
ledger. Its derived host cap is `3 + 1 + 1 + 2^14 + 1 + 2^12 = 20,486`:
three prior-meta bodies, one
contract ID, one algorithm ID, at most `2^14` authenticated request-module
IDs, one evaluator primitive-support module ID, and at most one distinct
primitive ID per `2^12` term nodes. The cap therefore cannot add a refusal
inside the selected semantic bounds. Before contract routing,
the evaluator co-observes the exact supported prior-meta descriptor bodies in
the same ledger, so basis support cannot degrade to an ID-only registry hit.
Contract and primitive
support registries are accepted only as exact
tuples with at most `2^14` entries before member inspection, then captured in
immutable host maps. When primitive support is consulted, the instrument also
authenticates and observes the exact fixture module body that owns its built-in
declarations, so a conflicting supplied module body cannot select hard-coded
semantics. Evaluation after boundary 10 uses that same admitted immutable
resolver snapshot; a realization with a mutable or replaceable resolver would
have to observe it again inside the same ledger before use.

The instrument cannot construct two distinct exact preimages that both
authenticate to one selected SHA-256 typed ID without finding a collision or
second preimage. It exercises exact typed-pair authentication, cross-kind
non-aliasing, and the request-local conflict-ledger branch under a synthetic
digest substitution. That substitution gives no evidence of a real collision
or unconditional global binding; the latter remains conditional on the
constructor-specific digest assumption stated above.

Evidence owns appraisal and current-support conclusions. This page claims no
formal proof, cryptographic conformance, security property, implementation
correctness, production readiness, or downstream-domain closure from an
instrument result.

## Appendix A. Exact selected-v0 bodies

This appendix closes every byte-level definition used by the selected v0
profile. It is semantic specification, not an evidence record. In the compact
notation below, `U`, `N`, `I`, `O`, `Q`, `S`, `R`, and `V` mean respectively
`MetaUnit`, `MetaNatural`, `MetaInt`, `MetaBytes`, `MetaSymbol`, `MetaSeq`,
`MetaRecord`, and `MetaVariant`. Quoted text in `Q` is printable ASCII; quoted
text in `O` is ASCII octets with `\0` denoting one zero octet.

### A.1 Selected prior-meta descriptors

The selected identity-profile and hash-suite descriptor values are exactly:

```text
IdentityProfileDescriptorV0 = R {
  0: Q("zkc.identity.framed.v0"),
  1: O("zkc/content-id/v0\0"),
  2: Q("u64-be-octet-length"),
  3: S [
       Q("foundation-profile"),
       Q("identity-profile-id"),
       Q("hash-suite-id"),
       Q("subject-kind"),
       Q("semantic-regime-id"),
       Q("canonical-body")
     ],
  4: Q("digest-excluded")
}

HashSuiteDescriptorV0 = R {
  0: Q("sha2-256"),
  1: N(1),
  2: Q("fips-180-4-octets"),
  3: N(32)
}
```

Their `M` lengths and derived prior-meta digest octets are:

| Descriptor | `length(M(d))` | SHA-256 digest |
|---|---:|---|
| identity profile | `404` | `0764186d53048eb619e79783581331dd7ef7c3939215b8000239c94768237ac1` |
| hash suite | `136` | `c24b580c31bf26bf314e746c87a93cb7ff61d3c33880fbd0ad8e31b307110805` |

Let `CoreNamesV0` be this exact symbol sequence:

```text
[
  "unit", "bool", "nat", "int", "bytes", "symbol", "seq",
  "record", "variant", "literal", "variable", "let",
  "record-construct", "project", "inject", "case",
  "sequence-construct", "sequence-length", "fail", "strict-index",
  "bounded-append", "primitive-call", "bounded-iterate", "conditional"
]
```

`SemanticCoreLawSourceV0` is the ASCII encoding of the following lines joined
by LF, including one LF after the last line and no CR octets:

```text
zkc.foundation.semantic-core-law.v0
source-encoding=ASCII-0x20..0x7e;LF-after-every-line-including-last;no-CR
notation=U:MetaUnit;MF:MetaBooleanFalse;MT:MetaBooleanTrue;N(n):MetaNatural(n);I(z):MetaInt(z);O(x):MetaBytes(x);Q(x):MetaSymbol(x);S[x...]:MetaSeq(x...);R{n:x,...}:MetaRecord((n,x)...);V(n,x):MetaVariant(n,x);M(x):FoundationMetaProfileV0-canonical-bytes
reference-notation=PR(id):PriorRefV0(id);CR(id):ContentRefV0(id);SR:SemanticRegimeId-derived-from-this-exact-descriptor
basis-notation=B:the-enclosing-authenticated-PriorMetaAuthenticationBasis-with-B.semantic-regime.id=SR
ordinary-id(K,b):=SemanticContentId<K>(B,b)
sequence-notation=S[...] preserves written order;R fields are written in increasing ordinal order;map preserves source order
selected-limits=axis-octets<=1048576;meta-bytes<=1048576;meta-nodes<=16384;meta-child-edges<=16384;meta-root-zero-depth<=384;schema-nodes<=16384;schema-root-zero-depth<=48;term-nodes<=4096;term-root-zero-depth<=48;module-bundle-entries<=16384;module-nodes<=16384;module-import-edges<=16384;sequence-capacity<=16384;all-bounds-inclusive
axis-admission=A(s)-is-nonempty-printable-ASCII-and-length-at-most-1048576-checked-before-character-conversion-or-scanning
pair-authentication=exact-typed-constructor-kind-and-axes;strict-canonical-body-decode-and-reencode;recomputed-governing-digest-equals-asserted-ID
closed-validation-scope=one-top-level-admission-check-or-evaluation-transaction-from-prior-meta-basis-authentication-through-final-decision;includes-every-request-preimage-and-every-consulted-successfully-authenticated-registry-resolver-or-cache-preimage
hash-binding-conflict=same-exact-typed-ID-and-two-pair-authenticated-distinct-canonical-descriptor-or-body-byte-strings-in-one-closed-validation-scope
hash-binding-conflict-outcome=CheckerFailure-before-owner-admission-or-capability;equal-byte-reobservation-is-idempotent;retained-cross-transaction-authentication-state-requires-equivalent-cross-scope-grouping-and-quarantine-or-per-transaction-reauthentication
aggregate-bound-owners=MetaValue-sequence-or-record:remaining-cumulative-meta-child-edges-and-nodes;FiniteSchema-record-or-variant:per-aggregate-meta-child-edge-ceiling-plus-remaining-cumulative-schema-node-minimum-reservation;SemanticFunction-inputs-or-failures,PrimitiveDeclaration-failures,PrimitiveWork-indices,EvaluationContract-cost-rules,SemanticModule-declaration-catalogs-or-bodies,PortableAlgorithm-inputs:per-aggregate-meta-child-edge-ceiling;CanonicalTerm-multi-child:remaining-term-nodes;SemanticModule-imports:per-module-import-edge-ceiling-then-authenticated-closure-remaining-edge-reservation;DirectModuleRoots:module-node-ceiling;ModulePreimageBundle:module-bundle-entries;EvaluationRequest-inputs:derived-function-input-count
aggregate-admission-preflight=every-aggregate-bearing-semantic-carrier-has-the-explicit-owner-above;check-its-declared-or-trusted-cardinality-against-that-bound-before-member-inspection-or-derived-aggregate-construction;the-serialized-carrier-separately-owns-aggregate-raw-byte-preflight
u64-range=0..18446744073709551615
core-names=unit,bool,nat,int,bytes,symbol,seq,record,variant,literal,variable,let,record-construct,project,inject,case,sequence-construct,sequence-length,fail,strict-index,bounded-append,primitive-call,bounded-iterate,conditional
root-domain-kind=foundation.root-value-domain
root-domain-bodies=0:Q(unit),1:Q(bool),2:Q(nat),3:Q(int),4:Q(bytes),5:Q(symbol),6:Q(seq),7:Q(record),8:Q(variant)
root-domain-catalog=kind:foundation.root-value-domain;ordinals:0..8-only;owner:SR
root-term-name-tags=literal:0,variable:1,let:2,record-construct:3,project:4,inject:5,case:6,sequence-construct:7,sequence-length:8,fail:9,strict-index:10,bounded-append:11,primitive-call:12,bounded-iterate:13,conditional:14
root-primitive-catalog=empty
module-kind=foundation.semantic-module
module-catalog-body=R{0:Q(kind),1:S[bodies...]}
module-body=R{0:S[O(CR(import))...],1:S[module-catalog-body...],2:domain-payload}
module-id(m)=ordinary-id(foundation.semantic-module,module-body(m))
module-self-id=absent-from-module-body
module-nonauthority=container-and-diagnostic-label-are-outside-module-body-and-cannot-change-portable-authentication-admission-declaration-resolution-evaluation-or-completion
module-import-admission=each-import-kind-foundation.semantic-module;each-import-regime-SR;ascending-full-CR-bytes;no-duplicates
module-catalog-admission=ascending-A(kind)-bytes;unique-kinds;body-position-is-zero-based-local-ordinal
module-value-domain-kind=value-domain
module-value-domain-body=ValueDomainDeclarationBody(name):=R{0:Q(name)}
module-value-domain-admission=catalog-kind-is-exactly-value-domain;body-is-exactly-one-field-0-containing-a-valid-MetaSymbol-name;declares-one-opaque-nominal-domain-only;does-not-establish-DomainSupport
local-decl-ref-body=LDRB(kind,ordinal):=R{0:Q(kind),1:N(ordinal)}
local-decl-ref-admission=ordinal-is-u64;target-is-a-declaration-in-the-same-authenticated-aggregate;cross-kind-local-refs-are-permitted;supported-kind-specific-admission-owns-finite-local-SCC-and-cycle-legality
module-closed-scc-law=mutually-recursive-declarations-are-one-finite-aggregate-module-and-use-LDRB;ordinary-module-imports-remain-acyclic
module-reference-grammar=within-supported-kind-specific-declaration-bodies,LDRB-same-aggregate,DRB-Root-SR,and-DRB-Module-authenticated-import-closure-refs-are-permitted;arbitrary-body-bytes-are-never-scanned-for-references
decl-ref-root-body=DRB(Root(r,k,n)):=V(0,R{0:O(PR(r)),1:Q(k),2:N(n)})
decl-ref-module-body=DRB(Module(m,k,n)):=V(1,R{0:O(CR(m)),1:Q(k),2:N(n)})
decl-ref-admission=Root-owner-is-exact-SR;Module-owner-kind-is-foundation.semantic-module-and-owner-regime-is-SR;ordinal-is-u64
decl-ref-resolution=Root-resolves-exact-kind-and-position-in-authenticated-SR-root;Module-resolves-exact-kind-and-position-in-authenticated-owner-module
decl-ref-no-inference=root-or-module-tag-owner-kind-and-ordinal-are-identity-bearing;names-registry-search-and-equal-digests-do-not-resolve
declaration-domain-ref-body=DDRB(Local(kind,n)):=V(0,LDRB(kind,n));DDRB(Durable(d)):=V(1,DRB(d))
declaration-value-type=DVT(domain,schema)
declaration-value-type-body=DVTB(DVT(d,s)):=R{0:DDRB(d),1:DSB(s)}
declaration-schema-body.Unit=DSB(Unit):=V(0,U)
declaration-schema-body.Bool=DSB(Bool):=V(1,U)
declaration-schema-body.Nat=DSB(Nat(max)):=V(2,N(max))
declaration-schema-body.Int=DSB(Int(min,max)):=V(3,R{0:I(min),1:I(max)})
declaration-schema-body.Bytes=DSB(Bytes(min,max)):=V(4,R{0:N(min),1:N(max)})
declaration-schema-body.Symbol=DSB(Symbol(max)):=V(5,N(max))
declaration-schema-body.Seq=DSB(Seq(element,max)):=V(6,R{0:DVTB(element),1:N(max)})
declaration-schema-body.Record=DSB(Record[(n,T)...]):=V(7,S[R{0:N(n),1:DVTB(T)}...])
declaration-schema-body.Variant=DSB(Variant[(n,T)...]):=V(8,S[R{0:N(n),1:DVTB(T)}...])
declaration-schema-admission=same-exact-scalar,ordinal,structure,worst-case,and-constitutional-body-bounds-as-FiniteSchema-with-every-recursive-child-a-DeclarationValueType
declaration-ref-lift.local=LiftRef_m(Local(kind,n)):=Module(m,kind,n)
declaration-ref-lift.root=LiftRef_m(Durable(Root(SR,kind,n))):=Root(SR,kind,n)
declaration-ref-lift.import=LiftRef_m(Durable(Module(target,kind,n))):=Module(target,kind,n)-iff-target!=m-and-target-is-in-the-authenticated-transitive-import-closure-of-m
declaration-ref-lift.self=LiftRef_m(Durable(Module(m,kind,n)))-refuses
declaration-schema-lift.scalar=LiftSchema_m(Unit):=Unit;LiftSchema_m(Bool):=Bool;LiftSchema_m(Nat(max)):=Nat(max);LiftSchema_m(Int(min,max)):=Int(min,max);LiftSchema_m(Bytes(min,max)):=Bytes(min,max);LiftSchema_m(Symbol(max)):=Symbol(max)
declaration-schema-lift.aggregate=LiftSchema_m(Seq(T,max)):=Seq(LiftType_m(T),max);LiftSchema_m(Record[(n,T)...]):=Record[(n,LiftType_m(T))...];LiftSchema_m(Variant[(n,T)...]):=Variant[(n,LiftType_m(T))...]
declaration-type-lift=LiftType_m(DVT(d,s)):=VT(LiftRef_m(d),LiftSchema_m(s))
declaration-lift-precondition=LiftRef_m,LiftSchema_m,and-LiftType_m-are-defined-only-after-m-and-its-exact-transitive-import-closure-authenticate;durable-same-module-spelling-refuses-even-when-a-caller-omits-the-declaring-module-context
declaration-lift-result-admission=for-every-D,LiftType_m(D)-and-every-recursively-lifted-nested-ValueType-must-have-an-exact-ValueDomainRef-and-VTB(LiftType_m(D))-must-satisfy-ordinary-same-regime-schema-and-type-body-admission-and-all-constitutional-bounds;DVTB-or-DSB-fit-alone-is-insufficient;failure-refuses-during-supported-kind-specific-declaration-admission
declaration-local-domain-admission=each-Local(value-domain,n)-used-as-a-domain-resolves-in-the-same-authenticated-module-aggregate-to-an-exact-admitted-ValueDomainDeclarationBody;Local(kind,n)-with-kind!=value-domain-cannot-be-a-domain
local-ref-nondurability=LDRB-has-no-owner-id,is-never-a-DRB,cannot-cross-an-import,cannot-escape-its-module,cannot-be-independently-content-addressed,and-cannot-use-a-durable-self-spelling
kind-specific-local-type-law=every-supported-kind-specific-body-that-stores-a-value-type-uses-DVTB-inside-the-module-and-compares-the-exact-LiftType_m-result-to-its-outward-ValueType-semantics;semantic-failure-payload-types-must-do-so
recognized-declaration-formation=for-every-recognized-kind-K,strict-decoding-into-K's-exact-typed-body-grammar-precedes-owner-context-interpretation;wrong-constructor,tag,record-field-set-or-order,or-field-carrier-is-Malformed;only-after-formation-can-closed-owner-admission-run
typed-coordinate-formation=before-coordinate-routing,every-PriorRefV0-and-ContentRefV0-carrier-must-have-its-exact-host-constructor,canonical-foundation-and-nested-prior-meta-axes,and-exact-32-byte-digest;failure-is-Malformed;only-a-fully-formed-carrier-can-be-compared-with-the-consuming-slot's-required-namespace,subject-kind,semantic-regime,owner-kind,or-other-semantic-axis,and-disagreement-is-KindMismatch
declaration-resolution-phases=at-each-hierarchical-recognized-body-boundary,strictly-form-the-complete-body-and-all-of-its-immediate-reference-carriers,then-classify-and-resolve-the-complete-explicit-coordinate-set-for-owner,kind,regime,scope,and-exact-local-position,before-interpreting-any-selected-target-body;repeat-the-same-sequence-for-each-selected-nested-body-before-contextual-lift-or-admission
direct-primitive-refs=all-distinct-exact-(primitive-id,declaration-ref)-pairs-structurally-present-in-PrimitiveCall-nodes;ascending-lexicographic-(CR(primitive-id),PrimitiveBody(ref))-bytes;only-exact-pair-duplicates-collapse
primitive-ref-pair-law=every-retained-pair-authenticates-before-primitive-support-lookup;failed-asserted-id-and-body-authentication-is-Malformed;same-typed-id-with-distinct-pair-authenticated-declaration-bodies-is-HashBindingConflict;equal-pair-reobservation-is-idempotent;same-declaration-body-cannot-authenticate-as-two-ids-under-one-fixed-deterministic-basis
direct-declaration-refs=all-declaration-references-in-ordered-input-types,literal-types,term-type-annotations,failure-constructors,and-declaration-halves-of-direct-primitive-refs;include-all-recursively-nested-value-types;never-scan-arbitrary-data
direct-module-roots=unique-module-owners-of-direct-declaration-refs;ascending-full-CR(module-id)-bytes
authenticated-imports-B(m,P)=imports-from-P[m]-only-after-strict-module-body-decode-and-recomputed-module-id-equals-m-under-basis-B
required-module-closure-B(alg,P)=least-X-containing-direct-module-roots-and-every-authenticated-import-of-every-m-in-X
module-preimage-bundle=finite-map-from-asserted-module-id-to-exact-module-body-bytes;entry-count<=16384-checked-before-key-iteration-or-copy;every-key-carrier-then-forms-and-routes-as-an-exact-same-regime-foundation.semantic-module-ID-before-map-copy-or-key-set-comparison;keys-ascending-full-CR-bytes;no-duplicate-key;aggregate-raw-carrier-byte-bound-is-owned-by-the-serialized-request-carrier
module-closure-order=depth-first;direct-roots-ascending;each-import-list-ascending;authenticate-reached-candidate-before-reading-its-imports-or-classifying-a-candidate-selected-cycle;reserve-the-whole-authenticated-import-list-against-the-remaining-closure-edge-budget-before-scheduling-or-inspecting-any-child-target
module-closure-admission=every-reached-key-recomputed-before-its-imports;keys(P)-equal-required-module-closure-after-traversal;unreferenced-extra-keys-refused-without-body-interpretation;no-missing-wrong-kind-cross-regime-id-mismatch-or-cycle
module-closure-measure=each-unique-module-node-once;each-authenticated-module-import-edge-once;shared-diamond-target-authenticated-and-expanded-once
module-closure-limits=unique-nodes<=16384;import-edges<=16384
module-declaration-reference-scope=after-module-authentication-each-supported-kind-interprets-only-its-exact-body-law;recognized-target-is-LDRB-in-the-same-aggregate,SR-root,or-a-module-in-the-declaring-module-import-closure;an-unrecognized-kind-in-a-generic-extension-capable-declaration-position-is-Unsupported;an-exact-typed-slot-carrying-a-kind-other-than-its-required-K-is-KindMismatch;unreferenced-unknown-catalogs-are-inert
primitive-candidates-not-module-nodes=primitive-id-is-a-direct-algorithm-dependency;primitive-declaration-resolves-through-its-owner-module;only-module-imports-form-the-transitive-preimage-DAG
value-domain-ref=Root(SR,foundation.root-value-domain,n)-with-n-in-0..8-or-Module(m,value-domain,n)-whose-resolved-body-passes-module-value-domain-admission;no-other-kind-or-body-is-a-value-domain-ref
value-domain-ref-body=VDRB(d):=DRB(d)
value-type=VT(d,s):=(domain:d,schema:s)
value-type-body=VTB(VT(d,s)):=R{0:VDRB(d),1:SB(s)}
value-type-regime=domain-and-every-recursively-nested-value-type-have-exact-regime-SR
domain-support=DomainSupport(E,d):=Supports(E,(d,Resolve(d)),PortableValueDomainAdmissionV0)
domain-support-contract=exact-total-deterministic-schema-admission+datum-membership+unique-canonical-decode-encode+mathematical-equality-for-the-exact-ref-and-body;support-does-not-transfer-between-owner-kind-ordinal-or-body
root-domain-support=intrinsic-only-for-root-domain-kind-ordinals-0..8-with-the-exact-matching-outer-schema-constructor
module-domain-support=module-owned-domain-is-opaque;FiniteSchema-is-only-a-carrier-shape-bound;resolution-or-shape-does-not-prove-membership;without-exact-DomainSupport-use-is-Unsupported-before-domain-interpretation-or-owner-admission
root-structural-boundary=generic-Boolean,record,variant,sequence,and-natural-operations-require-the-exact-corresponding-root-domain;schema-shape-equality-is-insufficient
module-value-entry=first-entry-only-as-owner-admitted-literal,owner-admitted-input,or-owner-admitted-result-of-an-exact-supported-primitive;root-aggregate-members-may-contain-already-admitted-same-regime-module-values
canonical-value=CV(T,v,d,M(d));d-is-the-unique-domain-admitted-MetaValueV0-representative-of-v;strict-decode-consumes-one-datum-reencodes-identically-and-owner-admits
canonical-and-root-value-equality=defined-only-for-values-with-the-same-exact-ValueType;then-use-the-exact-domain-owned-mathematical-equality;selected-root-domains-use-equality-of-their-unique-admitted-datums;same-domain-values-under-different-FiniteSchemas-are-not-equal-at-this-typed-value-layer
canonical-value-id-body(T,d):=R{0:VDRB(T.domain),1:SB(T.schema),2:d}
canonical-value-id(K,T,d):=ordinary-id(K,canonical-value-id-body(T,d));defined-only-after-exact-domain-admission;private-or-unaddressed-values-need-no-id
schema-body.Unit=SB(Unit):=V(0,U)
schema-body.Bool=SB(Bool):=V(1,U)
schema-body.Nat=SB(Nat(max)):=V(2,N(max))
schema-body.Int=SB(Int(min,max)):=V(3,R{0:I(min),1:I(max)})
schema-body.Bytes=SB(Bytes(min,max)):=V(4,R{0:N(min),1:N(max)})
schema-body.Symbol=SB(Symbol(max)):=V(5,N(max))
schema-body.Seq=SB(Seq(element,max)):=V(6,R{0:VTB(element),1:N(max)})
schema-body.Record=SB(Record[(n,T)...]):=V(7,S[R{0:N(n),1:VTB(T)}...])
schema-body.Variant=SB(Variant[(n,T)...]):=V(8,S[R{0:N(n),1:VTB(T)}...])
schema-ordinal-law=record-fields-and-variant-cases-use-u64-ordinals-in-strictly-increasing-order;variant-case-list-is-nonempty
schema-scalar-bounds=Nat:0<=max<2^256;Int:min<=max-and-max(abs(min),abs(max))<2^255;Bytes:0<=min<=max<=1048576;Symbol:1<=max<=4096;Seq:0<=max<=16384
schema-structure=finite-acyclic-occurrence-tree;nodes<=16384;root-zero-depth<=48
schema-type-body-bound=M(VTB(T))-fits-meta-bytes-nodes-child-edges-and-root-zero-depth-selected-limits
canonical-value-type-formation=direct-VTB-is-a-refined-carrier-and-forms-only-after-schema-ordinal,scalar,finite-tree,Worst,and-type-body-bounds-all-hold;failure-in-a-presented-algorithm-or-value-header-is-Malformed;raw-DVTB-first-forms-its-complete-grammar-and-post-formation-contextual-lift-or-closed-schema-admission-failure-is-Refused;derived-maximum-completion-schema-bound-failure-is-Refused
mag(n)=max(1,ceil(bitlength(n)/8))
worst.Unit=Worst(Unit):=(1,1,0,0)
worst.Bool=Worst(Bool):=(1,1,0,0)
worst.Nat=Worst(Nat(max)):=(9+mag(max),1,0,0)
worst.Int=Worst(Int(min,max)):=(10+mag(max(abs(min),abs(max))),1,0,0)
worst.Bytes=Worst(Bytes(min,max)):=(9+max,1,0,0)
worst.Symbol=Worst(Symbol(max)):=(9+max,1,0,0)
worst.Seq=Worst(Seq(T,c)):=(9+c*(8+w.bytes),1+c*w.nodes,c*(1+w.edges),if-c=0-then-0-else-1+w.depth);w:=Worst(T.schema)
worst.Record=Worst(Record[(n,T_i)...]):=(9+sum_i(16+w_i.bytes),1+sum_i(w_i.nodes),count+sum_i(w_i.edges),if-count=0-then-0-else-1+max_i(w_i.depth));w_i:=Worst(T_i.schema)
worst.Variant=Worst(Variant[(n,T_i)...]):=(17+max_i(w_i.bytes),1+max_i(w_i.nodes),1+max_i(w_i.edges),1+max_i(w_i.depth));w_i:=Worst(T_i.schema)
schema-worst-admission=for-Worst(s)=(bytes,nodes,edges,depth):bytes<=1048576;nodes<=16384;edges<=16384;depth<=384
max-datum-bytes=MaxDatumBytes(T):=Worst(T.schema).bytes
actual-datum-admission=exactly-one-strict-MetaValueV0-datum;recursive-carrier-shape-match;actual-meta-bytes-nodes-child-edges-and-depth-within-selected-limits;then-exact-domain-owner-membership
root-membership.Unit=Unit-admits-only-U
root-membership.Bool=Bool-admits-only-MF-or-MT
root-membership.Nat=Nat(max)-admits-N(n)-iff-0<=n<=max
root-membership.Int=Int(min,max)-admits-I(z)-iff-min<=z<=max
root-membership.Bytes=Bytes(min,max)-admits-O(x)-iff-min<=length(x)<=max
root-membership.Symbol=Symbol(max)-admits-Q(x)-iff-1<=ASCII-length(x)<=max-and-each-octet-is-0x21..0x7e
root-membership.Seq=Seq(T,max)-admits-S[x_0...x_(k-1)]-iff-k<=max-and-each-x_i-is-owner-admitted-at-T
root-membership.Record=Record[(n_i,T_i)...]-admits-R{n_i:x_i,...}-iff-the-ordinal-sequence-is-exact-and-each-x_i-is-owner-admitted-at-T_i
root-membership.Variant=Variant[(n_i,T_i)...]-admits-V(n_j,x)-iff-n_j-is-a-declared-case-and-x-is-owner-admitted-at-T_j
root-type-aliases=RootUnit:=VT(Root(SR,foundation.root-value-domain,0),Unit);RootBool:=VT(Root(SR,foundation.root-value-domain,1),Bool);RootNat[m]:=VT(Root(SR,foundation.root-value-domain,2),Nat(m));RootInt[a,b]:=VT(Root(SR,foundation.root-value-domain,3),Int(a,b));RootBytes[a,b]:=VT(Root(SR,foundation.root-value-domain,4),Bytes(a,b));RootSymbol[m]:=VT(Root(SR,foundation.root-value-domain,5),Symbol(m));RootSeq[T,c]:=VT(Root(SR,foundation.root-value-domain,6),Seq(T,c));RootRecord[F]:=VT(Root(SR,foundation.root-value-domain,7),Record(F));RootVariant[C]:=VT(Root(SR,foundation.root-value-domain,8),Variant(C))
failure-type=Failure(module,ordinal,payload-type);module-kind-foundation.semantic-module;module-regime-SR;declaration-kind-semantic-failure
failure-type-body=FT(Failure(m,n,T)):=R{0:DRB(Module(m,semantic-failure,n)),1:VTB(T)}
failure-declaration-body=FailureDeclarationBody(name,D):=R{0:Q(name),1:DVTB(D)}
failure-declaration-admission=exact-owner-module-m-and-ordinal-resolve-to-one-strict-FailureDeclarationBody(name,D);name-is-a-valid-Symbol;D-is-an-admitted-localizable-declaration-value-type;LiftType_m(D)-equals-the-outward-payload-type-exactly;payload-regime-SR
primitive-ref=PrimitiveRef(id,module,ordinal);id-kind-foundation.semantic-primitive;module-kind-foundation.semantic-module;both-regime-SR;declaration-kind-semantic-primitive
primitive-semantic-body=PrimitiveBody(p):=DRB(Module(p.module,semantic-primitive,p.ordinal))
primitive-id-law=p.id=ordinary-id(foundation.semantic-primitive,PrimitiveBody(p))
primitive-ref-body=PRB(p):=R{0:O(CR(p.id)),1:DRB(Module(p.module,semantic-primitive,p.ordinal))}
primitive-declaration-body=PrimitiveDeclarationBody(name,version,type-source,operation-source,failures,discipline):=R{0:Q(name),1:N(version),2:O(type-source),3:O(operation-source),4:S[LDRB(semantic-failure,n_i)...],5:Q(discipline)}
primitive-declaration-formation=name-and-discipline-are-Symbols;version-and-each-failure-ordinal-are-u64;n_i-resolves-in-the-same-authenticated-module-to-one-strict-FailureDeclarationBody-whose-localizable-payload-type-forms-and-lifts;malformed-primitive,local-failure,or-DVT-or-DSB-structure-is-Malformed;formed-wrong-kind-or-regime-coordinate-is-KindMismatch;absent-local-failure-coordinate-or-post-formation-closed-lift-admission-failure-is-Refused
primitive-declaration-admission=exact-owner-module-and-ordinal-resolve-to-one-strict-PrimitiveDeclarationBody;the-supported-kind-law-interprets-the-immutable-type-and-operation-sources-and-fixes-exact-input-and-derived-output-rule,exact-failure-row,semantic-dependencies,state-and-effect-discipline,bounds,distribution,canonicality,and-side-conditions
primitive-denotation=total-deterministic-function-of-exact-owner-admitted-arguments;returns-exact-owner-admitted-derived-success-or-one-declared-typed-failure;semantic-state-is-explicit-input-and-output;ambient-state,freshness,I/O,and-supplier-behavior-are-forbidden
primitive-provider-law=provider-and-build-identity-are-nonsemantic-unless-explicitly-identified;lack-of-provider-is-operational-noncompletion;provider-disagreement-is-checker-or-conformance-failure
function-type=Fn(inputs,success,failures)
function-type-body=FnB(Fn(inputs,success,failures)):=R{0:S[VTB(input_i)...],1:VTB(success),2:S[FT(failure_i)...]}
failure-row-order=ascending-M(FT(f))-bytes;exact-duplicates-collapse;same-declaration-with-different-payload-type-refuses
failure-row-derivation=canonical-union-of-every-failure-in-every-structurally-present-subterm-including-unselected-case-and-conditional-branches,each-explicit-Fail,StrictIndex,and-BoundedAppend-failure,and-each-resolved-primitive-declaration-row
semantic-completion=Success(CV(success,...))|DomainFailure(failure_i,CV(failure_i.payload-type,...));only-these-are-semantic-completions
term-body.Literal=TB(Literal(v)):=V(0,R{0:VTB(v.type),1:v.datum})
term-body.Variable=TB(Variable(n,T)):=V(1,R{0:N(n),1:VTB(T)})
term-body.Let=TB(Let(bound,body)):=V(2,R{0:TB(bound),1:TB(body)})
term-body.RecordConstruct=TB(RecordConstruct[(n,e)...]):=V(3,S[R{0:N(n),1:TB(e)}...])
term-body.Project=TB(Project(record,n)):=V(4,R{0:TB(record),1:N(n)})
term-body.Inject=TB(Inject(n,payload,sum-type)):=V(5,R{0:N(n),1:TB(payload),2:VTB(sum-type)})
term-body.Case=TB(Case(scrutinee,[(n,branch)...])):=V(6,R{0:TB(scrutinee),1:S[R{0:N(n),1:TB(branch)}...]})
term-body.SequenceConstruct=TB(SequenceConstruct(T,[e...],capacity)):=V(7,R{0:VTB(T),1:S[TB(e)...],2:N(capacity)})
term-body.SequenceLength=TB(SequenceLength(source)):=V(8,TB(source))
term-body.Fail=TB(Fail(f,payload,success-type)):=V(9,R{0:FT(f),1:TB(payload),2:VTB(success-type)})
term-body.StrictIndex=TB(StrictIndex(source,index,f)):=V(10,R{0:TB(source),1:TB(index),2:FT(f)})
term-body.BoundedAppend=TB(BoundedAppend(source,element,f)):=V(11,R{0:TB(source),1:TB(element),2:FT(f)})
term-body.PrimitiveCall=TB(PrimitiveCall(p,[argument...])):=V(12,R{0:PRB(p),1:S[TB(argument)...]})
iteration-source-body=IS(SequenceSource(e)):=V(0,TB(e));IS(RangeSource(e)):=V(1,TB(e))
term-body.BoundedIterate=TB(BoundedIterate(source,initial,body)):=V(13,R{0:IS(source),1:TB(initial),2:TB(body)})
term-body.Conditional=TB(Conditional(condition,when-true,when-false)):=V(14,R{0:TB(condition),1:TB(when-true),2:TB(when-false)})
term-ordinal-law=Variable-de-Bruijn-indices-and-record-field,case-branch,projection,and-injection-ordinals-are-u64;record-fields-and-case-branches-are-strictly-increasing
term-structure=finite-acyclic-occurrence-tree;nodes<=4096;root-zero-depth<=48;M(TB(term))-and-M(AlgorithmBody)-also-fit-all-selected-meta-limits
typing-context=Gamma-is-ordered-nearest-binder-first;de-Bruijn-index-zero-is-nearest;Variable(n,T)-requires-n<length(Gamma)-and-T=Gamma[n]
typing-literal=output-is-the-explicit-exact-type-without-schema-shape-or-owner-membership-inspection-of-the-datum;canonical-algorithm-structure-authentication-independently-requires-the-literal-datum-to-be-one-exact-canonical-MetaValueV0-within-constitutional-limits;after-DomainSupport-owner-admission-rechecks-constitutional-limits-and-checks-the-finite-carrier-shape-and-exact-domain-law
typing-let=type(bound,Gamma)=B;type(body,[B]+Gamma)=R;output=R
typing-record=field-ordinals-strictly-increasing;type(e_i,Gamma)=T_i;output=RootRecord[(n_i,T_i)...]
typing-project=type(record,Gamma)=RootRecord[(n_i,T_i)...];n=n_j-for-one-field;output=T_j
typing-inject=sum-type=RootVariant[(n_i,T_i)...];n=n_j;type(payload,Gamma)=T_j;output=sum-type
typing-case=type(scrutinee,Gamma)=RootVariant[(n_i,T_i)...];branch-ordinals-exactly-(n_i);type(branch_i,[T_i]+Gamma)=R-for-one-exact-R;output=R
typing-conditional=type(condition,Gamma)=RootBool;type(when-true,Gamma)=type(when-false,Gamma)=R;output=R
typing-sequence=type(e_i,Gamma)=T;count(e)<=capacity<=16384;admit-schema-RootSeq[T,capacity];output=RootSeq[T,capacity]
typing-sequence-length=type(source,Gamma)=RootSeq[T,capacity];output=RootNat[capacity]
typing-fail=f-resolved-and-admitted;type(payload,Gamma)=f.payload-type;success-type-S-is-explicit;output=S
typing-strict-index=type(source,Gamma)=RootSeq[T,capacity];type(index,Gamma)=RootNat[m]=f.payload-type;f-resolved-and-admitted;output=T
typing-bounded-append=type(source,Gamma)=RootSeq[T,capacity];type(element,Gamma)=T;f.payload-type=RootUnit;f-resolved-and-admitted;output-is-the-exact-source-type
typing-primitive-call=p-resolved-and-owner-typed;argument-types-ordered;resolved-exact-type-rule-derives-output-R;output=R
index-type=IndexType(N):=RootNat[max(0,N-1)];if-N=0-no-index-value-is-produced
continue-break-type=ContinueBreak(S,R):=RootVariant[(0,S),(1,R)]
typing-iterate-sequence=type(source.sequence,Gamma)=RootSeq[T,N];0<=N<=16384;type(initial,Gamma)=S;type(body,[IndexType(N),T,S]+Gamma)=ContinueBreak(S,R);output=ContinueBreak(S,R)
typing-iterate-range=type(source.exclusive-bound,Gamma)=RootNat[N];0<=N<=16384;type(initial,Gamma)=S;type(body,[IndexType(N),IndexType(N),S]+Gamma)=ContinueBreak(S,R);output=ContinueBreak(S,R)
reachable-value-types=every-input,explicit-annotation,literal,failure-payload,primitive-derived-output,subterm-derived-output,and-every-recursively-nested-member-type-in-the-complete-typed-term
typing-and-owner-admission-order=resolve-and-kind-support-all-declarations;derive-all-carrier-types-and-complete-ABI-without-owner-admitting-literals;require-DomainSupport-for-every-reachable-value-type;then-owner-admit-literals-in-canonical-syntax-order
evaluation=strict-deterministic-call-by-value;each-term-entry-is-charged-before-that-node;semantic-failure-immediately-propagates
evaluation-order=every-executed-strict-term-constructor-and-operand-list-is-evaluated-in-canonical-TB-field-order-and-each-S-field-in-source-order;Let-bound-before-body;record-fields-by-ordinal;sequence-elements-left-to-right;primitive-arguments-left-to-right;Project-source-first;Inject-payload-first;SequenceLength-source-first;Fail-payload-first;case-scrutinee-before-only-selected-branch;conditional-condition-before-only-selected-branch;StrictIndex-source-before-index;BoundedAppend-source-before-element;iterator-source-before-initial-before-items-in-source-order
eval.Literal=return-owner-admitted-literal
eval.Variable=return-Gamma[index]
eval.Let=evaluate-bound;prepend-result;evaluate-body
eval.RecordConstruct=evaluate-fields-by-ordinal;construct-R{n:datum...};owner-admit-at-inferred-RootRecord-type
eval.Project=evaluate-record;select-exact-field-datum;owner-admit-at-inferred-field-type
eval.Inject=evaluate-payload;construct-V(case,payload-datum);owner-admit-at-explicit-RootVariant-type
eval.Case=evaluate-scrutinee;owner-admit-selected-payload-at-its-case-type;prepend-payload;evaluate-only-corresponding-branch
eval.Conditional=evaluate-RootBool-condition;evaluate-only-true-branch-for-MT-or-false-branch-for-MF
eval.SequenceConstruct=evaluate-elements-left-to-right;construct-S[datum...];owner-admit-at-RootSeq[T,capacity]
eval.SequenceLength=evaluate-source;return-owner-admitted-N(actual-count)-at-RootNat[capacity]
eval.Fail=evaluate-payload;complete-DomainFailure(f,payload)
eval.StrictIndex=evaluate-source-then-index;if-index>=actual-count-complete-DomainFailure(f,index);otherwise-owner-admit-selected-element-at-T
eval.BoundedAppend=evaluate-source-then-element;if-actual-count>=capacity-complete-DomainFailure(f,RootUnit-value);otherwise-append-and-owner-admit-at-exact-source-type
eval.PrimitiveCall=evaluate-arguments-left-to-right;charge-exact-work-formula-before-denotation;enter-exact-total-denotation;owner-admit-returned-success-or-declared-failure-payload
eval.IterateSequence=evaluate-sequence-then-initial;items-are-(RootNat-index,owner-admitted-element)-in-sequence-order
eval.IterateRange=evaluate-exclusive-bound-n-then-initial;items-are-(RootNat(i),RootNat(i))-for-i=0..n-1
eval.IterateLoop=before-each-item-charge-iteration-item-units;evaluate-body-with-[index,item,state]+Gamma;case-0-owner-admits-next-state-and-continues;case-1-returns-the-exact-Break-value-immediately;exhaustion-returns-owner-admitted-V(0,final-state-datum)
totality=finite-acyclic-typed-syntax+finite-schemas+bounded-sequences+single-bounded-iterator+acyclic-module-closure+supported-total-domain-laws+supported-total-primitives
portable-language-exclusions=no-general-recursion;no-cyclic-calls;no-callbacks;no-dynamic-code;no-ambient-registry;no-I/O;no-clock;no-implicit-randomness;no-reflection;no-unordered-iteration;no-implementation-defined-arithmetic
algorithm-candidate=algorithm-kind:Symbol;ordered-inputs:S[ValueType...];term:CanonicalTerm
algorithm-body=AlgorithmBody(alg):=R{0:Q(alg.algorithm-kind),1:S[VTB(input_i)...],2:TB(alg.term),3:S[PRB(p_i)...]}
algorithm-direct-primitive-field=p_i-is-exactly-direct-primitive-refs-derived-from-term-in-canonical-order;omission,padding,or-reordering-refuses
algorithm-id=ordinary-id(foundation.portable-algorithm,AlgorithmBody(alg));regime-axis-SR
algorithm-derived-ABI=Fn(ordered-inputs,type(term,ordered-inputs),derived-canonical-failure-row)
algorithm-derived-module-roots=direct-module-roots-are-derived-only-and-not-an-authored-or-hashed-summary
algorithm-nonauthority=diagnostic-label,authored-output-manifest,authored-failure-manifest,trace,printer,normalization,and-extensional-equivalence-are-excluded-from-identity-and-cannot-change-portable-authentication-admission-evaluation-or-completion
work-formula-body.Fixed=WB(Fixed(c)):=V(0,N(c))
work-formula-body.SumByteLengths=WB(SumByteLengths(indices,c)):=V(1,R{0:S[N(index)...],1:N(c)})
work-formula.body.MinByteLengthNatural=WB(MinByteLengthNatural(byte-index,natural-index,c)):=V(2,R{0:N(byte-index),1:N(natural-index),2:N(c)})
work-formula-syntax-admission=all-constants-are-naturals;all-positional-indices-are-u64-naturals;SumByteLengths-indices-ascending-numeric-and-unique;fixed-has-no-indices;MinByteLengthNatural-has-exactly-two-indices;unknown-tag-fails-closed-variant-formation-and-is-Malformed;constitutional-body-bounds-apply
work-formula-admitted-for-ABI=FormulaSyntaxAdmissible-and-all-indices-in-the-exact-primitive-ABI-and-SumByteLengths-selected-argument-datums-are-O(x)-or-MinByteLengthNatural-selected-datums-are-O(x)-then-N(n);checked-only-for-rules-keyed-by-exact-direct-primitives;unused-syntax-admissible-rules-grant-no-ABI-applicability
work-formula-semantics=Fixed(c):c;SumByteLengths(indices,c):c+sum_index-in-indices(length(argument[index].datum.octets));MinByteLengthNatural(byte-index,natural-index,c):c+min(length(argument[byte-index].datum.octets),argument[natural-index].datum.natural)
evaluation-contract-version=0
evaluation-contract-body=ContractBody(C):=R{0:N(0),1:N(C.term-entry-units),2:N(C.iteration-item-units),3:Q(portable-evaluation-precedence-v0),4:Q(tagged-canonical-completion-v0),5:Q(maximum-completion-schema-v0),6:S[R{0:O(CR(primitive-id)),1:WB(formula)}...]}
evaluation-contract-rule-order=primitive-ids-have-kind-foundation.semantic-primitive-and-regime-SR;rules-ascending-full-CR-bytes;no-duplicate-key
evaluation-contract-id=ordinary-id(foundation.evaluation-contract,ContractBody(C));regime-axis-SR
evaluation-contract-closure=every-direct-primitive-has-exactly-one-ABI-compatible-rule-and-evaluator-support;unused-rules-are-allowed-and-do-not-enlarge-module-closure
evaluation-contract-boundary=contract-controls-only-charges,validation-precedence,completion-encoding,and-static-completion-preflight;it-does-not-change-term-typing,evaluation-order,primitive-denotation,semantic-failure,or-algorithm-identity
evaluation-request=finite-limits+complete-prior-meta-basis+asserted-contract-id-and-exact-contract-body+asserted-portable-algorithm-id-and-exact-algorithm-body+exact-module-preimage-bundle+ordered-input-headers-and-canonical-payload-bytes
evaluation-request-snapshot=evaluation-consumes-one-immutable-admitted-request-snapshot;module-and-input-material-is-captured-exactly-once-at-its-respective-validation-boundary;all-later-semantic-steps-use-only-the-captured-material-and-never-reread-a-mutable-producer-or-source;capture-preserves-validation-precedence-and-cannot-observe-a-later-boundary-early;concrete-host-carriers-are-not-portable-semantic-root-law
evaluation-limits=maximum-term-units,maximum-iteration-units,maximum-primitive-work,maximum-completion-bytes;each-is-a-finite-mathematical-natural;request-local-and-not-content-addressed
evaluation-charge=term-units,iteration-units,primitive-work,completion-bytes;each-is-a-mathematical-natural;completion-bytes-is-zero-until-one-complete-envelope-exists
charge-term=on-entry-to-each-term-node-add-C.term-entry-units-before-node-work
charge-iteration=before-each-executed-iterator-item-add-C.iteration-item-units-before-body-work
charge-primitive=after-arguments-and-before-denotation-add-the-exact-formula-result
charge-atomicity=precheck-combined-next-counter-values-against-request-limits;commit-all-or-none-before-associated-work;equal-to-limit-is-allowed
precedence.01=validate-all-request-limit-fields-as-finite-mathematical-naturals
precedence.02=authenticate-and-establish-support-for-the-complete-exact-prior-meta-basis
precedence.03=validate-contract-typed-header;strictly-decode-exact-body;authenticate-asserted-id;validate-version,closed-formula-syntax,canonical-rule-order,and-same-regime-refs;establish-support-for-that-exact-contract
precedence.04=validate-subject-outer-typed-header-and-require-foundation.portable-algorithm
precedence.05=strictly-decode-canonical-algorithm-structure,reject-every-over-u64-Variable-index-or-other-structural-ordinal,and-authenticate-asserted-id-without-declaration-resolution-or-owner-typing
precedence.06=derive-direct-references;authenticate-the-exact-required-module-closure;resolve-the-complete-explicit-declaration-coordinate-set-for-owner,kind,regime,and-exact-local-position;begin-no-kind-specific-body-interpretation-until-all-coordinates-resolve
precedence.07=establish-supported-kind-specific-interpretation-for-every-resolved-body;derive-carrier-types-and-complete-ABI-without-owner-admitting-literals;check-exact-direct-primitive-field;compute-all-reachable-value-types;require-DomainSupport-for-all;owner-admit-all-literals-in-canonical-syntax-order
precedence.08=validate-input-arity,carrier-shape,and-exact-ValueType-for-all-headers-in-argument-order-without-decoding-any-input-payload
precedence.09=strictly-decode-and-owner-admit-input-payloads-in-argument-order
precedence.10=establish-evaluator-support-for-every-exact-direct-primitive-and-require-one-exact-ABI-compatible-work-formula-per-direct-primitive
precedence.11=derive-and-preflight-the-full-maximum-tagged-completion-schema-and-byte-size-before-first-term-entry
precedence.12=enter-semantic-evaluation
precedence-barrier=failure-at-an-earlier-boundary-forbids-later-semantic-inspection;missing-or-invalid-owner-declaration-precedes-unsupported-domain;unsupported-reachable-domain-precedes-input-arity,header,and-payload-defects;all-input-headers-precede-any-input-payload-decode
completion-bytes.Success=CompletionBytes(Success(v)):=M(V(0,v.datum))
completion-bytes.Failure=CompletionBytes(DomainFailure(failures[i],p)):=M(V(i+1,p.datum))
completion-maximum=MaximumCompletionSize:=17+max({MaxDatumBytes(success)}-union-{MaxDatumBytes(f.payload-type)-for-f-in-failures})
completion-schema=RootVariant([(0,success)]-concatenated-with-[(i+1,failures[i].payload-type)-for-0<=i<length(failures)])-shape;its-schema-structure-and-Worst-measure-must-be-admitted-and-MaximumCompletionSize<=1048576
completion-envelope-nonauthority=the-derived-tagged-variant-is-only-the-exact-ABI-envelope-for-one-derived-function-type;it-is-not-a-universal-Foundation-result-type
completion-preflight=MaximumCompletionSize-is-checked-against-maximum-completion-bytes-before-first-term-entry;actual-complete-envelope-size-is-charged-on-completion;equal-to-limit-is-allowed
operational-noncompletion=unsupported,missing-dependency,kind-mismatch,malformed,refused,deterministic-limit-exhaustion,and-checker-or-conformance-failure-are-distinct-from-Success-and-DomainFailure
operational-outcome-partition=Unsupported,MissingDependency,KindMismatch,Malformed,Refused,DeterministicLimitExceeded,and-CheckerFailure-are-pairwise-distinct;MissingDependency-means-a-required-exact-named-preimage-is-absent-after-typed-coordinate-formation;KindMismatch-means-an-exact-formed-typed-subject,reference,or-header-names-the-wrong-namespace,kind,regime,arity,or-exact-ABI-coordinate-under-the-authenticated-basis;Unsupported-means-an-exact-same-kind-and-same-regime-authenticated-basis,subject,or-request-pair-lacks-evaluator-selected-interpretation-or-coverage,including-an-absent-primitive-provider-or-cost-rule;Malformed-means-an-invalid-carrier,forbidden-subclass,noncanonical-bytes,failed-asserted-ID-and-body-authentication,or-failed-structural-formation-before-a-closed-semantic-predicate-is-defined;Refused-means-an-authenticated-structurally-formed-candidate-reached-and-failed-a-supported-closed-resolution,typing,owner-admission,or-compatibility-predicate,including-a-present-work-rule-incompatible-with-the-exact-call-ABI;DeterministicLimitExceeded-means-a-declared-finite-request,closure,or-evaluation-bound-is-exhausted-before-the-associated-work-and-produces-no-semantic-completion;CheckerFailure-means-an-evaluator-advertised-or-selected-support-entry,derived-ABI,provider-postcondition,or-request-local-typed-ID-binding-is-internally-inconsistent;strict-input-decode-failure-is-Malformed-and-post-decode-owner-admission-failure-is-Refused
host-failure=process-death,unrecordable-allocation-failure,or-unavailable-device-may-produce-no-record-and-is-never-a-semantic-completion
nonclaims=no-universal-result-type-or-resource-or-judgment;no-security-property;no-distribution-property;no-constant-time-property;no-provider-conformance;no-unconditional-hash-binding-or-collision-resistance;no-protocol-relation-analysis-compiler-or-endpoint-admission
```

The byte string has length `39,468` and SHA-256 digest
`4c0115cb4301240c555e1484ce98863bd2f3400a1ac0cf456ff89248229452d3`.
The digest here is only an exact transcription check; descriptor field `1`
contains the bytes themselves.

The selected regime descriptor is exactly:

```text
SemanticRegimeDescriptorV0 = R {
  0: Q("zkc.foundation.portable-semantics.v0"),
  1: N(0),
  2: R {
       0: S(map(CoreNamesV0, Q)),
       1: O(SemanticCoreLawSourceV0)
     },
  3: S [],
  4: Q("local-ordinals-and-closed-scc-v0"),
  5: Q("extension-modules-same-root-dag-v0")
}
```

It has `length(M(SemanticRegimeDescriptorV0)) = 40,383`; those encoded
descriptor bytes have SHA-256 digest
`e7fa336ad42e028d272f7eb870cc5a9213068253a74f07c710ae111da3205eb0`,
and its prior-meta `SemanticRegimeId` digest is
`bfe22f86f4afc4ffaa79d7ec02db42f0c3fad30f6e6e81163cf21a52e05cce77`.
The embedded law source, not an external appendix fiat, authenticates the
selected semantic law. This appendix reproduces that law and expands its
notation for readers; it cannot assign extra meaning to the same descriptor
bytes. Changing any semantic law requires a changed descriptor and
`SemanticRegimeId`.

### A.2 Value domains, schemas, and payloads

For this regime, root declaration kind
`"foundation.root-value-domain"` resolves ordinals `0..8` to the first nine
symbols in `CoreNamesV0` and to these exact structural schema constructors:

| Ordinal | Root body | Required outer schema |
|---:|---|---|
| `0` | `Q("unit")` | Unit |
| `1` | `Q("bool")` | Boolean |
| `2` | `Q("nat")` | bounded natural |
| `3` | `Q("int")` | bounded signed integer |
| `4` | `Q("bytes")` | bounded bytes |
| `5` | `Q("symbol")` | bounded symbol |
| `6` | `Q("seq")` | bounded sequence |
| `7` | `Q("record")` | record |
| `8` | `Q("variant")` | nonempty tagged sum |

No other ordinal resolves for that root kind. Positions `9..23` of
`CoreNamesV0` name the term constructors in tag order `0..14`; they are not
additional value-domain declarations. Descriptor field `3` is empty, so this
root declares no semantic primitive.

Every module-owned value domain instead uses catalog kind exactly
`Q("value-domain")` and body exactly:

```text
ValueDomainDeclarationBody(name) = R {0:Q(name)}
```

The record has exactly field `0`, and `name` must be a valid `MetaSymbol`.
Admission declares one opaque nominal domain and nothing more; in particular,
it does not establish `DomainSupport`, membership, equality, or a canonical
value map. No other module catalog kind or body resolves as a value domain.

Canonical value-domain and type bodies reuse the declaration encoding:

```text
ValueDomainRefBody(d) = DeclarationRefBody(d)

CanonicalValueTypeBody(T) = R {
  0: ValueDomainRefBody(T.domain),
  1: SchemaBody(T.schema)
}

CanonicalValueIdBody(T, datum) = R {
  0: ValueDomainRefBody(T.domain),
  1: SchemaBody(T.schema),
  2: datum
}
```

`CanonicalValueIdBody` is admissible for ordinary identity only after `datum`
passes exact domain admission at `T`.

Inside one module declaration, the localizable counterparts are exactly:

```text
DeclarationDomainRefBody(Local(K,n)) =
  V(0, LocalDeclarationRefBody(K,n))

DeclarationDomainRefBody(Durable(d)) =
  V(1, DeclarationRefBody(d))

DeclarationValueTypeBody(DT) = R {
  0: DeclarationDomainRefBody(DT.domain),
  1: DeclarationSchemaBody(DT.schema)
}
```

`DeclarationSchemaBody` uses the same tags and atomic payloads as the table
below. Its aggregate payloads are the following exact substitutions:

| Tag | Declaration schema | Payload |
|---:|---|---|
| `6` | `Seq(element,max)` | `R {0:DeclarationValueTypeBody(element), 1:N(max)}` |
| `7` | `Record(fields)` | `S(map(fields, (n,t) -> R {0:N(n), 1:DeclarationValueTypeBody(t)}))` |
| `8` | `Variant(cases)` | `S(map(cases, (n,t) -> R {0:N(n), 1:DeclarationValueTypeBody(t)}))` |

The localizable tree obeys the same scalar, ordinal, structure, `Worst`, and
constitutional canonical-body bounds. Its lifted outward
`CanonicalValueTypeBody` independently obeys those bounds as specified in
Section 3.2; compact local references do not weaken outward admission.

`SchemaBody` has exactly these cases and payloads:

| Tag | Schema | Payload |
|---:|---|---|
| `0` | Unit | `U` |
| `1` | Boolean | `U` |
| `2` | `Nat(max)` | `N(max)` |
| `3` | `Int(min,max)` | `R {0:I(min), 1:I(max)}` |
| `4` | `Bytes(min,max)` | `R {0:N(min), 1:N(max)}` |
| `5` | `Symbol(max)` | `N(max)` |
| `6` | `Seq(element,max)` | `R {0:CanonicalValueTypeBody(element), 1:N(max)}` |
| `7` | `Record(fields)` | `S(map(fields, (n,t) -> R {0:N(n), 1:CanonicalValueTypeBody(t)}))` |
| `8` | `Variant(cases)` | `S(map(cases, (n,t) -> R {0:N(n), 1:CanonicalValueTypeBody(t)}))` |

Each table payload is wrapped as `V(tag,payload)`. Record-field and variant-case
ordinals satisfy `0 <= ordinal < 2^64` and are strictly increasing; variants
are nonempty. Nested types have the same exact regime. Schema trees have at
most `2^14` nodes and depth `48`; recursive host structures refuse. In
addition,
`M(CanonicalValueTypeBody(T))` must itself fit all constitutional bytes, nodes,
edges, and depth bounds. Bounds are:

```text
Nat:     0 <= max < 2^256
Int:     min <= max and max(abs(min),abs(max)) < 2^255
Bytes:   0 <= min <= max <= 2^20
Symbol:  1 <= max <= 4096
Seq:     0 <= max <= 2^14
```

Let `mag(n) = max(1, ceil(bitlength(n)/8))`. For a value type `T`, write
`MaxDatumBytes(T) = MaxDatumBytes(T.schema)`. The exact maximum payload byte
size induced by a schema is:

| Schema | `MaxDatumBytes` |
|---|---:|
| Unit or Boolean | `1` |
| `Nat(max)` | `9 + mag(max)` |
| `Int(min,max)` | `10 + mag(max(abs(min),abs(max)))` |
| `Bytes(_,max)` or `Symbol(max)` | `9 + max` |
| `Seq(element,max)` | `9 + max * (8 + MaxDatumBytes(element))` |
| `Record(fields)` | `9 + sum(16 + MaxDatumBytes(field.type))` |
| `Variant(cases)` | `17 + max(MaxDatumBytes(case.type))` |

A derived maximum above `2^20` refuses the schema. Actual payload admission
also checks the constitutional budgets. More exactly, schema admission derives
`Worst(s) = (bytes,nodes,edges,depth)` coordinatewise. Atomic schemas have
`(MaxDatumBytes(s),1,0,0)`. For child measures `w_i`:

```text
Worst(Seq(t,c)) = (
  9 + c*(8+w.bytes),
  1 + c*w.nodes,
  c*(1+w.edges),
  if c=0 then 0 else 1+w.depth)

Worst(Record(fields)) = (
  9 + sum(16+w_i.bytes),
  1 + sum(w_i.nodes),
  count(fields) + sum(w_i.edges),
  if fields=[] then 0 else 1+max(w_i.depth))

Worst(Variant(cases)) = (
  17 + max(w_i.bytes),
  1 + max(w_i.nodes),
  1 + max(w_i.edges),
  1 + max(w_i.depth))
```

Every coordinate must fit its constitutional bound, so every structurally
shaped value fits before domain narrowing is considered. Actual payload
admission rechecks the same bounds. A canonical payload is exactly one
`MetaValueV0` datum matching the recursive schema, admitted by the exact domain
declaration, and encoded as `M(datum)`.

### A.3 Canonical term bodies

Write `T(e) = CanonicalTermBody(e)`, `VT(t) = CanonicalValueTypeBody(t)`,
`FT(f) = CanonicalSemanticFailureTypeBody(f)`, and
`PR(p) = CanonicalSemanticPrimitiveRefBody(p)`. The term body is exactly one
of these variants:

| Tag | Constructor | Payload |
|---:|---|---|
| `0` | Literal | `R {0:VT(value.type), 1:value.datum}` |
| `1` | Variable | `R {0:N(de-Bruijn index), 1:VT(annotation)}` |
| `2` | Let | `R {0:T(bound), 1:T(body)}` |
| `3` | RecordConstruct | `S(map(fields, (n,e) -> R {0:N(n), 1:T(e)}))` |
| `4` | Project | `R {0:T(record), 1:N(ordinal)}` |
| `5` | Inject | `R {0:N(case), 1:T(payload), 2:VT(sum type)}` |
| `6` | Case | `R {0:T(scrutinee), 1:S(map(branches, (n,e) -> R {0:N(n), 1:T(e)}))}` |
| `7` | SequenceConstruct | `R {0:VT(element type), 1:S(map(elements,T)), 2:N(capacity)}` |
| `8` | SequenceLength | `T(source)` |
| `9` | Fail | `R {0:FT(failure), 1:T(payload), 2:VT(success type)}` |
| `10` | StrictIndex | `R {0:T(source), 1:T(index), 2:FT(failure)}` |
| `11` | BoundedAppend | `R {0:T(source), 1:T(element), 2:FT(failure)}` |
| `12` | PrimitiveCall | `R {0:PR(primitive), 1:S(map(arguments,T))}` |
| `13` | BoundedIterate | `R {0:iteration source, 1:T(initial), 2:T(body)}` |
| `14` | Conditional | `R {0:T(condition), 1:T(true branch), 2:T(false branch)}` |

Each row is wrapped as `V(tag,payload)`. An iteration source is
`V(0,T(sequence))` or `V(1,T(exclusive bound))`. Field and branch sequences
use ordinals in `[0,2^64)` and are strictly increasing. Projection and
injection ordinals and variable de Bruijn indices are in the same range.
Variable index zero names the nearest binder, and every variable must repeat
the exact type at its environment position. These structural `u64` checks are
part of canonical algorithm authentication, before dependency resolution.

Typing is syntax-directed. Structural algorithm authentication has already
required every literal datum to be one exact canonical `MetaValueV0` within
the constitutional limits because that datum is part of the authenticated
term body. During later type derivation a literal contributes only its
explicit exact `ValueType`: its datum is not inspected against the type's
finite schema or owner law. After the complete reachable type set has exact
domain support, literal data are rechecked against the constitutional limits,
checked against their finite carrier shape, and owner-admitted in canonical
syntax order before request inputs are inspected.
`let` prepends its bound type. Record construction and projection use the exact
root record domain. Injection and case use the exact root variant domain, case
is exhaustive, and all branches have one result type. A conditional requires
the exact root Boolean domain and equal branch types. Sequence and iteration
use the exact root-domain equations in Section 5.2. Sequence length derives the
root natural type bounded by capacity. Strict index requires a root-natural
index whose exact type is also the failure payload type. Bounded append
requires and preserves an exact root-sequence source and has an exact root-Unit
failure payload. A primitive call uses only its authenticated, supported
declaration type rule; its returned value is owner-admitted before it becomes a
`CanonicalValue`. `Fail` checks its payload carrier type against the failure
declaration and uses its explicit success type solely to type the unreachable
success path.

The statically derived failure row is the canonical union from every subterm,
including unselected branches, plus each exact primitive declaration's row.
Evaluation remains strict in Section 7.1 order: an iterator evaluates its
source, then initial state, then body applications; only executed branches and
items incur effects on evaluator-control counters.

### A.4 Canonical completion bytes

For derived ABI failure row `failures[0..q)`, completion bytes are exactly:

```text
CompletionBytes(Success(v)) = M(V(0, v.datum))

CompletionBytes(DomainFailure(failures[i], p)) =
  M(V(i + 1, p.datum))
```

The envelope carries no repeated type or failure reference; the already
derived ABI interprets its tag and payload. Because a variant adds exactly
`17` octets outside its payload:

```text
MaximumCompletionSize = 17 + max(
  MaxDatumBytes(success),
  map(failures, f -> MaxDatumBytes(f.payload_type))
)
```

The corresponding tagged variant schema must itself be admitted by the full
`Worst` rule in Appendix A.2, so every completion case fits the constitutional
node, child-edge, and depth bounds as well. The byte result above must remain
within the constitutional canonical-byte bound. This is the exact meaning of
`TaggedCanonicalCompletionV0` and `MaximumCompletionSchemaV0` in Section 7.2.
