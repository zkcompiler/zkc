# F1-R temporary package and checker contract

> **Kind:** Executable research contract
> **Authority:** None. This format is disposable F1-R instrumentation and is
> not a selected zkc artifact, identity profile, Analysis family, or public
> compatibility promise.

## 1. Purpose

The F1-R package tests one boundary from the formal-assurance F0 result:

```text
complete static owner authentication preimages
  + one question-relative exact semantic-read projection
  -> independently checked Q1-style agreement
```

The package is inert. It carries neither admission authority nor live owner
capabilities. The positive fixture is a manually formed model of the selected
target's Fresh Schnorr verifier surface. Shared-challenge/interleaving and
Fiat--Shamir fixtures are discriminators for observations a plain alternating
Schnorr package cannot exercise. F1-I must replace every manually formed body
and view with live owner-issued values before any implementation-conformance
claim is available.

## 2. Wire subset and canonical value encoding

The wire is strict UTF-8 JSON with a maximum of 1 MiB. Duplicate object keys,
floating-point numbers, negative numbers, integers outside unsigned 64-bit
range, non-ASCII strings, control characters in decoded strings, nesting
deeper than 64, and values outside JSON null/Boolean/u64/string/array/object
are malformed. Every decoded string is nonempty printable ASCII. Object keys
are subject to the same rule.

The canonical value encoding is compact JSON over the decoded value:

- object fields are ordered by unsigned ASCII byte order;
- arrays preserve order;
- `null`, Booleans, and u64 naturals use their shortest JSON spellings; and
- strings quote `"` and `\\` and otherwise emit their printable ASCII octets.

Whitespace and lexical escape choices in the input therefore do not affect an
identity. The Python and Rust checkers implement this contract independently;
they share neither a parser nor a canonical encoder.

For domain `D` and value `V`:

```text
Id(D, V) = "sha256:" || lowercase_hex(
  SHA-256(ascii(D) || 0x00 || CanonicalJson(V)))
```

The temporary domains are:

| Value | Domain |
|---|---|
| formal source contract body | `zkc/f1r/contract/v0` |
| authentication-node preimage | `zkc/f1r/auth-node/v0` |
| complete package without `asserted_package_id` | `zkc/f1r/package/v0` |
| exact closed manifest | `zkc/f1r/manifest/v0` |
| formed agreement proposition | `zkc/f1r/proposition/v0` |
| affirmative agreement body | `zkc/f1r/result/v0` |

## 3. Top-level package

Every package has exactly these fields:

```text
{
  format,
  semantic_profile,
  contract: { asserted_id, body },
  authentication: { roots, nodes },
  manifest,
  projection,
  ledger,
  asserted_package_id
}
```

`format` is `zkc.formal-source-package.f1r.v0`. All set-like sequences are
strictly sorted and unique by their named ASCII coordinate. Order-bearing
source values, including occurrence schedules and transcript influence, remain
arrays and are never sorted.

### 3.1 Contract body

The contract body has exactly:

```text
{
  contract_schema,
  package_schema,
  semantic_profile,
  root_requirements: [{ coordinate, kind, profile }],
  read_roots: [ReadCoordinate],
  read_catalog: [{
    coordinate,
    source_node,
    source_pointer,
    value_kind,
    requires: [ReadCoordinate]
  }],
  protected_observations: {
    ObservationClass: [ReadCoordinate]
  },
  excluded_support_kinds,
  finite_controls: {
    max_wire_bytes,
    max_depth,
    max_auth_nodes,
    max_reads
  }
}
```

The checker verifies the contract ID, validates every reference, computes the
fixed point of `requires` from `read_roots`, and rejects cycles. The catalog
must equal that fixed point: dormant, unreachable read rows are malformed.
The contract profile must equal the package profile. Every protected
observation maps to a nonempty set of exact reads, and the union of those sets
must equal the required-read closure. The map records what the fixture intends
to retain; it does not itself establish a cryptographic property.

### 3.2 Authentication closure

An authentication node has exactly:

```text
{
  coordinate,
  kind,
  profile,
  dependencies: [NodeCoordinate],
  body,
  asserted_id
}
```

Every body is an object whose `imports` field is exactly the same sorted-unique
coordinate sequence as `dependencies`. For a node `N`, the ID preimage is:

```text
{
  coordinate: N.coordinate,
  kind: N.kind,
  profile: N.profile,
  dependencies: [{ coordinate, id }],
  body: N.body
}
```

Dependency IDs are recursively recomputed, not accepted from the producer.
The declared roots must match the contract's root requirements. Their complete
dependency closure must equal the complete node set; missing and unreachable
preimages are negative results.

### 3.3 Exact read projection

`manifest` is exactly the sorted fixed point of the contract's read graph. A
projection row has exactly:

```text
{
  coordinate,
  source_node,
  source_pointer,
  value_kind,
  value
}
```

`source_pointer` is a restricted RFC 6901 JSON Pointer rooted at `/body`.
Every projection row must use the source node, pointer, and kind named by its
contract catalog row, and `value` must equal the value independently selected
from the authenticated node. Contract catalog source bindings are one-to-one.
Exact source coordinates are checked even when two selected values have the
same type and content.

`ledger` repeats only the total coordinate-to-source binding:

```text
{ coordinate, source_node, source_pointer }
```

Its coordinates and bindings must agree exactly with both the manifest and
the contract. A package containing any projection row whose `value_kind` is
listed in `excluded_support_kinds` is refused before ordinary extra-read
classification. This makes attempted serialization of confidential values or
causal capabilities a boundary refusal rather than an innocuous unknown row.

## 4. Q1-style result

After all checks, each implementation returns the same checker-independent
agreement body:

```text
{
  class: "Affirmative",
  code: "F1R-AFFIRMATIVE",
  contract_id,
  package_id,
  manifest_id,
  proposition_id,
  result_id,
  root_ids: [{ coordinate, id }],
  required_reads: [ReadCoordinate]
}
```

The proposition binds exact contract, package, root IDs, manifest, profile,
and the direction `ExactSemanticReadAgreement`. `result_id` authenticates the
same agreement body without itself. Checker implementation identity and local
diagnostic text are deliberately outside this common result; a durable
Analysis result would additionally bind its validation basis and residual
trust.

## 5. Outcome precedence

The checker returns the first applicable class in this order:

1. `DeterministicLimitExceeded` for outer wire/depth/count limits;
2. `Malformed` for undecodable or ill-formed values and schemas;
3. `Refused` for excluded owner-local support;
4. `KindMismatch` for a formed package in the wrong semantic profile or root
   kind/profile; and
5. `Negative` for an exact formed proposition whose authenticated source,
   manifest, coordinate binding, selected value, or asserted identity
   disagrees.

The mutation ledger in `cases.json` fixes the exact expected class and stable
code for every F1-R case. This evaluator's codes are local research codes, not
allocated zkc diagnostics.
