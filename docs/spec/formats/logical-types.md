# Structured logical type data

This page specifies `zkc.logical-types/1`, used by the foundation's versioned
shared exports. It is structured interchange data, not MLIR textual assembly,
a native handle or a mathematical admission certificate. Current support is
recorded in [status](../../status.md).

The standalone record is `["zkc.logical-types/1", types]`. Enclosing formats
may embed the `types` array under their own version. Entries are complete type
trees, interned by exact structural equality in first-use order. References are
canonical unsigned decimal strings indexing this table. Duplicate and unused
entries refuse; references cannot invent domain or installation authority.

```text
Type = ["apply", constructor, [Argument...]]
     | ["variant", Identity, [[alternative, [Type...]]...]]
     | ["oracle", kind, [Argument...]]
     | ["oracle_sequence", kind, [Argument...], maximum]
     | ["service", contract]
Argument = ["domain", sort, identity]
         | ["type", Type]
         | ["nat", decimal]
Identity = ["atom", text] | ["tuple", [Identity...]]
```

`constructor`, argument kinds and their order must agree with a declared type
head. Boolean and u64 index are the nullary `bool` and `index` applications;
field values use `field` with their nominal Field argument. Sequence and fixed
array applications retain their complete element and extent arguments.
Encoding a constructor does not add it to a consumer's admitted profile.

Variant alternatives are nonempty, uniquely named and ordered; each payload
list may be empty. Identity is the complete structured nominal identity term,
including phantom static actuals. It is not a hash, an MLIR printer result or a
JSON document inside a string. This is the structured form of the existing
[nominal identity and payload rules](../ir/variants.md). A one-alternative
product retains the same identity, alternative and child order. Source field
names, role views and native-port associations remain in the enclosing logical
layout, not inferred from equality of leaf types.

Oracle kinds have the exact closed kinded arguments defined by their contract;
associated Data/Query/Answer types and named shapes are derived and checked.
Oracle and service cases are logical interfaces. They are recursively excluded
where an ordinary native payload or codec is required. Logical claim records
may retain handles under their separately admitted role/custody layout; this
does not grant them a native codec.

An identity atom is exact nonempty UTF-8, with no normalization during decoding.
Identifier-valued fields use the owning declaration's name grammar. Naturals
match `0|[1-9][0-9]*` and fit the owning bound; `maximum` and index values fit
u64. A domain identity includes its declared sort. Equal representations or
equal moduli do not merge distinct nominal domains. Extensions retain their
associated base and selected basis through complete catalog and layout records.

The type table contains at most 4096 entries. Expanded traversal has depth at
most 64, at most 200,000 nodes and at most 64 MiB of metadata; a variant has at
most 512 alternatives and each alternative at most 512 payloads. Enclosing
formats may impose stricter limits. Sharing must not bypass expanded-work
limits. Unknown tags, wrong arities, wrong JSON kinds, malformed Unicode,
unknown constructors, inconsistent argument kinds and duplicate alternatives
refuse. No fallback parser accepts a printed MLIR type or the old hex descriptor
where a structured Type is required.

Data.Value and other compiler-only layout carriers must expose their existing
logical schema as typed attributes internally. They are not given a public
type case by this format. A consumer either lowers them through their owning
logical-layout contract or refuses export; it cannot replace them with an opaque
string. Physical representation, ordered children and byte layout remain the
responsibility of the selected target and [program byte language](program-bytes.md).
