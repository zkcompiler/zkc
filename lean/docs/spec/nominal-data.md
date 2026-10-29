# Nominal data and execution boundaries

`Source.Structured.Ty` owns the recursive type vocabulary.
`Source.Structured.Carriers.Value` is its value interpretation. A model supplies
arithmetic and helper semantics for those carriers; choosing a Lean carrier is
separate from proving field, group, embedding, or sampling laws.

`Construction.Domain.Payload` packages an exact type, a proof that its recursive
`Ty.isService` check is false, and a value at that type. Message eligibility uses
this check. It does not enforce a protocol relation, a length bound, a finite
sampling universe, or availability of a byte codec. Invalid statements and
oversized data therefore remain available to the modeled adversary.

## Nominal decoding

`Payload.value` casts only after equality of the complete nominal type.
`Payload.ofValue_value`, `Payload.value_ofValue`, and the fixed-type injectivity
laws connect packaging and decoding. Proof witnesses for service exclusion do
not contribute identity. In particular:

- different fields remain distinct when their Lean carriers coincide;
- vectors and sequences remain distinct, including empty values;
- product identity, constructor, and ordered field types remain present in
  the descriptor; field naming and use are fixed by the admitted source;
- a service anywhere inside an aggregate excludes the whole value from data.

Source admission checks descriptor well-formedness separately. Constructing a
Lean payload does not itself prove that its descriptor belongs to a selected
source program.

## Public statements

`Construction.Domain.PublicBinding` contains the application and an ordered row
of `(sourceCoordinate, Payload)` values. `PublicBinding.history_eq_iff` is scoped
to a fixed checked schema and coordinate list. It establishes logical statement
binding, without claiming injectivity across arbitrary schemas or cryptographic
collision resistance.

A statement includes all selected public coordinates. Relation evaluation may
ignore an inactive field; binding still retains its value. Missing coordinates
refuse preparation, rather than shifting later coordinates. Repeated relation
selectors and the ordered public ABI are different concepts: a relation may
refer to the same input more than once.

There is no second recursive domain-public-value encoding. The older uniform
public representation has a separate selected consumer and must not be used as
an unchecked conversion for a nominal row.

## Execution and proof views

`Construction.Domain.participant` interprets the admitted constructed
instruction tree. Data values, transcript capabilities and occurrence indices
are separate runtime cases. Arithmetic and helpers use the structured model's
operations. Checkpoints, stops, unread proof suffixes, and service state belong
to the complete execution.

A `Domain.Correspondence` proof relates this actual interpretation to a reusable
view. The proof quantifies every response at a receive or query. Rewriting with
that equation can serve several properties; it does not prove any property by
itself. Completeness additionally needs the actual producer, the fixed honest
input contract, a related input, and the selected success event. Soundness needs
the actual adversary interface and a rejection argument. A checked structural
projection or an export hash alone supplies neither argument.

The source protocol, constructed participant, ideal transcript experiment and
interpreted bytes have distinct meanings. Connections name both sides and
preserve the observations needed by their consumer. Extending the message or
oracle-key universe requires a new game proof or an explicit adversary
transport; an operational embedding is not sufficient to preserve a security
bound.

## Bytes and randomness

[Data codecs](data-codecs.md) add admitted values, byte limits, successful
encoding, decoding, and canonicality. Their laws apply to the selected format.
They do not establish equality to a native provider's serialization.

Aggregate transmission does not imply uniform aggregate sampling. A query site
fixes its reply type and distribution. The security layer supplies sampling and
probability laws; the operational core remains probability-free. Computational
hardness, query budgets, and extractor access are separate property contracts,
as described in [selected property adapters](selected-property-adapters.md).

## Model changes

A proof checked against a new payload, profile, or public-binding definition is
a proof about that new model. An unchanged theorem statement fingerprint does
not establish unchanged dependencies. The assurance process inventories each
protected root, records preservation theorems where claimed, and otherwise
re-establishes the property under its new exact model and request. Independent
kernel replay checks proof validity; model review checks the intended meaning.
Neither replaces the other.
