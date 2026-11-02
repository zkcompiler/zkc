# Native installation

`zkc.native-installation/0` declares the physical choices of the native
installation: representations, provider preferences and their installation
units, field arithmetic forms and backend calling conventions. It is authored
in `common/catalog/installation.json`, beside the
[declaration catalog](contract-declarations.md), and the same three
independent validators check it: the catalog generator, the native TableGen
backend and the Rust build. It is a build and package input, not a
per-program serialization, and native compilation never reads it back at run
time.

The document holds available physical choices, the third of the
[four installed facts](contract-declarations.md#installed-instances). It
grants no declared meaning and no logical encoding, and it does not establish
actual compiled support: a target still resolves and admits the exact handler,
signature, storage owner and enabled contribution for every selected
representation and implementation. A preferred provider is a selection
preference, not an installation grant.

## Binding to the declarations

Rows reference declaration keys one way: a `(kind, domain)` logical type
instance, a domain identity, a codec identity or an operation name. The
declaration document never references this document. A native-installation
document is interpreted only together with the declaration document of the
same catalog package: every build, package and generated projection includes
both, and the package identity covers both. Each validator resolves every
reference against that declaration content and checks the referenced facts,
not only key existence. A physical-only change can change a toolchain identity
without changing the logical declaration projection, and the logical
declaration export never includes these tables.

## Inventory

The root has exactly `format`, `representations`, `appliedRepresentations`,
`providers`, `providerUnits`, `fieldForms` and `physicalArguments`. The format
tag is `zkc.native-installation/0`. Unknown fields, duplicate keys and
unresolved references refuse. Row order is declaration order. Identities use
the catalog name rule, and counts are JSON integers from 0 to 1,048,576.

```text
Representation        = {identity, kind, domain, default, layout, frame, unit}
AppliedRepresentation = {constructor, arguments, identity, default, child,
                         frame, provider, unit, vectorPort}
Pattern               = ["domain", sort, identity] | ["type", Type]
                      | ["natRange", minimum, maximum] | ["any"]
Reference             = {kind, domain, representation}
Provider              = {domain, default, alternatives}
ProviderUnit          = {provider, unit}
FieldForm             = {field, arithmetic, montgomery, byteEncoding}
PhysicalArguments     = {operation}
```

`Type` is the [logical type tree](logical-types.md). Providers are `arkworks`,
`blst`, `dalek`, `halo2curves-axiom`, `plonky3` and `spongefish`. Installation
units are `arkworks`, `blst`, `dalek`, `halo2curves`, `plonky3` and
`independent`. The two vocabularies stay distinct: a provider names the
implementation family that a binding selects, and a unit names the native
library contribution that owns its storage and handlers. `spongefish` is a
provider whose unit is `arkworks`; `halo2curves-axiom` is a provider whose unit
is `halo2curves`; `independent` is the unit of provider-free logical storage.

## Representations

A representation row makes one physical representation available for one
logical type instance. `(kind, domain)` is a declared logical type instance and
`(kind, domain, identity)` is unique. A representation identity may serve
several instances. At most one row per instance has `default` true, and every
instance has one default. `layout` is empty or an identity naming an explicit
layout selection, at most once per instance. `frame` is `canonical` when the
instance has a codec frame and the representation's value bytes are that
frame, and `local` otherwise; a `canonical` row requires a framed codec for its
instance, and the default of every instance with a framed codec is
`canonical`. `unit` is the installation unit that owns the storage. The
default of a unary instance has the unit of its domain's default provider,
and the default of a nullary instance has unit `independent`.

An applied representation covers a constructor applied to static arguments.
`constructor` is a declared type with parameters, or `variant`. `arguments`
has one pattern per parameter (none for `variant`): an exact Domain argument
naming a declared domain of the parameter's sort, an exact Type argument
`["apply", constructor, arguments]` naming an admitted logical type instance
(never a variant, oracle or service tree), a closed natural range `["natRange", minimum, maximum]` of canonical
decimals with minimum at most maximum at most 1,048,576, or `["any"]`. `child`
is null or a `Reference` to the representation row of the single dense child,
which must be the logical child of the applied type. A row with a child is a
dense container, and `provider` and `vectorPort` state its
[calling convention](#calling-conventions); both are null exactly when `child`
is null. A `canonical` applied row requires
an aggregate frame for its constructor (and for `field_array`, for its exact
field). Overlapping patterns of one constructor may not share an identity or
both be defaults.

## Providers

A provider row names a declared domain, its `default` provider and the ordered
`alternatives` that a binding may select instead; every domain has exactly one
row and no provider appears twice in a row. `providerUnits` has exactly one
row for each provider of the vocabulary, and no provider's unit is
`independent`; the unit owning a domain's default storage is
the unit of its default provider. A provider's unit applies only after a
binding has selected that provider and resolved an exact implementation; it
does not replace the target's handler and contribution check, nor the domain
dependencies of generic `native` operations.

## Field forms

A field form row describes the represented arithmetic of one declared Field
domain along two separate axes:

- `arithmetic` is null or `{form, representation}`: `form` is `residue`
  (canonical residue arithmetic of the declared structure) and
  `representation` names the default representation row of the field's
  `field` instance. `montgomery` is null or `{wordBytes, radixBits}`, with
  `wordBytes * 8 = radixBits`: a coordinate `x` is stored as the word
  `x * 2^radixBits mod characteristic`, which requires an `arithmetic` row and
  a characteristic below `2^radixBits`.
- `byteEncoding` is null or `{codec, order}`: `codec` names the field's `field`
  codec, which has a frame, and `order` is `littleEndian`, the coordinate byte
  order of that frame.

A Field domain has at most one field form row.

The axes are independent: a field with a byte encoding need not have residue
arithmetic, and the logical codec width is the codec's, never a provider's
internal word.

## Calling conventions

A dense container's `provider` names the provider whose dense operations use
the container, and its `vectorPort` is a `Reference` to the representation row
of the `vector` instance over the child's domain that those operations
exchange: the vector port of their signatures. The port row has an empty
`layout` and the container's `unit`. The provider is the default or an
alternative of the child domain's provider row, and its unit is the
container's `unit`. A provider has at most one dense container per
constructor. Consumers read the provider and the port from these columns; the
installation states no rule that selects them from units, layouts or names.

A `physicalArguments` row names a declared operation whose native binding
carries physical static type arguments, the represented types of its
type-parameter ports, in addition to its logical static arguments. Bindings
of other operations carry none, except `representation.convert`, whose
physical arguments are its contract. This is a backend calling convention: it
grants no mathematical meaning and is not part of the operation's logical
declaration.

## Validation

Each validator checks every rule above, including exact shapes, unique keys,
the closed vocabularies, every reference into the declaration document and
the facts it relies on: instance existence, codec kind and domain, Field
sort, the default and canonical-frame rules, child agreement, and the dense
calling convention's port row, units and provider. The two
documents are checked together, and each dump prints only its own tables.
