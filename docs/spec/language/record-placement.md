# Record schemas and participant placement

This chapter specifies the accepted layout-language record contract. Source
checking, native transport, recursive interfaces and SDK component admission
are implemented for the supported fixed-roster profile. The strict recursive
interface schema is published in the shared format. Coherent cross-branch
integration and independent formal-reader compatibility remain landing gates;
native support does not imply a formal interpretation of every record profile.
Serialized changes belong to the existing
[interface contract](../formats/entry.md) and [contract register](../contracts.md),
with strict producers and readers updated together.

## Schema, placement and native components

A logical type schema, an instantiated participant placement, and a native
component observation are distinct. Ordinary type identity retains the nominal
declaration and every kinded static argument, including phantom arguments.
Placement adds exact participant association without changing an ordinary type
argument into a participant or granting field access.

There are three placement alternatives:

| Alternative | Meaning |
|---|---|
| Data | A nonempty canonical set of distinct participant-local components |
| Oracle | One holder and a nonempty canonical receiver set excluding that holder |
| Product | An exact type instance, an injective participant association, and declaration-ordered child placements |

A product has no aggregate availability or oracle holder. Its role union is not
access authority, common-value evidence, or a substitute for its child
placements. A child cannot name participants outside its enclosing product's
role application. Empty fields and empty products retain their schema and
identity even when they have no native data storage.

Role applications are ordered maps. Data availability and receiver membership
are sets. Applying a protocol role substitution preserves product argument order
and canonicalizes the resulting sets. Structural tuple/array argument unions
are canonicalized as sets after substitution; nominal telescope arguments
retain their declaration order. Authored delivery order remains separate
invocation information: canonical receiver membership does not reorder sends or
their observable failure prefix.

For a nominal distributed record, Product arguments follow its declared role
telescope. For a structural tuple or fixed array, they are the canonical union
of its child participants. A tuple such as `(index @P, bool @V)` retains the
same static type schema as a locally placed `(index, bool)`; its Product
placement carries the difference. Ordinary schema leaves do not grant aggregate
access to a distributed value. An array carries one element-placement template,
including at length zero, and validates it without allocating native components.

## Declarations and formation

An ordinary `struct` has no role telescope. A `struct` with `roles(...)` is a
distributed logical product. For example, the target layout surface is:

```zkc
pub struct RoundState<F: Field> roles(P, V):
    table: Vector<F> @P
    pending: Pending<F> @V

pub struct Batch<F: Field> roles(P, V):
    state: RoundState<F> roles(P, V)
    count: index @(P, V)
```

Every ordinary field of a distributed product has an explicit placement.
A nested distributed field supplies its own role application; an outer
availability annotation cannot overwrite it. Aliases preserve nominal identity
and the exact role application. Constructor inference may select a unique
application from its expected placed type and checked field constraints;
ambiguity refuses. Public signatures expose the role application unless an
alias already closes it.

Category checking precedes storage expansion. Ordinary type parameters, ordinary
vectors, associated representations and zero-length arrays cannot hide logical
handles or distributed products. Admitted fixed logical products retain every
element's role association; a zero-length container still retains and checks
its element schema. Runtime-variable participant sets, recursive distributed
layouts and distributed variant alternatives are outside this profile.

Constructor operands are evaluated exactly once in authored order, then stored
in declaration field order. Projection validates visibility and obtains its
placement from the selected schema path. Forwarding a whole product preserves
its exact map; it does not move each field to every participant in the product.

## Permissions and custody

Transparent-product permissions are the intersection of child permissions,
further restricted by explicit wrapper annotations. An affine restriction removes
Copy; a linear restriction removes both Copy and Drop. Neither restriction grants
a missing permission. Sealing and field privacy are independent access rules.
An explicitly restricted wrapper retains its root usage obligation even when
transparent or empty; visiting its droppable fields cannot discharge that root.

Explicit restrictions retain nominal native custody. A distributed restricted
wrapper has one source obligation and a local custody fragment at each declared
role, with separate paths for nested wrappers. Fragment observations retain
nominal specialization, wrapper path and role; nominal native unit types and
actual resource origins remain distinct. Actual SSA/resource origins distinguish
different dynamic instances of the same type. Equal fragment types do not
authorize mixing fragments from different instances.

Fresh construction is ordered and home-authorized. A consuming successor API
must retain a checked relationship to the selected old custody in its actual
emitted operations. Destruction followed by fresh construction does not acquire
that relationship merely from an equal nominal type. Native comparison checks
actual operands and transitions; source restrictions alone are insufficient.

Existing prefix-overlap move checking applies to declared field paths and aliases.
Calls, branch yields and loop carries preserve exact placed schemas and custody.
Zero-trip loops retain their initial values and origins. Stopped outcomes remain
distinct from successful Drop or a continuing successor.

## Component observation and independent checking

Each retained native component is identified by:

```text
(declaration field path, local leaf, participant, facet, native coordinate)
facet = data | oracle_data | oracle_anchor | custody
```

The component map is derived from the schema and placement. It must have complete
coverage and exact types, roles and facets. Different participant components may
select the same existing multi-role SSA coordinate; uniqueness is over the typed
source component, not the native integer. Zero-storage members retain schema
paths without fabricated native components.

The independent interface reader reconstructs this observation from decoded
schemas and actual candidate signatures. It does not trust the producer's map.
Source/interface comparison additionally checks retained source association and
authority; actual-body comparison checks the emitted operations and operands.
These checks are separate. In particular, equal layout types are not evidence
that two fields, oracle anchors or resource instances are interchangeable.

## Entry and formal consumers

Root adapters select typed ordinary components by input, declaration path,
participant and facet. Admission checks visibility, domain, setup/public policy,
coverage and exact ABI association. It cannot fabricate oracle anchors or
custody from user bytes. Selecting ordinary fields of a logical input does not
supply its remaining handle or resource obligations.

A heterogeneous aggregate is not implicitly public. The existing proof policy
requiring public coverage for verifier-available ordinary data remains in force
at component granularity. Public-input agreement is a separate admission fact;
it does not follow from multi-role placement.

Shared source and interface changes retain the existing development version `0`.
Publish exact schemas and positive/mutated fixtures before changing producers,
then update affected native readers and SDK adapters together. The Lean owner
implements its reader, interpretation and connector. Reader compatibility and
new formal proof completion are separate integration gates; this placement
contract grants no new receipt status, claim stage or correspondence theorem.
