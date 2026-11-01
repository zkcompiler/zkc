# Distributed record source contract

This chapter defines role-bearing records in the checked source model. Native
component lowering, independently decoded interfaces, SDK binding and protocol
common-control integration must implement the same contract before the complete
record package is supported. The earlier direct logical-family source fixtures
remain migration controls; they do not define the role-bearing surface or a
second accepted shared interface schema.

## Declaration and application

A struct without a role telescope is ordinary data. A nonempty role telescope
makes a struct a distributed product, including one containing only ordinary
fields:

```zkc
struct State<T: Type> roles(P, V):
    pub local: T @P
    pub observed: index @V
    private_empty: () @P

struct Batch<T: Type> roles(A, B):
    pub state: State<T> roles(B, A)
    pub count: index @(A, B)

protocol Forward roles(P, V)(s: Batch<index> roles(P, V)) -> Batch<index> roles(P, V):
    return s
```

Each ordinary field has an explicit nonempty participant set. Its components
are role-local data; a set does not assert equality. A direct oracle field uses
an explicit holder-to-receiver arrow, including `@P -> (V, W)`. The holder is
outside the nonempty, distinct receiver set. A nested distributed field uses
an explicit ordered role application and has no overriding outer annotation.
Every application is injective. Declaration-role order is significant; data
and receiver sets are canonical sets.

An alias can abstract and apply roles independently of ordinary static arguments:
`type Reversed<T: Type> roles(A, B) = State<T> roles(B, A)`. Alias application
retains that map and the target's nominal type identity. A plain alias to a
role-bearing nominal type can retain its open role abstraction. Public protocol
ports explicitly apply roles, including through an alias. There is no ambient
roster default and no aggregate holder arrow for a role-bearing product.

Finite tuples and fixed arrays can contain explicitly placed distributed
products. Ordinary tuple members inside such a structural product specify their
own placements. For example, a field may have type
`([State<index> roles(P, V); 2], index @V)`. A fixed array retains its element
schema and exact role application even at length zero. Ordinary structs, enum
payloads, `T: Type`, associated representations and ordinary native collections
cannot hide distributed values. Category checking precedes storage expansion.
This check resolves aliases at every nesting level before discarding placement
metadata; an outer data annotation cannot overwrite a placed alias's category.

## Identity and schemas

`Type` retains ordinary nominal/static identity, including phantom arguments.
Placement is a separate checked judgment, represented beside Type by
`PlacedType` and optional placement metadata on ports, values, fields and alias
targets. Absence is meaningful in ordinary mathematical/local contexts. Protocol
boundaries validate the complete placed identity.

The existing placement alternatives are data, direct oracle and recursive
product. A heterogeneous structural tuple/array can retain an ordinary Type
while having Product placement, even if all of its leaves are ordinary data.
The placed-category query accounts for that metadata; the Type-only query does
not grant access to a whole structural product. A nominal product retains `typeIdentity(type)`, the ordered instantiated
role arguments and declaration-ordered child placements. Field identity is the
owning declaration plus ordinal. Names, visibility, exact types, row bounds and
empty children remain in the field schema. Structural products retain their
exact structural type identity; their role scope is derived from their children.
The array placement has one retained element-schema child, independently of the
number of storage elements.

Static specialization rebuilds product identity and children from specialized
types and checked field formulas. It never edits an encoded identity string.
Equal storage, equal role sets, changed nominal types and changed phantom
arguments do not establish placed equality. Participation summaries on products
are diagnostic/roster data and grant no field access.

## Values, permissions and order

Constructors evaluate field expressions once in written order and store operands
in declaration order. The checker checks complete field coverage, privacy,
constructor authority and ownership before publishing an aggregate. It uses an
explicit application, a unique expected placement, or a unique solution to field
placement equations. Ambiguous or inconsistent applications refuse with
`source.placement-inference`. It does not select a permutation by roster order.
An uninstantiated field schema guides category checking while the constructor
retains actual field placements for inference. It supplies no concrete roles.
Structural tuple/array equations recurse through child schemas; only nominal
product arguments supply an ordered telescope. Receiver sets remain unordered,
so an undistinguished receiver permutation remains ambiguous.

Projection follows the selected ordinal path and obtains that child's exact
placement. Whole forwarding, protocol arguments/results, assignments and repeat
initial/successor carries preserve full placed identity. A disjoint visible Copy
field can remain readable after moving a non-Copy child; overlapping moves and
whole uses after a partial move remain invalid. The zero-trip carry retains the
initial state.
Read-only repeat captures project the selected path before intersecting its
components with the loop roster. Ordinary data can select existing components;
logical captures retain their complete exact family or product placement.

Permissions derive recursively from field types and intersect explicit wrapper
restrictions. Privacy, placement, nominal identity, Copy and Drop are separate.
A role-bearing `#[linear]` or `#[affine]` wrapper does not acquire sealing merely
from the restriction. Fresh restricted construction is an authorized ordered
root bound with `<-`. Empty wrappers retain their source root obligation.
An authorized home protocol can explicitly consume a wrapper with
`fields <- unpack(state)`. The result retains each field placement in a structural
tuple; an empty wrapper produces unit. This does not permit implicit resource
unpack through a pure pattern. Ordinary calls, captures, finite-domain operands
and sends cannot interpret a product participation summary as ordinary data.
Multiple-role ordinary fields still satisfy the existing participant admission
contract, including after generic specialization.

The same installed `zkc::records::{inspect_record,repack_record}` declarations
support home-authorized consuming succession in Protocol mode. Inspection
returns `(same_wrapper, placed_payload)` with every required nominal custody
fragment forwarded once. Repacking passes each original fragment and replaces
only the payload, whose fields must actually permit Copy and Drop. Both calls
preserve the exact nominal/static instance, ordered role map and zero-storage
fields, and require all wrapper participants to be active. The lexical caller's
constructor authority is independently checked; the installed declaration grants
no access to sealed or private fields. Unpack followed by fresh construction
creates different roots and cannot replace this path at a repeat backedge.

General protocol branches require the separate projected-control and
common-value judgment. Local control lowering is not admitted in protocol mode.
Availability alone does not discharge agreement for a shared repeat. Native
custody fragments, Entry component selection, source/native comparison and
strict interface readers remain coordinated consumers of this source contract;
source checking alone does not establish those integrations or a security claim.
