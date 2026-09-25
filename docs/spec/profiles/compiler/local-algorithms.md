# Canonical local algorithm expansion

This executable compiler profile connects a finite subset of
[stored local definitions](../source/definitions.md) to the current participant
machine. It does not change the common PIR observation relation. The
[implementation and evidence](../../../compiler/local-composition.md) describe
the adapter and its limits.

## Formation and intermediate representation

A local definition contains ordered primitive operations, role-free `apply`
instructions, [structured local regions](local-control.md), and one final return. An application names a local definition or
configuration in the same module and supplies exactly its ordered argument and
result types after checked static substitution. Generic signatures and requirement
entailment follow the [generic source profile](../source/generic-definitions.md).
The portable record is `["apply", site, callee, static_arguments, inputs, outputs]`;
only this six-field shape is admitted. Specialization eliminates static arguments
before common MLIR admission. No implicit capture is permitted. The whole local call graph,
including unused generic definitions and configuration-resolved edges, must be
acyclic and have at most 64 edges on a path. Source declaration order is not
scope order: resolution may topologically order the definitions to obtain the
scope of `Zkc.Source.Definitions`.

The ordinary affine-use checks apply at each call boundary and inside each
callee. Passing an affine argument consumes that binding; only declared results
are available afterwards. Repeated use, repeated return, or a wrong nominal type
is refused before expansion. This does not make every Boolean a mandatory-use
verdict. An executed `control.require` remains a guard even if all other results
of its containing helper are unused.

A callee may stop without producing its declared results. Expansion preserves
that stop and removes the caller suffix on that path. If specializing every arm
of an `if` or `match` leaves a join with declared results but no producing arm,
expansion refuses at that control operation (`algorithm-terminal-results`); it
never emits undefined or invented results.
An explicitly result-less all-stopping source region remains supported. Checked
library linking normalizes selected terminal callees earlier: it removes
unreachable join results before emitting this portable source. The portable
expander refusal remains for independently authored raw calls without that
normalization.

Native common IR retains these applications as typed `func.call` operations
inside isolated `func.func` definitions. Module admission checks the call graph,
local-only scope, complete signatures and affine use as well as MLIR's symbol
and SSA checks. Arbitrary control-flow regions, indirect calls, external callees
and calls to protocols are not legal local applications. Participant and physical
IR require all local applications to have been expanded; residual `func.call`
operations are refused at export.

## Expansion and accounting

The policy identifier is `canonical-expanded-locals/1`. It defines execution of
this subset by ordered, capture-free expansion before projection. Each nested
call substitutes its actual argument values, retains every primitive in source
order, and binds its returned aliases into the caller. A return adds no primitive
and runs the caller suffix only after the callee's primitives complete. No
primitive, guard, sample or semantic failure is removed, duplicated by sharing,
reordered or speculated. Multiple call occurrences execute distinct copies.

Returned aliases can make distinct duplicable capture bindings denote the same
value. Expansion retains the first capture occurrence, substitutes the region
arguments consistently, and removes duplicate loop capture forwarding. This
also applies inside nested regions. Affine argument reuse is still refused
before expansion; capture canonicalization does not authorize resource copying.

Native instruction, allocation and retained-value budgets apply to the resulting
executable body under the existing participant and backend policies. There is
one runtime local frame at the enclosing protocol `local` action. An inner
`apply` has no runtime frame, entry charge, return charge, or local destruction
point. Entered local control regions do create child frames under the
[local-control accounting contract](local-control.md#execution). Intermediates
remain in their owning frame until its cleanup or a checked storage release. Physical conversions and inserted
releases retain their existing accounting rules.

This policy does **not** assert exact resource equivalence with an interpreter
that allocates a frame or charges for every source `apply`. In particular,
flattening can extend lifetimes. Fixed-budget native failure and exhaustion are
observations of the canonical expanded machine; no sufficient-resources premise
is used to erase them. Complete logical primitive results include returned or
stopped outcome, reached effects, consumed resource state and the first failing
occurrence. The existing formal inlining theorem applies to its own selected
primitive interpretation, not automatically to native allocations or raw source
elaboration.

Compile-time expansion is separately bounded. Native and independent Lean
expansion charge each visited instruction and region body, including empty
callees and both conditional arms, against 32768 visits across the local definitions. Existing module
instruction and byte limits still apply to the output. A call path has at most
64 edges, and an encoded operation site is a source name of at most 128
bytes. Limit failures are compiler refusals, not protocol execution results.

## Origins, selectors and identity

A primitive occurrence has an enclosing function, an ordered sequence of
`(application site, original callee definition)` pairs, and its original primitive site. A function
containing an application encodes **all** its expanded sites, including direct
primitives. The encoding is `lc` followed by `_BYTE_LENGTH_COMPONENT` for every
path component and the leaf site. ASCII source names make byte lengths explicit
and the encoding unambiguous. Functions without applications keep their sites. A specialized callee uses its
logical definition origin, not its generated code symbol. Its enclosing function
origin retains ordered nominal static bindings for ordinary generic definitions.
A checked component member uses `Component.member` as its logical definition;
its exact selected identity stays in the linked symbol and selection evidence.
A logical member selector denotes all specializations of that member; the
generated symbol can select one specialization. Neither places long generated
hashes in nested operation sites.
Combining checked programs whose distinct exact declarations map to the same
qualified origin is refused (`library-origin-ambiguity`). An authored module
has one library identity; no cross-library selector resolution is inferred from
a shared component name.
For example, `Scale.scale` at `Linear.left` becomes
`lc_4_left_5_Scale_5_scale`; the right application has a different site.

The enclosing protocol call, selected role/instance and loop iteration remain
in their existing origin fields. This local path supplements those fields.
MLIR cloning retains the leaf diagnostic location; debug locations do not
establish semantic or transcript correspondence. `protocol-algorithm-map`
reports the output function/site, original definition/site and application path.
It is a derived inspection report, not trusted producer evidence. Source-relative
checking independently derives the expansion and compares actual primitive
order, operands, attributes and sites.

A construction selector `(definition, primitive site)` selects every expanded
copy of that definition's primitive, including generic instantiations and copies
in different callers. Ordinary function names and materialized top-level
configuration names also retain their direct selectors. Nested generic helpers
are selected by their original definition name. Naming an ordinary function
selects that function's primitive and its expanded copies, even when it shares
an explicit origin with sibling functions. Naming the group selects matching
occurrences across its members. Closed carrier selectors match both a concrete
function name and a logical origin with that spelling; ordinary helper copies
can legitimately share the latter. A direct function selector whose spelling
is also an origin other declared functions share names both the function and
their group, whether or not the function belongs to it; it is ambiguous and
refuses `construction-source-selector-ambiguous`. This is a construction request
ambiguity, not a program admission restriction.
Selecting across incompatible
randomness domains is refused by the existing construction domain check. It does
not select a single execution. A descriptor selects the union of its selectors'
occurrence sets, so selectors that reach the same occurrence select it once;
listing one selector twice is malformed. The constructor derives that occurrence
set before its existing resource analysis and retains the caller's original
descriptor in the certificate. Nested challenge origins carry their distinct
expanded sites. Native construction checking recomputes the candidate from the
original source; the independent Lean interpreter derives its own expansion and
selector mapping.

Exact identity retains original callable source. Normalized identity resolves
labels before expansion and includes the transitive local-helper closure.
Relabeling local application and primitive sites preserves normalized identity
when descriptor references and origin-family selector membership are preserved;
changing a reached helper body does not.

Normalized construction additionally requires each selected raw alias/site to
have exactly the same occurrence membership after declaration-local numbering.
A helper family's bodies need not have identical whole site maps, but at the
selected coordinate every raw occurrence must map to the chosen numbered site,
and every occurrence of that numbered site under the alias must have that raw
label. Otherwise only normalized construction refuses
`construction-selector-coordinates`; the program and exact construction remain
valid under their existing rules. A shared string does not establish an
origin-family correspondence. Unambiguous concrete-copy
selectors can select members with different site orders individually.
The declaration supplying a coordinate may have a call at that label while an
origin-family member has the selected primitive there. Coordinate resolution
does not replace construction's check of actual primitive occurrences after
expansion.
