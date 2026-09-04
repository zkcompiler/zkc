# M1 Mechanized Kernel Edges and Canonicity

> **State:** `Affirmative/M1-A-KERNEL-EDGES-AND-CANONICITY` for five bounded
> D1 carriers and the exact natural byte-bound pair
> **Authority:** None. This increment edits no target Foundation or PIR owner
> page and does not publish a semantic identity.
> **Executable evidence:**
> [`evaluation/formal-kernel-mechanization-m0`](../../../../evaluation/formal-kernel-mechanization-m0/README.md)

## 1. Question and answer

M0 showed that core-only Lean definitions could reproduce canonical K1 bytes,
strict-decoder vectors, D1 topological orders, and D1 class tables, and could
prove the encoder-to-parser direction. It deliberately accepted exported node,
edge, and transfer tables, did not prove decoder canonicity or class-fold order
independence, and could not execute the natural at the constitutional byte
edge.

M1 asks whether those gaps can be closed without changing the owner split:

1. decode the admitted Core and used semantic-module declarations from exact
   canonical bytes;
2. construct the Section 11 graph and all requested products in Lean;
3. prove accepted bytes are their datum's canonical encoding;
4. prove the class result is independent of topological-order choice;
5. replace the right-appending magnitude with a linear-list-work definition
   and run the `2^20`-octet natural in Lean; and
6. apply the supplied K1 natural-overhead decision and freeze both sides of the
   boundary.

The bounded answer is affirmative. All five carriers reproduce every D1 graph
product, all three new theorem families elaborate without `sorry` on standard
Lean axioms only, and both Lean and K1 accept the natural whose complete
encoding is exactly `2^20` octets while refusing the crossing K1 vector.

## 2. Evidence boundary and ownership

M1 preserves the existing responsibility handoff:

```text
Foundation canonical bytes
  -> admitted PIR Core plus authenticated module declarations
  -> PIR-owned PCGraph construction and class/sink products
  -> Analysis or deployment policy may consume the qualified view
```

The D1 exporter now exposes canonical Core-domain bytes and only the module
declaration bodies used by each carrier. Its node and edge tables are no
longer inputs. Lean decodes the fourteen Core tables, decodes module controls,
outputs, dependencies, transfer, visibility, and acceptance relevance, and
derives the graph.

The expected side remains D1's finite owner evaluator. Equality with it is a
bounded differential result, not proof that D1 is the uniquely correct reading
of prose. The Section 11 gaps below therefore remain `CannotAnswer` even when
the exact carrier tables agree.

## 3. PCGraph construction

The M1 Lean construction follows Section 11 items 1--6. It creates all
fourteen `PCNode` cases and adds:

- producer edges for derived values, guards, constructor operands, public
  Query indices, checks, reductions, terminals, and bindings;
- parent-opening and scope-opening edges;
- every earlier terminal decision as a liveness predecessor of a later
  activity, with no generic schedule-prefix edge;
- publication-to-Query and publication-and-Query-to-Answer edges;
- effect-to-output and effect-to-state edges; and
- exact declaration-owned module dependency, control, output, and outward
  occurrence-output edges.

The construction then derives the canonical Kahn order, class table, all
public sinks, acceptance sinks, private-input predecessors, LogicalAccess
influence cones, and their acceptance intersections.

The transport boundary is mechanically visible: the M1 vector's `input`
object contains only Core/module bytes; every graph table is under `expected`.
The Lean executable cannot use an expected edge table to build its graph.

## 4. Five-carrier result

| Carrier | Nodes / edges | Terminal-preemption edges | Query/Answer-target edges | Module edges | All products equal D1 |
|---|---:|---:|---:|---:|---|
| integrated baseline | 91 / 151 | 3 | 18 | 21 | yes |
| private Verifier-output sink | 91 / 151 | 3 | 18 | 21 | yes |
| invalid module-control sink | 91 / 151 | 3 | 18 | 21 | yes |
| history Challenge condition | 91 / 151 | 3 | 18 | 21 | yes |
| logical Reject preemption | 91 / 146 | 3 | 18 | 21 | yes |

"All products" means exact equality of node set, edge set, Kahn order, class
table, sinks, acceptance sinks, private predecessors, LogicalAccess cones, and
acceptance intersections. The edge-family columns are coverage counts, not a
partition of the edge table.

The retained 22 canonical M0 bodies still encode and round-trip exactly, and
all 25 malformed bodies still refuse. Thus graph construction did not trade
away the M0 encoding and decoder checks.

## 5. Decoder canonicity

Foundation Section 2.1 lines 94--97 requires a decoder to consume one value
and require byte-for-byte re-encoding equality. M0 proved the forward
direction, `parse (encode d ++ r) = some (d,r)`, but did not prove that accepted
input was canonical.

M1 separates the structurally recursive `parseRaw` from the strict `parse`,
which performs the specification's byte-for-byte re-encoding check, and proves
the requested remainder statement:

```text
parse_canonical:
  parse fuel b = some (d,r) -> encode d ++ r = b
```

The complete-input decoder corollary is:

```text
decode_canonical:
  decode b = some d -> encode d = b
```

The existing `decode_encode`, injectivity, and prefix-freedom results remain.
`#print axioms` reports `propext` and `Quot.sound` for both
`parse_canonical` and `decode_canonical`; there is no `sorryAx` or declared
package axiom. The theorem is explicit about its trust boundary: canonicity
comes from the strict parser's required re-encoding comparison, not from an
unproved claim about the unchecked structural recursion.

## 6. Class-fold order independence

The executable five-carrier comparison uses the deterministic least-body Kahn
order because that is the serialized owner order. The semantic class result,
however, should not change merely because another valid topological order was
chosen.

M1 defines the exact dependency list read by each transfer and a proof-oriented
fold indexed by any rank that places every dependency earlier. Membership
witnesses justify each recursive call. `classFoldByRank_solves` proves that the
fold satisfies every transfer equation. A well-founded induction then proves
that any two complete solutions agree at each node. Consequently:

```text
class_fold_topological_order_independent:
  Topological(rank1) -> Topological(rank2) ->
  classFold(rank1) = classFold(rank2)
```

The theorem is universal over the abstract indexed dependency graph, not an
enumeration of orders for the five carriers. Its axiom closure is `propext` and
`Quot.sound`.

## 7. Linear magnitude and the byte edge

M0's minimal magnitude recursively appended one octet to the right, making
list construction quadratic. M1 retains that definition as
`magnitudeQuadratic`, introduces an accumulator that conses low octets, and
uses the direct `1 :: zeros` representation for exact powers of 256. It proves:

```text
magnitude_eq_quadratic:
  magnitude n = magnitudeQuadratic n
```

The compiled Lean runner constructs `256^(1048567-1)`, encodes it as a natural,
and reports:

| Measure | Value |
|---|---:|
| magnitude octets | 1,048,567 |
| complete encoding octets | 1,048,576 |
| reaches byte bound | true |
| `encodeChecked` accepts | true |

This is an executed boundary case, not the earlier M0 statement that Lean
would accept "by definition".

## 8. K1 boundary decision

Foundation Section 2.1 lines 99--111 says reaching a cumulative bound is
allowed. A natural has one tag and eight length octets, while a signed integer
also has one sign octet. M1 applies the supplied decision directly:

- natural magnitude allowance: `2^20 - 9` octets;
- signed-integer magnitude allowance: `2^20 - 10` octets.

`reference_model.py` now passes the constructor-specific overhead to
`_magnitude_size` and `_minimal_magnitude`. The independent oracle and the
reference tests share no implementation but both expand the committed compact
recipes:

| Vector | Magnitude | Complete size | Outcome |
|---|---:|---:|---|
| exact natural bound | 1,048,567 | 1,048,576 | `Completed` |
| one octet across | 1,048,568 | 1,048,577 | `Malformed/CanonicalByteBound` |

The recipe form avoids adding multi-megabyte decimal and hexadecimal fixture
lines. The full `research.executable-foundations` gate remains 131/131.
`M0-C-NAT-BYTE-BOUND` is resolved; no owner page changed for this item.

## 9. Owner wording still `CannotAnswer`

M1 follows D1 but does not silently turn its choices into owner law:

1. **Challenge failure precedence.** `interactive-core.md` lines 1490--1493
   says "first failed dependency" but does not choose positional precedence or
   the D1 lattice-priority reading. The fifteen carrier Challenges do not
   distinguish them.
2. **Public Query transfer coordinate.** Lines 1486--1489 give
   `Join(activity,index)` without explicitly placing it on the Query effect
   node or saying that the publication-effect incoming edge is excluded from
   that named join.
3. **Deterministic Verifier-message transfer coordinate.** The same lines do
   not explicitly place `Join(activity,inputs)` on the output node even though
   the input edges terminate at the effect node.
4. **LogicalAccess publication transfer coordinate.** Line 1486 names an
   "Oracle publication output", but LogicalAccess has no occurrence output.
   D1 and M1 place `Publish(activity)` on the publication-effect node.
5. **Public Query sink coordinates.** Lines 1508--1511 name a public Query
   index but do not enumerate whether activity and effect are also retained as
   public-observation sinks. D1 and M1 retain all three coordinates.

These findings identify exact target locations for the owner, but this research
lane does not edit the target text.

## 10. Cost, axioms, and nonclaims

The executable report records each source file's code/comment lines and the
wall time for deterministic export, Lean build, large-carrier input assembly,
compiled execution, axiom reporting, the Python boundary probe, and the whole
gate. A warm run is approximately ten seconds on this lane; exact artifacts
own the measured number. `Axioms.lean` reports every theorem used by a finding
and the runner permits only `propext`, `Classical.choice`, and `Quot.sound`.

The 36-finding aggregate is finite mechanized and differential evidence. It
does not establish normative target publication, unique resolution of the five
wording findings, arbitrary-Core construction correctness, compiler or backend
correspondence, host semantic-module conformance, relation satisfaction,
theorem applicability, protocol soundness, Fiat--Shamir security, random-oracle
or concrete-sponge assumptions, QROM applicability, production readiness, or
a decision to make Lean a durable owner artifact.

M1 introduces no `FSKernel`, transcript-root authority, or semantic MLIR token.
Any promotion should remain with the existing Foundation, PIR, Analysis,
Compiler, Realization, and Evidence owners.
