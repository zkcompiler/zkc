# Indexed Core elaboration experiment

This package asks one bounded architectural question: should a protocol family
replace exact finite `InteractiveCore` as the primary semantic object, or is a
small indexed authoring layer above exact Cores sufficient?

The experiment evaluates only the second design:

```text
authenticated IndexedCoreSchema + exact finite index
                         |
                         | deterministic bounded elaboration
                         v
                 exact finite Core body
                         |
                         | unchanged Core authenticate/admit
                         v
            CheckedCoreElaborationAt (live result)
                         |
              +----------+----------+
              |                     |
          Fresh Protocol       Fiat--Shamir Protocol
              \______ same exact CoreId ______/
```

`IndexedCoreSchema` is not a protocol meaning or a family theorem. It contains
a canonical finite index domain, a semantic static expansion bound, and the
complete AST of one program in a closed bounded template grammar. Its profile
identity also authenticates the complete formation and admission contract, a
closed semantic-law entry for every accepted grammar node, and global
evaluation-order, sizing, and delegation rules. Omitting a node is rejected;
changing a formation or mapping law rotates the profile.
Before canonical encoding or index enumeration, one carrier meter charges every
command, nested expression, reference, predicate, and tuple slot and enforces
exact total-node, structural-depth, and sequence-width caps. Admission then
preflights range materialization across every fiber in the finite index domain.
`SchemaId` authenticates all three. The grammar has typed natural, name,
reference, and finite name-sequence expressions, plus declarations, emissions,
`Static`, and finite `Repeat`. It has no recursion, general calls, effects, or
runtime-dependent topology. The authenticated language profile fixes the one
generic interpreter; schemas do not select an ambient family implementation
or carry an opaque generator label.

At one selected index, the checker computes the expansion size from the AST,
enforces the semantic output-and-command-work bound and its local evaluator
limit, interprets the
program, then delegates to the existing concrete Core admission and identity
authentication unchanged.

The issued `CheckedCoreElaborationAt` is deliberately live checker authority,
not another persistent semantic ID. `CoreId` is computed only from the exact
output Core body. Consequently:

- two structurally different programs may elaborate to the same Core;
- a narrower-domain schema may elaborate to that same Core; and
- in both cases the `SchemaId` values differ while the `CoreId` values agree.

Evaluator work limits are operational and do not enter either identity. The
schema's static expansion bound does enter `SchemaId`, because it is part of
the schema's promised semantic envelope.

## Selected fibers

The package uses two structurally different, intentionally small programs in
the same grammar:

1. A logical-oracle FRI shape with fold depths 2, 3, and 4; query counts 1 and
   2. Grouped and flattened AST structures encode the same program behavior,
   giving twelve checked program/index routes over six distinct finite fibers.
   Every route elaborates to a native-oracle Core, passes the existing Core
   checker, and executes as a same-Core Fresh/Fiat--Shamir pair.
2. A sumcheck shape with 1, 2, and 4 rounds. Each round has a prover message,
   a challenge, a check, and one linear claim reduction into the next round.
   Every selected index also executes as a same-Core Fresh/Fiat--Shamir pair.

One FRI fiber and one sumcheck fiber are independently hand-authored in the
tests. Their canonical Core bodies and `CoreId` values equal their generated
counterparts.

The negative cases cover:

- missing, extra, reordered, and out-of-domain semantic-index coordinates;
- malformed command aggregates and repetitions over an undeclared axis;
- explicit refusal of runtime-dependent topology;
- mismatched publication/next-challenge sequence lengths;
- a schema whose static output/work expansion bound is too small, including a
  nested repeat that emits only claim uses;
- excessive command nesting and excessive finite index products;
- oversized AST sequences, deep name concatenation, and oversized name ranges;
- an evaluator whose local limit is too small without identity rotation;
- a future occurrence reference rejected by concrete Core admission;
- a publication whose required least-following-challenge anchor is wrong; and
- a statement transcript frame moved after the challenges.

The all-index theorem API is a sentinel that always reports the feature as
unsupported. It records an explicit nonclaim; it is not negative evidence
against a family theorem or another family representation.

## Narrow authoring measurement

For one of the two equivalent FRI programs, the six selected expansions
contain 84 occurrence instances while its AST contains eight occurrence-
emission clauses. The sumcheck expansions contain 24 occurrence instances
while its AST contains four such clauses. The test derives the clause counts
by traversing each program AST and records the exact differences, 76 and 20.

This is a syntactic measurement of these two generators, not evidence that a
general schema language is smaller, safer, or expressive enough. The FRI
measurement counts one program rather than double-counting its structurally
distinct equivalent encoding. The result supports keeping a compact indexed
layer available for repetitive authoring; it does not support making that
layer the semantic root.

## Run

From the repository root:

```sh
python3 evaluation/indexed-core-elaboration/run.py --check
```

The gate uses only the Python standard library and the existing executable
foundation and Protocol/Fiat--Shamir reference models.

## Exact conclusion and limits

The finite result is consistent with this architecture:

```text
optional indexed authoring schema
        -> checked elaboration at one index
        -> exact finite InteractiveCore as semantic authority
```

It is evidence against immediately replacing `InteractiveCore` with
`CoreFamily` as the primary semantic subject. It is not a proof that every
useful protocol family fits this pattern. In particular, the package does not
provide dependent typing, recursion, data-dependent topology, preprocessing,
an asymptotic cost theorem, an all-index protocol theorem, or a security
theorem. The accepted finite repeat semantics cover only the exact bounded
index domains in each `SchemaId`. Any stronger claim remains owned by a
separately stated Analysis question with its own quantified basis.
