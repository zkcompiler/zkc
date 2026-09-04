# F0-V2A canonical PIR view-schema feasibility gate

This disposable research package tests the description architecture selected
in
[`f0v2-canonical-view-schema-design.md`](../../docs-next/notes/semantic-revalidation-and-redesign/formal-assurance-research/f0v2-canonical-view-schema-design.md).
It does not change or implement the target Interaction profile.

The positive candidate contains one representative schema/value pair for each
of the five Core views and the Protocol `ExecutionView`. Together they exercise
the selected finite structural universe (`Record`, `Variant`, `Sequence`) and
all nine semantic atom classes:

```text
Unit
Natural
MetaBoolean
MetaSymbol
Bytes
CanonicalBody(exact compiler)
CanonicalValue(exact admitted type)
ExactProfileLaw(exact declaration)
AdmittedModuleEffect
```

The module-effect fixture is intentionally nested. Both observers validate its
exact module/declaration agreement and owner-schema result but emit the whole
effect as one atomic leaf; neither reflects into the `MetaValueV0` payload.

Two implementations inspect the same plain-data candidate:

- `model.py` uses recursive schema admission, enumeration, and resolution;
- `independent.py` uses an independently coded iterative stack machine and
  duplicates the closed compiler/law inventories.

They must agree on all six schema digests, all complete-manifest digests,
per-view leaf counts, instantiated module-effect boundary, total leaf count,
and the three distinct coordinates carrying an equal `ValueRef` value. Each
implementation also resolves every enumerated coordinate back to the exact
leaf and validates the supplied manifest as the complete sorted-unique active
leaf set.

Run from the repository root:

```sh
python3 -B evaluation/formal-source-view-schema-f0v2a/run.py --check
```

The frozen gate contains thirteen architectural findings and twenty-seven
dual-path refusal mutations. Mutations cover unknown/reflection nodes,
noncanonical and duplicate fields, empty variants, unknown atoms and body
compilers, generic descent into a module payload, missing/extra concrete
fields, inactive variants, sequence overflow, law and compiler substitution,
unadmitted canonical values, unsupported/invalid/wrong-owner module effects,
strict Boolean typing, complete-manifest omission/duplication/reordering,
wrong boundaries, interior/text/out-of-range paths, cross-view replay, and
equal-value coordinate aliasing.

An affirmative aggregate means only that one small PIR-owned description
universe and generic algorithms can represent and distinguish the bounded
pressure shapes. The exact six target body grammars, owner derivation from the
F1-R1B handles, target profile publication and identity migration, and
proper-subset dependency closure remain `CannotAnswer`. This package is not a
target body compiler, Core evaluator, view authority, source-correspondence
result, implementation check, formal proof, or security claim.
