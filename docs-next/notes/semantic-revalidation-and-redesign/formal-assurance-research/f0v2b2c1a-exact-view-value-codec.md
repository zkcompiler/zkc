# F0-V2B2C1A Exact View-Value Codec and Ordering

> **Kind:** Temporary reopened-F0 owner-projection prerequisite
> **State:** Complete at exact-value codec resolution with
> `Affirmative/F0V2B2C1A-A-EXACT-VIEW-VALUE-CODEC`; B2C1B1 has since completed
> four foundation projection families, while seventeen isolation families
> remain
> **Authority:** None. This note and executable package do not change PIR,
> the Interaction profile, a compiler, evaluator, runtime, or Analysis
> judgment
> **Predecessor:**
> [`F0-V2B2C0 canonical-byte owner admission`](f0v2b2c0-canonical-byte-owner-admission.md)
> **Executable gate:**
> [`evaluation/formal-source-view-codec-f0v2b2c1a`](../../../../evaluation/formal-source-view-codec-f0v2b2c1a/README.md)

## 1. Decision

B2C1 needs an exact schema-directed value codec before it can compare owner
projections. Equality of diagnostic objects is insufficient. The selected
research topology is:

```text
authenticated B2B view schema + derived diagnostic value
  -> recursively compile every structural node and exact atom
  -> one complete K1 MetaValueV0 body

same schema + value
  -> independent iterative postorder compiler
  -> byte-identical K1 MetaValueV0 body
```

For a `SortedUnique` sequence, both paths sort and validate using the exact
compiled element body. No JSON serializer, host record order, display label,
or tuple comparison participates in target ordering.

## 2. Discriminating findings

The smallest order probe uses `ConstantNode(0)` and `ReductionStateNode(0)`:

```text
M(PCNodeBody) order  = [case 2, case 10]
JSON wire order      = [case 10, case 2]
```

The two exact codecs accept only the first sequence. Both B2B diagnostic
validators accept only the second. This is not a contradiction in B2B's
scoped inhabitance result: that package explicitly made JSON diagnostic-only
and generated no multi-element sorted sequence. It does prove that the B2B
validator is inapplicable to target owner values at this boundary.

The second finding concerns leaf embeddings. B1's identifier helper stored raw
`ContentRefV0(id)` bytes in its diagnostic atom. Those bytes are not a complete
MetaValue datum. The exact enclosing body requires:

```text
MetaBytes(ContentRefV0(id))
```

Both codecs reject the raw representation and accept the wrapped one. B1's
bounded derivation claim remains diagnostic; its values must not be promoted
as exact target view bodies.

## 3. Executable result

The package freezes 22 findings. At scoped resolution it establishes:

- agreement on the same six B2B schemas;
- one exact sample for all 22 candidate leaf-body compilers;
- exact profile-local bodies for the three referenced laws;
- one authenticated, opaque module-effect framing witness;
- recursive/worklist agreement on all 302 B2B branch inhabitants;
- full decode and byte-identical re-encode for every exact body; and
- rejection of compiler/law/profile substitution, malformed framing, and
  duplicate or wrongly ordered target collections.

The module witness establishes framing only. Its declaration semantics are not
accepted as a Core effect by this codec.

## 4. Main-design consequence

F0-V2C should publish enough source for an independent implementation to
derive both conformance and exact value encoding from the same schema entry:

```text
PIRStaticViewSchemaDeclaration {
  structural schema,
  exact leaf-body compiler references,
  exact law references,
  exact recursive value-body interpretation,
  sequence discipline
}
```

The exact recursive interpretation need not be a callback or another kernel.
It is the closed structural meaning of Record, Variant, Sequence, and the
authenticated atom compiler catalog. This keeps body formation with the
existing PIR profile owner and gives `SortedUnique` one unambiguous order.

B2C1B must consume this codec rather than compare JSON values. B2C1B1 has
since done so for the first four foundation families. Each of the remaining
seventeen isolation families still needs an authenticated minimal carrier,
retained owner facts, a reference projection, a cold byte-derived projection,
exact six-body equality where applicable, and its named negative
discriminator.

## 5. Non-claims

This result does not admit or project any new Core constructor, establish
complete owner/source correspondence, validate a complete or integrated
`PCGraph`, define runtime Oracle receipts, publish or migrate the Interaction
profile, verify current implementation correspondence, prove a theorem,
establish a cryptographic property, or close Q1. The remaining B2C1B slices
and B2D remain open.
