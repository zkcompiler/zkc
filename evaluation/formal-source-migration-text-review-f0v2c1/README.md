# Migrated owner-text freeze review

This package asks one exact question: does the migrated PIR owner text close
the nine independent freeze-review questions for decision fidelity, the
Terminal contract, public-coin graph transfers and sinks, owner-view closure,
manifest closure, publication reconstruction, family-view body closure,
reference-leaf closure, and static-view law-field selection?

Run from the repository root:

```sh
python3 -B evaluation/formal-source-migration-text-review-f0v2c1/run.py --check
```

The round-six frozen answer is
`Affirmative/F0V2C1-A-MIGRATION-TEXT-CLOSED`: all nine questions close. The
`PIRReference` declaration arm at `docs-next/pir/interactive-core.md:2256-2259`
now ranges over the declaration kinds recognized by the selected profile's
exact-used owner-module closure, and `PIRReferenceBody` remains closed under
that profile at lines 2261-2266.

The declaration-kind set is determinate from the three profile pages. The
Interaction profile recognizes nine kinds at
`docs-next/pir/interactive-core.md:111-118`. The canonical-framed profile
imports Interaction at `docs-next/pir/fiat-shamir.md:73-74` and adds
`pir.fs-application-domain` at lines 68-71, for ten kinds. The duplex profile
imports exactly Interaction at `docs-next/pir/duplex-sponge-fiat-shamir.md:58`,
lists its declaration catalog at lines 68-71, and states its no-extra closure
at lines 73-76, so it recognizes the inherited nine and adds none.

The checker pins the six migrated owner pages, eight migrated manifests, and
the two earlier candidate packet sources. It recursively walks all sixteen
`StaticViewSchema` bodies and their owner-defined type aliases. The frozen
census has 386 reference-leaf occurrences: 332 take `PIRReference`, 35 take
`PIRProfileLawReference`, two take `AdmittedModuleEffect`, and seventeen
portable algorithm references take `Bytes` through their exact identity body.
Every occurrence takes exactly one displayed `PIRViewAtomicBoundary` arm and
none is uncovered. The checker also covers the split source-envelope compilers and
no-policy arm counts, every manifest declaration and subject reference, the
dependency graph, selected revision transitions, and all 95 fields in the
eight family bodies. Every field must be an exact identity, value, natural,
closed tag, law reference, record, or sequence of those. It also exhausts the
opaque-guard implication fixture, checks the strict impossible-region refusal,
and reconstructs the exact seventeen-profile rotation cone with two
independent publication compilers. Round three additionally exhausts 3,108
small schedule/opening variants and 47,280 attemptedness comparisons. `Region`
is exact on that corpus, its 3,868 impossible regions are exactly the
unreachable regions, and 23,640 opening-boundary comparisons reproduce the
deterministic unguarded boundary. Across 18,282 path-referenced claim cases,
including 14,148 using that candidate boundary as the source, no `Live` or
`Dead` verdict is unsound. Four direct source discriminators cover an initial
Claim opened Initially, initial Claims opened before unguarded and guarded
occurrences, and a Reduction output observed at a later identically guarded
terminal. All four are `Live`; the guarded-opening case remains `Unknown` under
the pre-repair occurrence coercion. A separate 238-term must-fact corpus checks
the non-Boolean, catch-all-constructor, contradiction, and impossible rules.

The path reference also rechecks 58 claim/frontier pairs in the exact terminal
projection, the five integrated carriers, and the represented WHIR and
WARPfold holdout shapes: 49 are `Live`, nine are `Dead`, none are `Unknown`,
and neither verdict has a counterexample. Four source-specialized holdout rows
still lack exact carriers and are not silently filled in. Reusable claim 0 is
`Live` at all fifteen integrated terminal frontiers, so the mechanization
package's five-carrier refusal stands.

The round-five law-selection audit separately finds all 35 displayed
`PIRProfileLawReference` fields and exactly 35 table entries: five in the
Interaction profile, thirteen in the canonical-framed profile, and seventeen
in the duplex-sponge profile. Every selected declaration exists at a
determinate catalog ordinal, all four imported entries have consuming-schema
dependencies, all nine new selectors occur exactly once in their source
fragments, and none of the twenty pre-existing law ordinals moved.

A passing `--check` reproduces the frozen nine-affirmative result and the
digest of the complete evidence metrics. It does not choose the semantics of
any nominal declaration, establish that the recognized-kind sets are complete
for an unlisted future profile, or repair owner text. It also does not publish
or bless an identity, prove the Terminal law for arbitrary Core values, validate a live
compiler/runtime/backend, establish relation satisfaction or theorem truth, or
make a Fiat--Shamir, random-oracle, concrete-sponge, QROM, protocol-security,
endpoint-validity, deployment, or production-readiness claim.
