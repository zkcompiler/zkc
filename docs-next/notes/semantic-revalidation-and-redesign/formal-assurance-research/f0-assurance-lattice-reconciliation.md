# Assurance-Lattice Reconciliation

> **Kind:** Temporary cross-lane reconciliation record
> **State:** First reconciliation complete at reading resolution; no durable
> vocabulary is selected until the design lane reviews it
> **Authority:** None. This note selects names for discussion only. It changes
> no owner page, profile, result family, or judgment.
> **Inputs:** the F0 claim lattice in
> [`f0-assurance-lattice-and-trust.md`](f0-assurance-lattice-and-trust.md);
> the ten-layer Fiat--Shamir lattice, claim levels, and proposed Analysis
> profile family in the absorbed package under
> `../semantic-closure-and-freeze/fs-assurance-pre-freeze/`; the current
> bridge demand in `docs/formalization.md` and the three-link bridge in
> `docs/ecosystem.md`; the Analysis four-role separation in
> `docs-next/analysis/analysis-model.md` Section 5.2.

## 1. Why one vocabulary is needed now

Two research programs written three days apart each produced an assurance
lattice for the same repository. The formal-assurance program produced eleven
claim levels, Q0 through Q10, ordered by what each claim is about: source
admission, source reification, provider correspondence, environment
authentication, theorem truth, applicability, property, Compiler transition,
property transport, OIR correspondence, and realization correspondence. The
Fiat--Shamir assurance program produced ten layers, L1 through L10, ordered
along the Fiat--Shamir security argument: structural prefix, closed Statement
correspondence, query encoding, transition binding, sampler, oracle process,
source property and theorem, projection, realization, deployment. Neither
program cites the other. Both select an owner-separated chain, both reject a
kernel-style authority, and both propose an Analysis profile family. If either
enters `docs-next/analysis/` as written, the corpus gains two overlapping
result vocabularies, which is the drift the design program exists to remove.

The two lattices are not rivals. One is a claim lattice, owner-neutral and
property-neutral; the other is a premise catalog for one property family. The
reconciliation below keeps the first as the shared spine and files the second
inside it.

## 2. Layer-by-layer map

| FS layer | Owner | Where it sits in Q0--Q10 | Note |
|---|---|---|---|
| L1 structural prefix complete | PIR | Q0, source admission of the FS Protocol and its checked same-Core construction | a PIR admission fact, not an Analysis result |
| L2 closed Statement correspondence | Relations | Q0 of the Relations owner; enters Q1 as part of the exact source closure and Q5 as a premise | F0 routes relation roles through Relations views; the FS lattice names the same owner |
| L3 logical query encoding adequate | Analysis | premise family inside Q5, with finite exhaustive cases as Q6 support | F0 had no named slot; this is a genuine addition |
| L4 transition binding adequate | Analysis, concrete fact later from Realization | premise family inside Q5; the primitive-binding assumption is a Q6 hypothesis | ditto |
| L5 challenge sampler adequate | Analysis | premise family inside Q5 | ditto; the four affirmative forms must stay distinct |
| L6 oracle-process correspondence | Analysis | the FS-specific content of Q2 when the provider is a game model, and a Q5 premise otherwise | F0's Q2 was stated for a formal artifact; the FS lattice makes the adaptive-process content explicit |
| L7 source property and theorem applicable | Analysis | Q4 theorem truth plus Q5 applicability, with theorem-source validation as Q3 | same separation, different granularity |
| L8 projection correct | OIR | Q9 | identical |
| L9 realizes OIR | Realization | Q10 | identical |
| L10 deployment approved | consumer policy | the reliance layer below Q10 | identical |

Two F0 levels have no FS counterpart: Q1, portable source reification for an
independently released consumer, and Q3 as a separate environment
authentication step. The FS program assumed same-process Analysis reads and
folded environment authentication into its theorem-source validation
subquestion. That is not a disagreement. F0's portable mode exists for a
consumer the FS program did not need; F0's local mode is the FS program's
assumption.

Two FS elements have no F0 counterpart: the claim levels S0 through S3, and
the three-way factoring of L4 into semantic encoder injectivity, adapter-chain
injectivity, and primitive binding. Both are worth keeping.

## 3. Proposed single vocabulary

1. **Keep Q0--Q10 as the claim spine** for every property family, because it
   is owner-neutral and already matches the current `docs/formalization.md`
   bridge demand: its five requirements are Q1 or local Q0 views, Q2 plus Q5,
   Q3, reliance policy, and Q9 plus Q10.
2. **File L3--L6 as the named premise catalog of the Fiat--Shamir property
   family**, each premise an exact slot in that family's Q5 applicability
   question and, where finite and exhaustively covered, a Q6 support entry.
   Other families get their own catalogs; none redefines the spine.
3. **Adopt S0--S3 as cumulative claim levels over the spine**: S0 is Q0 of
   PIR plus Q0 of Relations; S1 adds Q3 through Q6 for the named family; S2
   adds Q9 and Q10; S3 adds reliance. The levels are reporting language, not
   result identities.
4. **One Analysis intake, two question kinds.** The formal-interpretation
   family owns Q1 and Q2; the Fiat--Shamir family owns its Q5 premise catalog
   and Q6 property; both consume the existing theorem-source validation
   profile for Q3 and Q4. No `FSKernel`, no `FormalKernel`, no second
   outcome enumeration.
5. **Retire the numeric labels at absorption.** Durable pages name exact
   owner coordinates and result families; Q and L numbers stay in the
   temporary notes.

## 4. Points that need a decision, not a mapping

- **Where L6 lives depends on the provider.** For a VCVio interpretation the
  adaptive oracle process is part of the Q2 correspondence relation; for a
  paper theorem consumed through a receipt it is a Q5 premise. The family
  contract must say which, per provider kind, or the same fact will be
  checked twice or never.
- **Two Analysis families were proposed by two lanes.** The design lane should
  confirm the split in item 4 before either lane writes profile source.
- **Q1's portable package trigger remains unselected.** The FS program did
  not need it; the formal-assurance program needs it only under the
  independent-consumer scenario. The trigger is a project decision recorded
  in the Protocol IR architecture page, not something either lane can select.

## 5. Non-claims

This note proves nothing about any layer. It does not select profile source,
result identities, or wire formats, and it does not close any row in either
program. It records one consistent way to name the same facts so that
absorption into the Analysis owner happens once.
