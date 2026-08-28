# K2 Protocol and Fiat--Shamir Kernel

> **Document kind:** Temporary bounded work-package charter
> **Document state:** Bounded K2 package narrowly reclosed at its pre-K3-E
> checkpoint; current rotated-profile reclosure is owned by the
> [K3-E integration record](../k3-minimum-consumer-co-design/k3-e-integrated-closure.md)
> **Provisional owner:** `pir`, coordinated by `project`
> **Authority:** None. This package records research, selection, and validation;
> current normative Protocol and Fiat--Shamir rules remain under
> [`docs/`](../../../../docs/README.md).
> **Activated:** 2026-08-26
> **Completed:** 2026-08-26
> **Narrow reclosure:** 2026-08-26, after exact-body and evidence-boundary
> repair; that historical checkpoint and focused follow-up are recorded in
> [`validation.md`](validation.md)
> **Disposition:** Selected semantics and exact limitations are absorbed into
> the durable PIR owners. Retain this research/validation package as optional
> reference until the redesign notes are normalized before cutover; durable
> pages must not depend on it.

## Scope

K2 closes the finite Protocol and structural Fiat--Shamir kernel over the
selected [K1 executable foundation](../k1-executable-foundations/README.md).
It selects and tests:

- the exact finite `InteractiveCore` and `Protocol` boundary;
- typed input occurrences, explicit Statement scopes, and private-value
  classes needed by later Relations and Analysis consumers;
- actor-visible histories, legal decisions, causal strategy-generated runs,
  and non-authoritative replay;
- the v0 effect algebra, including native immutable oracle publication and
  query/answer interaction;
- derived transcript influence and exact challenge prefixes;
- structural public-coin eligibility;
- a complete state-passing Fiat--Shamir initialization, absorb, framing,
  squeeze, decode, bounded-retry, and typed-failure contract;
- the checked relation between Fresh and Fiat--Shamir interpretations; and
- the registered Core choices whose answers affect identity, execution, or
  admission.

K2 does not establish soundness, knowledge soundness, zero knowledge, random-
oracle or quantum-random-oracle applicability, quantitative loss, relation
grounding or satisfaction, OIR projection correctness, compiler legality, or
implementation migration. K3 owns the minimum Relations, Analysis, and OIR
consumer co-design. K4 owns the differentiated real-protocol portfolio.

### Narrow reclosure amendment

A later exactness review preserved the architecture while repairing the Oracle-
answer and guard-Boolean canonical bodies, correcting evidence claims, and
making the stricter all-prior-prover absorption choice explicit. The detailed
rationale and dependency cone live in
[`research-and-selection.md`](research-and-selection.md); final disposition and
gates live only in [`validation.md`](validation.md).

## Fixed intake

**Current:** The authoritative v0 has explicit `public_bind`, complete
challenge dependencies, global Frozen-Heart protection, segment-sensitive
statement ordering, challenge-domain uniqueness, and Last-Challenge reduction
closure. Its execution and implementation are the target's non-regression
source, not a constraint on the new representation.

**Pre-K2 target:** The Stage 3/4A target has the useful factorization
`Protocol = InteractiveCore + ChallengeInterpretation`, but it consumes a
whole supplied `ProverTrace`, treats transcript participation partly as an
authored event choice, has no faithful first-class route for every Statement,
does not derive public-coin eligibility, leaves `SqueezeAndSampleRule`
undefined, and cannot natively express an interactive oracle publication and
later random-access query without encoding it as ordinary messages.

**K1 intake:** K2 uses K1's authenticated regime-qualified content identities,
domain-indexed canonical values, portable bounded algorithms, derived function
types, typed completed failures, and deterministic evaluation controls. K2 may
define PIR-owned types, predicates, and semantic failures, but may not create a
second value, algorithm, identity, or generic outcome foundation.

## Research questions and rival set

K2 compares complete candidates, not isolated patches, for these questions:

1. whether one literal Core can support both Fresh and Fiat--Shamir execution,
   or whether only a checked relation between distinct Cores is honest;
2. whether Statement binding is global-only, dynamically inferred, or owned by
   explicit lexical/composition scopes;
3. whether transcript influence is authored, inferred only by message kind, or
   derived from typed semantic obligations and dependency closure;
4. whether strategies are Core values, external suppliers constrained by a
   Core-owned decision interface, or merely whole traces;
5. whether oracle interaction is encoded as messages, represented by native
   publication/query effects, or placed in a separate IOR subject;
6. whether guards are a fixed canonical decision diagram or K1 portable Boolean
   algorithms over prior values;
7. whether total schedule order is semantic, quotientable, or only a carrier
   choice;
8. whether fixed party cardinality, prover nonproduction, failure precedence,
   and composition context belong in the Core; and
9. which extension mechanism preserves a small closed v0 while refusing unknown
   semantics at the first boundary.

The initial research basis is deliberately narrow: the current authoritative
contract and implementation; the prior target; the CFRG Fiat--Shamir draft;
primary multi-round Fiat--Shamir, IOP/IOR, and round-by-round soundness work;
and protocol-level IR experience that can falsify the chosen abstraction.
K2 does not repeat the broad Stage 1 survey.

## Frozen exit gate

K2 completes only if all of the following are true:

1. one routed durable PIR definition set defines independently implementable formation,
   authentication, admission, execution, replay, Fresh interpretation,
   Fiat--Shamir construction, and checked Fresh/FS relation laws using K1
   mechanisms rather than placeholders;
2. online execution generated through legal actor decisions agrees with replay
   for the honest control, while a replayable trace whose early prover action
   depends on a future challenge fails causal generation;
3. every scoped Statement occurrence is bound before its first dependent
   challenge, and omitted or late binding fails structurally;
4. every required prover or oracle contribution is derived into every dependent
   challenge prefix; a required contribution made wire-only, omitted, duplicated,
   reordered, or conditionally skipped fails structurally;
5. reused challenge namespaces and any verifier-private influence on a
   Fiat--Shamir challenge fail before construction;
6. one exact state transition connects admitted prefix bytes to the next
   transcript state and challenge value or typed failure, including framing,
   domain/occurrence separation, state update, bounded rejection or grinding,
   and deterministic resource behavior;
7. the same admitted Core has successful Fresh and Fiat--Shamir interpretations
   on the Schnorr control, with the construction relation preserving exact
   occurrence coordinates rather than silently remapping behavior;
8. a native immutable-oracle fixture expresses publication, verifier-selected
   query, answer, and checking; malformed lifetime, index, answer, and transcript
   influence cases fail at named first boundaries;
9. the selected guard, schedule, role, failure, composition-context, and
   extension answers have explicit identity and admission effects, bounds,
   rejected rivals, and reversal triggers; and
10. the bounded executable gate, target-document reconciliation, manifest and
    link checks, and one final cold review are green with exact nonclaims.

Each negative has an unchanged positive control at the same boundary. K2 does
not remain open merely to add more examples once these criteria are met; any
remaining protocol-family doubt advances to K4 unless it changes a shared K2
decision.

## Completed records and instrument

- [`research-and-selection.md`](research-and-selection.md) reconstructs the two
  live models, cites the bounded primary sources, compares integrated rivals,
  and records the selected model and reversal conditions.
- [`validation.md`](validation.md) owns the executable contract, cold-audit
  disposition, falsifier matrix, exact run results, limitations, and bounded
  completion verdict.
- [`evaluation/k2-protocol-fiat-shamir/`](../../../../evaluation/k2-protocol-fiat-shamir/)
  is the standalone K1-backed reference instrument. It is evidence, not
  compiler code or authority.

## Known risks and non-claims

**Caution:** A trace checker is not an adversary model. A public value is not
automatically a Statement binding. A transcript flag is not a proof that all
required influence is present. A deterministic hash invocation is not by
itself an adequate Fiat--Shamir construction. Public-coin eligibility is
structural but Fiat--Shamir security remains theorem- and model-relative.

Native oracle effects preserve an IOP/IOR interaction shape; they do not by
themselves define a polynomial commitment, the BCS compiler, Merkle security,
salting, query privacy, or a proof-system theorem. Finite fixtures establish
inhabitance and boundary behavior only, not protocol-family completeness or
cryptographic security.

## Intended durable destinations

Accepted Core, execution, public-coin, transcript, Fiat--Shamir, oracle, and
structural-construction rules go to `pir/`. K1-shared mechanics remain owned by
`foundation/`. Strategy classes and theorem applicability go to `analysis/`;
Statement/Witness correspondence goes to `relations/`; projected effects and
discharges go to `oir/`; implementation support and evidence claims remain in
their own domains.

## Deletion trigger

Delete this package only after K3 has consumed the frozen read interfaces, all
rejected alternatives have durable rationale or reversal triggers, no durable
page depends on this package, and the parent temporary inventory is updated.
K2 completion alone does not require immediate deletion because this package
remains useful optional research provenance during the redesign.
