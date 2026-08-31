# Native FRI/IOR Final Classification and Retention

> **Kind:** Temporary case disposition and absorption record
> **State:** Retained at the assigned executable-falsification depth for one
> bounded two-lane case; the wider protocol portfolio remains active
> **Authority:** None. This record classifies one research case and routes its
> results. It does not establish protocol support, theorem applicability,
> security, implementation conformance, or normative cutover.
> **Source anchor:** Block, Garreta, Katz, Thaler, Tiwari, and Zajac,
> [*Fiat-Shamir Security of FRI and Related
> SNARKs*](https://eprint.iacr.org/2023/1071), revision 7, Section 5.7,
> Algorithm 1.
> **Executable route:** [Native FRI/IOR Semantic
> Validation](../../../../evaluation/native-fri-ior/README.md)
> **Deletion:** Absorb the retained rationale, scope, and evidence routes into
> durable owners, then delete this page with the temporary research package.

## 1. Decision

The case-level primary classification is **`ConservativeExtension`**.

The central factorization survives:

```text
source logical-Oracle Core
        |
        | checked Oracle-commitment construction
        v
committed Core
        +--------------------------+
        |                          |
        v                          v
Fresh Protocol              Fiat--Shamir Protocol
                             over the same committed Core
```

The source and committed Cores are different because the verifier observes
different capabilities and messages. Fresh and Fiat--Shamir remain challenge
interpretations of one unchanged committed Core. What had to be added was
typed structure that preserves those distinctions:

- `InitialOracle` versus `ProverOracle` origin;
- `LogicalAccess` fixation and exact-domain query access without pretending
  that a carrier or commitment value was published;
- one checked, profile-bound Core-to-Core Oracle-commitment construction; and
- one causal, purpose-bound confidential PIR view through which Relations can
  compare the exact initial Oracle material without publishing it or placing a
  secret-derived digest in semantic identity.

Those are additive semantic capabilities. They do not invalidate the existing
Core, Protocol, challenge-interpretation, Relations, or Analysis meanings.
Field, domain, fold, tree, codec, and sampler choices remain profile-local.

## 2. Retained evidence lanes

The case is retained as one combined packet with two explicitly different
controls. Neither is silently renamed into the other.

| Lane | Role | Retained positive scope | Deliberate boundary |
|---|---|---|---|
| Earlier finite control | Exercises native logical access, a commitment/opening compilation, an orthogonal work augmentation, public target replay, negative boundaries, and the same-Core Fresh/Fiat--Shamir split | One order-16, two-fold, degree-less-than-two-terminal implementation-style profile | It is early-terminated and has no exact correspondence to Algorithm 1 or to a paper theorem. Its commitment and work-augmentation results are validation-bound to their recorded finite use. |
| Exact classical control | Pressures the source schedule and the retained construction architecture at exact finite coordinates | Goldilocks field, order-64 initial domain, degree bound 8, three binary folds, scalar terminal, four labelled query draws, and twelve ordered layer checks; frozen public input/proof replay and separately coded verifier | Its source claim stops at fixed-coin deterministic verifier shape. It establishes no randomized experiment, strategy law, theorem premise, security property, or family generalization. |

The earlier control contributes the complete historical executable and replay
packet. The exact control removes its decisive source-shape ambiguity and
provides the three-fold/scalar-terminal structural pressure. The retained case
therefore satisfies its assigned depth through the combined packet, not by
pretending that either lane supplies conclusions it does not carry.

## 3. Exact source-correspondence boundary

The exact classical control corresponds to revision 7 Algorithm 1 only at the
following deterministic structural boundary, after all verifier coins are
fixed:

1. the verifier begins with logical access to `G0`;
2. each of three fold challenges follows fixation of the preceding Oracle;
3. `G1` and `G2` are prover Oracles fixed after their respective challenges;
4. the third fold yields a scalar `C` before query sampling;
5. four labelled initial-domain draws each induce one complete binary-fibre
   check at each of three layers; and
6. the verifier evaluates exactly twelve layer checks: eight fold equations
   and four scalar-terminal comparisons. The retained fixture chooses one
   deterministic query-then-layer evaluation order for replay; the source's
   parallel-query presentation does not impose that execution order.

The following are local zkc profile or compilation choices, not claims about
Algorithm 1:

- the Goldilocks field and exact subgroup generators used by the fixture;
- four repetitions as the selected finite parameter;
- public Statement and application-context coordinates;
- salted SHA-256 pair leaves, tree shape, physical-opening deduplication, and
  proof encoding;
- transcript framing, domain labels, rejection samplers, resource limits, and
  the exact strong-Fiat--Shamir profile; and
- owner-only deterministic material used to regenerate the fixture.

The source correspondence does **not** establish the randomized source
Protocol. In particular, it does not establish uniform or independent coin
laws, a quantified prover strategy or non-anticipation theorem, probability
experiments, commitment binding, the BCS transformation, round-by-round or
state-restoration soundness, theorem applicability, ROM or QROM security, a
proximity conclusion, or an outer computation relation.

## 4. Authority and property boundary

Structural formation and property reasoning remain separate:

```text
PIR
  admitted source Core
      -> checked Oracle-commitment construction
      -> admitted committed Core
      -> checked Fresh/Fiat--Shamir structural relation

Relations
  admitted relation instance + exact binding
      -> causal, purpose-bound confidential initial-Oracle comparison
      -> structural or run-grounded correspondence result

Analysis
  exact Protocol/construction/Relations views + explicit profile
      -> property question
      -> applicability or property result only when every premise is supplied
```

The first two lanes may establish exact structural facts and one finite
material agreement. They cannot establish a cryptographic property. The exact
FRI questions remain candidate or unsupported until Analysis owns and admits
an explicit experiment/theorem profile with the required strategy class, coin
law, source validation, theorem truth, construction assumptions, and resource
coordinates. No property result is inferred from a green execution or an
affirmative Relations check.

## 5. Gate disposition

| Gate | Final bounded disposition | Basis and limit |
|---|---|---|
| Source fidelity | Closed | Pinned revision and locator; the exact lane maps the three-fold/scalar-terminal/four-draw/twelve-check deterministic shape and labels every local strengthening or convention. |
| Design-space coverage | Closed | Full disclosure, one universal Core, opaque-module, distinct-Core construction, and broader-skeleton alternatives were compared; the distinct-Core construction was selected. |
| Semantic closure | Closed | Origin, logical access, exact domain, construction maps, advice ownership, identities, qualified failures, bounds, and confidential disclosure authority have named owners. |
| Protocol closure | Closed | Initial and folded Oracles, challenges, scalar terminal, ordered queries, openings, authentication, fold checks, and public outcomes are distinct typed coordinates. |
| Construction closure | Closed at the structural profile boundary | Admission rederives the target Core and total maps before issuing process-local authority. The inert run receipt proves only its named execution. |
| Relations closure | Closed at the exact material-agreement boundary | The public Instance contains only its Interface and public values; the static Binding owns Protocol and Oracle coordinates; the occurrence-specific question and live authorities own run grounding. The relation-side carrier is compared with the causally used initial Oracle without a trace, public selector, or secret-derived ID substituting for that comparison. |
| Analysis closure | Closed by explicit non-answer | Exact questions can be routed, but no active owner profile supplies the experiment, theorem, or premise authority required for an affirmative property result. |
| Executable pressure | Closed for the retained finite packet | The two frozen lanes retain positive paths, named negatives, bounded regeneration, and public replay. This is finite falsification evidence only. |
| Independent reconstruction | Closed at implementation-diversity strength | A separately coded public verifier reconstructs the exact committed execution from frozen public inputs and proof; it shares the published semantic contract and is not independent semantic authority. |
| Regression | Closed at the final checkpoint | The package passed 456 tests; public replay and twice-derived fixture checks passed; Ruff, `git diff --check`, the public-tree guard, and document-link/manifest audits passed. |
| Convergence | Closed for this case | Every accepted change has one owner; incompatible meanings were not merged; remaining variant and property questions are explicitly routed. |
| Absorption | Closed by this checkpoint's owner updates | PIR owns Core and construction semantics; Relations owns correspondence; Analysis retains a typed unsupported boundary; project pages own the architecture map; Evidence indexes the bounded executable route. |

The recorded checkpoint is finite regression evidence, not a theorem or a
general conformance result. A later failed gate reopens the exact affected row
and retains the failed snapshot; it does not weaken the gate wording.

## 6. Retention and portfolio handoff

Retain this case at its assigned executable-falsification depth with primary
classification `ConservativeExtension`. This closes only the portfolio's first
deep Oracle/IOR anchor. It does not close the wider portfolio, cross-family
Oracle/composition design, or independent semantic freeze.

The next protocol cases remain selected at their existing differentiated
depths. In particular, batched FRI, DEEP-FRI, verifier-derived Oracle views in
DEEP-ALI and STIR, Circle FRI, WHIR, literal BCS correspondence, polynomial
commitments, Sumcheck/GKR, complete argument systems, folding, recursion, and
holdouts remain separate work. Reusing the exact classical control as proof of
those cases is forbidden.

## 7. Reopening conditions

Reopen only the smallest affected owner if any of the following occurs:

- a primary-source recheck shows that the claimed Algorithm 1 order, fold
  count, scalar terminal, draw multiplicity, or fibre check is wrong;
- the frozen exact public replay cannot be regenerated from the selected
  public and owner inputs under its pinned profiles;
- the checked construction cannot preserve total occurrence, value, check,
  outcome, and public-environment maps without changing source or target Core
  meaning;
- logical access requires public disclosure, a dummy binding value, ambient
  host state, or strategy authorship of the initial Oracle;
- causal confidential grounding can be reproduced from replay, a raw trace,
  a portable secret-derived identifier, or a copied/equal capability;
- the Relations material-agreement result leaks either carrier or treats
  missing authority as semantic disagreement;
- an Analysis path can answer a FRI property question without an explicit
  profile and complete premise authority; or
- a materially different protocol shows that the retained factorization
  requires an opaque escape or a contradictory ownership rule.

Do not reopen merely because source and committed Cores have different
identities, because structural and property results use different owners, or
because later protocol families need additive profiles.
