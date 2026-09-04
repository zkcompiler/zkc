# Architecture Selection

> **Kind:** Temporary comparative architecture decision
> **State:** Selected for durable promotion
> **Authority:** None. The selected model has target status only after its
> definitions are incorporated into their durable owners.

## 1. Decision

Select a shared **verifier-side commitment-opening vocabulary** and retain
family-specific constructions around it.

```text
                     exact admitted InteractiveCore
                                  |
                                  v
          CommitmentOpeningVerifierProfile + exact Core use
             /                    |                    \
            /                     |                     \
 Oracle authentication    KZG native opening     KZG aggregation
 source Core -> target     single or original     separately checked
 Core construction        multipoint group       interaction shapes
```

The shared profile fixes:

- exact public-parameter roles and types;
- public commitment, query, asserted-answer, and evidence types;
- an exact ordered claim-group law;
- an exact bounded verification algorithm;
- intrinsic bounds and typed failures; and
- identity and public replay rules.

It does not contain a concrete setup value, private committed material,
commitment or prover algorithms, private state, advice, a security property,
or a universal batching operation.

The exact public setup is selected from `PublicParameter` bindings in a
`CoreInvocation`. The profile schema is static identity; the runtime SRS or
transparent parameter value belongs to the invocation-issued public setup
view. A hard-coded setup may instead be an intentional Core constant, in which
case changing it rotates `CoreId`.

## 2. Why verifier-side is the correct shared boundary

PIR owns what the verifier observes and computes. Honest commitment and proof
generation belong to a `ProverPlan` or to a construction-specific producer
adapter. Relations owns the equation between private material and a published
commitment. Analysis owns binding, hiding, extraction, correctness, and setup
assumptions.

Putting `Commit`, `Open`, or a private polynomial into the common verifier
profile would create a second owner for Plan and Relations meaning. It would
also rotate verifier semantics when only a prover implementation changes.

The common runtime claim is therefore:

```text
OpeningClaim = {
  public_commitment,
  query,
  asserted_answer
}

VerifyOpeningGroup(
  exact public setup assignment,
  exact verification context,
  exact ordered nonempty OpeningClaim sequence,
  public evidence)
    -> Boolean
```

The answer and evidence are distinct roles. They may be projections of one
wire message, but one cannot be inferred from the other merely because the
message codec co-locates them.

## 3. Candidate comparison

| Candidate | Source fidelity | Ownership | Evolution | Decision |
|---|---:|---:|---:|---|
| Keep the current Oracle-only ABI | Fails KZG and V02 claim/evidence timing | Clear but specialized | Local | Rejected as universal; retained as an authentication construction after repair |
| One opaque `Setup/Commit/Open/Verify/Batch` PCS object | Superficially broad | Blurs Core, Plan, Relations, and Analysis | Easy to extend opaquely | Rejected |
| One generic queryable-object Core extension now | Could model polynomials | Prematurely merges finite Oracles, polynomials, and private producer material | Large new surface | Deferred; neither selected case requires it for verifier semantics |
| Completely separate Merkle, binary PCS, and KZG towers | Exact | Clear | Duplicates identity, setup, and replay machinery | Rejected |
| Shared verifier profile plus family-local constructions | Exact | Preserves current owners | Adds independent profiles without rotating siblings | Selected |

### 3.1 Why no generic queryable object is selected now

KZG's verifier does not query a private polynomial object. It reads a public
commitment, explicit evaluation claim, proof evidence, and SRS. The private
polynomial belongs to Plan/Relations. Introducing a generic functional object
into Core solely to model honest KZG generation would move private producer
semantics into the verifier subject.

The binary-field case already uses exact finite logical Oracles. Its virtual
word can be represented query-by-query by two ordinary Oracle answers plus a
`DerivedValueDecl` consuming `alpha`. No carrier, publication, commitment, or
new Oracle authority is needed. Positive folded words remain ordinary
`ProverOracle`s.

Reserve a narrow `DerivedOracleView` question only if a future complete
witness proves that query-by-query derivation cannot preserve a source's
schedule or access law. Do not preselect it here.

## 4. Shared verifier profile

The selected durable subject has the following conceptual body:

```text
CommitmentOpeningVerifierProfile = {
  profile_name,
  profile_version,

  setup_roles: ordered sequence of {
    role_ordinal,
    value_type
  },

  public_commitment_type,
  query_type,
  asserted_answer_type,
  verification_context_type,
  opening_evidence_type,

  exact_claim_count,
  claim_group_law,
  verify_opening_group,
  intrinsic_bounds,
  exact_failure_catalog
}
```

`claim_group_law` and `verify_opening_group` are exact authenticated, total,
deterministic, bounded algorithms. A caller does not supply a success bit.
The use checker independently evaluates both over exact runtime values.

An exact Core use maps every setup role once to a `PublicParameter`, names the
ordered commitment/query/answer `ValueRef`s, optional verification-context
values, evidence `ValueRef`, and exact `CheckRef`. It checks that the Core's
predicate is the profile verifier over precisely those inputs. Missing,
duplicated, reordered, or extra values refuse.

This profile permits one evidence value to cover several distinct claims, but
does not call that fact batching or infer any property from it.

## 5. Oracle-authentication repair

Keep the existing Oracle source/target construction and its authority shell.
Revise each commitment class to reference one exact verifier profile and setup
role map. Construction-local producer algorithms remain responsible for:

- encoding the complete source carrier;
- building private commitment state;
- deriving the public commitment;
- producing an opening response from exact selected claims; and
- projecting any intentionally public construction advice.

Every algorithm that needs public parameters receives the exact setup
assignment explicitly. No ambient registry, hard-coded runtime SRS, or private
advice substitute is allowed.

Replace the universal shape

```text
public opening -> extract answer -> verify
```

with

```text
opening response -> decode asserted answer and evidence
                 -> verify(setup, exact claims, evidence)
```

and replace `PhysicalOpeningBindingLaw` with a construction-owned
`OpeningEvidenceCoverageLaw`:

```text
OpeningClaimCoordinate = {
  source_answer,
  public_commitment_coordinate,
  query_value_ref,
  asserted_answer_value_ref
}

OpeningEvidenceGroup = {
  verifier_profile_id,
  ordered_claim_coordinates,
  evidence_slot,
  verification_check
}
```

The run checker derives coverage from the source and target records and
requires every logical claim, selected evidence slot, and selected check
exactly once. The current equal-key Merkle deduplication becomes one profile-
local coverage algorithm. It no longer defines all commitment openings.

This change does not turn Oracle authentication into KZG claim aggregation.
The source Core's challenges, claims, reductions, messages, and terminals are
preserved. The construction inserts only commitment and authentication
effects.

## 6. Binary-field inhabitance

The completed source Core has:

```text
f publication
f_prime publication
s_prime prover message
alpha challenge
interleaved Sumcheck messages, checks, and shared fold challenges
positive folded-Oracle publications
degree-one terminal message and check
paired queries to f and f_prime for every virtual-initial-word access
derived answer alpha * f(x) + f_prime(x)
```

Its BCS target maps ordinary source Oracle publications and answers to a
salted Merkle verifier profile. It must preserve:

- all logical query multiplicity even when physical evidence is shared;
- separate commit-padding, evaluation-mask, and leaf-salt advice roles;
- the single evaluation-session/query budget in the exact subject;
- positive folded Oracles as actual publications; and
- absence of any commitment or receipt for the virtual initial word.

An unsalted target may be structurally executable, but it is a different
profile and cannot satisfy the paper's zero-knowledge BCS applicability
question by substitution.

## 7. KZG profiles and constructions

### 7.1 Single opening

One exact KZG verifier profile uses:

```text
setup roles: exact SRS capabilities
claim group: one (C,z,y)
context: empty
evidence: W
check: the exact Type-3 pairing predicate
```

The Core may receive `z` as a Statement value or as an enclosing verifier
challenge. The profile does not prescribe its origin; the exact Core use does.
Its theorem question must bind that origin and challenge interpretation.

### 7.2 Original multipoint opening

A sibling verifier profile uses:

```text
claim group: one common C and distinct points z_i with y_i
context: empty
evidence: remainder polynomial r and witness W_B
setup: includes sufficient G2 multipoint capacity
```

Its group law checks one common commitment, distinct points, exact remainder
degree bound, and `r(z_i)=y_i`. It introduces no batching challenge.

### 7.3 Same-point linear-combination proof aggregation

This is a separately checked Core interaction shape, not a rewrite receipt for
completed single-opening proofs:

```text
ordered (C_i,z,y_i) claims
        |
        v
batching challenge v
        |
        v
one aggregate proof W
        |
        v
one exact aggregate pairing check
```

Its identity binds the ordered member coordinates, common-point law,
coefficient rule `1,v,...,v^(m-1)`, challenge declaration and domain, evidence
position, verifier profile, and bounds. The runtime challenge value is not
identity. The checked result establishes only exact structural use of that
profile, not equivalence to individual openings or special soundness.

### 7.4 Independent-proof verification aggregation

This distinct construction preserves every `(C_i,z_i,y_i,W_i)` tuple, derives
its coefficient only after all tuples are fixed, and replaces several pairing
computations with one aggregate check.

Its identity binds the complete tuple order, coefficient derivation or Fresh
challenge rule, domain separator and framing when Fiat--Shamir is used, and
aggregate equation. It does not claim proof compression or claim reduction.

### 7.5 Forbidden universal name

There is no `BatchOpeningConstruction`. The original multipoint profile,
same-point claim aggregation, independent-equation verification aggregation,
and Merkle evidence packing remain separately named and admitted.

## 8. Identity locality

| Change | Must rotate | Must not automatically rotate |
|---|---|---|
| verifier algorithm, setup schema, type, group law, or bound | verifier-profile ID and exact uses | unrelated sibling profiles |
| runtime SRS value | Core invocation and public-setup view | generic profile or Core, unless setup is a Core constant |
| commitment/opening producer algorithm | Plan or Oracle-construction identity | standalone verifier profile |
| Merkle layout or salt policy | Oracle commitment profile/construction | source logical Core |
| actual salts, blinds, or masks | run/advice occurrence | static construction identity |
| KZG member order, challenge rule, or coefficient law | exact aggregation construction and target Core | KZG primitive profile |
| theorem source, premise, or security model | Analysis identity | PIR identities |
| evaluator limits or observations | validation/evidence basis | semantic receipt identity |

The exact SRS value may receive a content identity through its canonical public
value and setup view. That fact says nothing about ceremony trust.

## 9. Failure boundaries

| Condition | Boundary |
|---|---|
| malformed field/group/proof encoding | typed ABI rejection |
| missing, extra, or wrong-class setup role | use/construction refusal |
| unsupported curve, SRS capability, degree, or multipoint capacity | `Unsupported` or structural Negative, as declared |
| missing, duplicated, or reordered claim coverage | structural Negative |
| evidence substituted for an asserted answer | structural Negative |
| false pairing or authentication predicate | Core check is false; accepting terminal is unavailable |
| batching challenge before all required claims or proofs | Core/construction admission failure |
| invented commitment for the V02 virtual word | exact-target or source-map mismatch |
| absent setup ceremony evidence or theorem premise | Analysis `CannotAnswer`; execution may remain well formed |

Construction failure while producing a quotient or proof is not verifier
rejection. It belongs to Plan/construction execution. A successful check is not
binding, extraction, or material correspondence.

## 10. Negative pressure set

The selected architecture must reject or keep unproved:

- ambient or private-advice setup substitution;
- runtime SRS embedded in generic profile identity;
- `y` extracted from KZG proof `W`;
- swapped commitments without swapped answers;
- changed member order under an unchanged construction identity;
- same-point aggregation with unequal points;
- challenge derived before the last required claim;
- final equation coefficient derived before all individual proofs;
- original multipoint opening under an SRS lacking its G2 capacity;
- duplicate points or `deg(r) >= |B|` in the multipoint profile;
- unequal Merkle claims sharing a slot under an equality-dedup profile;
- Merkle evidence packing cited as an algebraic reduction;
- an unsalted BCS target cited for the source's zero-knowledge claim;
- repeated binary-field evaluation sessions outside the selected budget; and
- any receipt promoted into a cryptographic theorem.

## 11. Reversal conditions

Reopen this selection if a source-faithful case demonstrates that:

1. verifier semantics cannot be specified without placing honest private
   producer material in the common profile;
2. one exact setup assignment cannot cover transparent and SRS-backed
   verifier inputs without ambient authority;
3. claim/evidence separation changes a source transcript rather than merely
   typing it;
4. V02 cannot preserve its virtual query schedule using ordinary paired Oracle
   queries and derived values;
5. a required construction cannot classify every target coordinate without a
   generic queryable-object extension; or
6. public replay necessarily needs a setup trapdoor or unopened private
   polynomial.

Migration cost, an existing pass shape, or a preference for one `batch` API is
not reversal evidence.
