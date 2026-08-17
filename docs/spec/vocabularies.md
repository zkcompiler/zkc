# zkc Vocabularies

Status: **canonical for ProtocolVocabulary v4 and the current PIR/OIR
surface (2026-07-29).** Companion to
`kernel.md`: every extensible vocabulary the kernel quarantines lives
here, with its admission rules. This document may add newly admitted entries
or reserve future names; it does not weaken the kernel judgments.

This document is canonical for the PIR vocabulary. There is no
theorem-row vocabulary: rules and their bindings are authored natively in the
Soundness Kernel signature (`soundness.md`), with no adapter and no dual path.

Vocabulary entries and extension names governed directly by this document use
one of two semantic admission states. The Soundness signature's separate
`admitted | declared` rule status is defined in §10.

```text
admitted  part of the closed current vocabulary and legal only when all
          applicable admission conditions hold
reserved  name or role allocated for a future version; it has no accepted
          current representation and must fail closed
```

## 1. Admission discipline (applies to every vocabulary)

1. Entries are content-addressed; unknown entries fail closed everywhere.
2. An entry MUST declare its identity impact: identity-bearing or
   evidence-only. Misclassification is a spec bug (kernel §2 test: if
   changing it alters transcript bytes, proof ABI, challenge
   authority, claim flow, or decision, it is identity-bearing).
3. An entry MUST NOT alter kernel judgments. A candidate that needs
   WF, LIN, BIND, COV_obl, ReductionClosureOK, or TerminalClosureOK to change is
   a kernel change, not a vocabulary entry.
4. An entry is either admitted whole under the extension admission contract
   below or remains reserved. There is no partially admitted state.
5. The breaking-change boundary is **semantic load**: adding a field, an
   entry, or a value carries no semantic load only if its absence carries
   no meaning; anything whose presence conditions the interpretation of
   an existing judgment, bound, status, or dependency edge changes what
   the corpus means, and so does removing or redefining an admitted entry.
   At v0 such a change is made in place — no identifier is minted to carry
   the old reading, and no reader negotiates between the two
   (`versioning.md`). What the change is required to do is move every
   content digest that depended on it, which it does by construction:
   an entry's identity is its content.

**Extension admission contract.** A new entry crosses the seal
boundary only when it arrives whole: concrete syntax in the carrier,
a stated denotation against the kernel judgment it feeds, a canonical
encoding (identity-bearing entries; kernel §8), fail-closed
validation requirements at every loader and judge that consumes it, and a
statement of its semantic load under rule 5 above. Partial admission is refusal: an
entry missing any leg does not enter. No residual authoring operation survives
past seal: whatever mints, edits, or completes an entry acts before the seal
judgment; a sealed artifact's vocabulary is closed content, never a work
surface.

## 2. Event subkinds

Kernel classes (§1.1 of kernel.md) are fixed; subkinds refine them:

| Subkind | Kernel class | State |
|---|---|---|
| meta (context binding) | public_bind | admitted |
| slot (prover message) | slot | admitted |
| slot.unabsorbed | slot, e ∉ A | admitted |
| chal (fresh challenge) | challenge | admitted |
| chal.project / chal.derive | challenge (pure origins) | reserved |
| check | check | admitted |
| commit / open | object events | reserved |
| artifact_import / artifact_verify | object / artifact_verify | reserved |
| public_release | public_bind | reserved |
| index (preprocessed-index binding) | public_bind | reserved |
| decision | decision | admitted |

Slot shape/multiplicity (scalar vs vector, per-query vs batched) is a
descriptor fact of the slot, carrier-canonicalized; it MUST be
declared because it is proof-ABI identity.

## 3. ProtocolVocabulary and claim profiles

The protocol-semantic vocabulary is one cross-admitted envelope,
`zkc.protocol_vocabulary`, containing `predicate_specs`,
`claim_profiles`, `check_contracts`, `hole_contracts`,
`reduction_contracts`, and `terminal_rules`. These sections are
not independently loadable authorities: admission succeeds only after all
cross-references and content pins resolve together. The sealed artifact carries
exactly the transitive cited subset in its flat `vocab.claim_profiles`,
`vocab.check_contracts`, `vocab.reduction_contracts`, and
`vocab.terminal_rules` sections, plus `vocab.hole_contracts` exactly when
construction routes cite at least one hole. Those sections are the sole digest
authority for these entries (kernel §8; carrier §6–7). Predicate-spec
preimages are re-admitted transitively through pinned CheckContracts rather
than duplicated into the artifact.

A `ClaimDescriptorProfile` is:

```text
id -> { kind, anchors: [ordered, unique names] }
```

The carrier type selects the id; the profile supplies the coarse kind and exact
anchor schema. An instance with a missing or extra anchor refuses. Profile
content is digested under the exact ASCII prefix
`"zkc/claim-profile\n"`; a claim descriptor is `(profile id, canonical
anchor dictionary)` and its position-free digest uses
`"zkc/claim\n"`.

The admitted closed set is deliberately small:

| Profile id | Coarse kind | Exact ordered anchors |
|---|---|---|
| `opaque_relation` | relation | `contract`, `statement` |
| `single_opening` | opening | `commitment`, `point`, `value` |
| `batch_opening` | opening | `members`, `point` |
| `opening_value_rlc` | opening | `coefficient`, `members` |
| `kzg_verification_equation` | verification equation | `material` |
| `kzg_equation_rlc` | verification equation | `coefficient`, `members` |
| `mle_evaluation` | evaluation | `oracle`, `point`, `value` |
| `sumcheck_evaluation` | evaluation | `statement` |
| `schnorr_evaluation` | evaluation | `statement` |
| `dleq_evaluation` | evaluation | `statement` |
| `or_evaluation` | evaluation | `statement` |
| `fri_query_consistent` | evaluation | `statement` |
| `r1cs` | relation | `a`, `b`, `c`, `public` |
| `r1cs_batched_sum` | evaluation | `statement` |

The evaluation profiles are split per producing family, and joint admission
refuses a reduction contract whose output profile is anchorless: an anchorless
profile is one constant descriptor in every artifact, so with descriptors as
the claim graph's objects it composes with every consumer at the link
boundary. A produced claim descriptor must say what it is about. Anchorless
*source* profiles stay legal — an entry claim's anchors are declared by its
author — and two contracts producing one anchored profile is ordinary
authoring, deliberately admitted (a producer-count clause would go vacuous
after this split and refuse the second arithmetization contract the relation
programme wants).

`opaque_relation` is a generic profile retained for compatibility. Its two
values are uninterpreted claim-identity bytes; neither value
resolves to a `RelationContract`, relation instance, or application statement.
`r1cs` has matrix and public-input anchors that are likewise opaque. The
vocabulary specifies their identity and role in the arithmetization claim
chain; it does not read either relation payload or establish source-compiler
correctness.

The single-opening value anchor prevents proving a different evaluation at the
same commitment and point. For full input descriptors encoded as `[profile,
anchors]`, let `D` be their array sorted by canonical descriptor bytes. The
batch operation rejects duplicate descriptor bytes, permutes commitments,
values, and coefficients with those whole records, and sets
`members = SHA256("zkc/claim-vector\n" || canonical(D))`. A new profile is
additive only when existing constructors and judgments already express it.
Scope, free parameters, required interfaces, or a wildcard profile are absent;
adding any is a versioned format decision.

## 4. Transformer vocabulary

- **Source kinds**: neutral claim instantiation through `pir.instantiate` is
  admitted; protocol-object introduction and artifact import are reserved. A
  source carries a profile and exact anchors, not relation denotation.
  Relation-specific meaning must not be inferred from an authoring label or
  source spelling.
- **Sink kinds** remain fixed by the kernel at four. `discharge` is accepted
  only through a check-backed `TerminalRule`; `artifact_verify` and
  theorem-backed terminal variants are reserved and therefore refuse in the canonical encoding.
  Export/assume/residual continue to cite route refs admitted by policy.
- **Reduction contracts** use digest prefix
  `"zkc/reduction-contract\n"` and are the sole authority for both protocol
  shape and exact local transition. Their closed fields are `version`,
  `consumes`, `dep_slots`, `rounds`, `parameters`, `checks`, `constraints`, and
  positional `outputs`; there is no parallel `produces` or shape registry.
  `rounds` is non-empty: a contract with no interaction rounds states no
  local transition to judge or price, and admission refuses it. A
  consume entry is one exact profile id, except that a contract may have one
  and only one variadic `{profile, min}` entry with positive `min`. Each output
  fixes one exact profile and the exact expression for every required anchor.
  The current contract format requires exactly one output. A derivation site
  names one output position, so admitting several would let each conclusion
  inherit the whole reduction error while leaving the other direction
  unconstrained; supporting several outputs requires a subject over the whole
  produced claim vector rather than silently weakening this rule.
  The digest transitively covers referenced claim-profile and body-check
  contract digests. A contract declares no security theorem: the reduction
  names no theorem; a rule binding anchors on it from the signature side, at an
  exact `{id,digest}` contract pin.
  This protocol-local `ReductionContract` is unrelated to the
  relation-domain `RelationContract` (`relations.md`): the former states one
  verifier reduction implication, while the latter states how an imported
  relation's ABI is read, as a post-seal, content-addressed document.
  Instance parameters have the closed sorts `atom`, `material_ref`, and
  `material_ref_vector`; the instance dictionary is exact. Constraints are
  same-sort expression equalities, and output constructors are the sole
  produced-profile authority. Authored `out_anchors` remain explicit carrier
  assertions and must equal the constructors byte-for-byte.
- **Dependency provenance and round challenge use.** A dependency slot is
  exactly `{role, source, class}`. `source` is the closed constraint `any |
  public_bind | prover_slot | challenge_capability`; the latter three require
  the dependency SSA value to be the exact result owned by that producer
  capability. `class` is the semantic payload class and must match the carried
  value. The retired producer pseudo-class `chal` is not a semantic class and
  refuses in both dependency and check-operand declarations.

  Provenance is deliberately orthogonal to theorem pricing. A contract
  realizing a per-round transcript shape assigns messages and one explicit
  `challenge_use` to each round:

  ```text
  challenge_use = {role}             // scalar, exactly one draw
                | {role, count: N}   // vector, 2 <= N <= 2^20
  ```

  The role must name a dependency slot, but that slot need not use source
  `challenge_capability`: `source:any` is legal and the round-use judgment
  independently requires the realized value to be the exact challenge-
  capability result. Conversely, a challenge-capability dependency that no
  round names is ordinary carried data and is not priced. Explicit `count:1`
  refuses because omission is the sole scalar spelling. A challenge use may
  head only one round, one capability may fill only one priced use, and a
  priced capability is owned by only one reduction. Future shared-use laws
  require an explicit versioned contract relation and theorem treatment; v4
  has no implicit reuse escape hatch.

  This view supplies the rounds to which k_i/|C_i|/ε_i attach and **generates**
  `P_req` for each priced use (kernel §5.2). A round MAY carry a kind label
  (`fold`, `query`); when all rounds are kinded, a rule's contract-round cases
  match by exact kind (`soundness.md` §5.1). A contract that omits its own
  round messages from generated requirements refuses at admission. Reduction
  closure and the Soundness Kernel's sealed-artifact projection each
  reconstruct source, exact challenge result, multiplicity, order, prefix, and
  ownership from the sealed artifact and the digest-covered contract.
- **Contract-owned checks and material expressions.** `checks` is an exact map
  from reduction role to `{contract, parameters, transparent_predicate?,
  attachments}`. The selected carrier check must match every field; missing,
  extra, ambiguous, or unrelated reuse refuses. One reduction and the terminal
  rule for its exact contract/output may select the same event because the two
  judgments independently establish the same producer proposition; no other
  cross-owner reuse is legal. Attachments use the fixed kinds
  `semantic_parameter`, `material_ref_equality`, `value_identity`,
  `material_ref_vector_equality`, and `common_material_ref_equality`.
  `value_identity` compares a dependency/message SSA value directly; material
  relations consume explicit `MaterialBinding` edges.

  Constraints, attachment sources, and output anchors use the closed
  many-sorted `MaterialExpr` algebra:

  ```text
  Ref    = literal_ref | input_anchor | dependency | message |
           parameter_ref | construct
  Refs   = input_anchors(order) | messages | parameter_refs | list
  Claim  = input_descriptor
  Claims = input_descriptors(order)
  Atom   = parameter_atom | literal
  order  = operand | canonical_unique
  ```

  `construct(tag,args)` is exactly
  `SHA256("zkc/material-expr\n" || canonical(["construct", tag,
  typed_evaluated_args]))`. Trees are bounded and statically sorted. There is
  no arithmetic, branch, loop, carrier position, protocol-name switch, or
  callback into foreign code. This closed free algebra is what makes new
  protocol contracts additive data rather than executable registry plugins.
- **Terminal rules** use digest prefix `"zkc/terminal-rule\n"`. The sole minted
  variant is check-backed and contains:

  ```text
  claim_profile: ClaimDescriptorProfile id
  producer: absent | {contract: ReductionContract id, output: index}
  checks: terminal_role -> CheckContract id
  attachments: [closed TerminalAttachment]
  transparent_predicates: terminal_role -> normalized predicate
  ```

  Contract references are content-pinned through the sealed protocol table;
  rule admission resolves them jointly. The terminal-rule digest transitively
  covers the consumed-profile, selected-contract, and optional producer-contract
  digests. The rule must cover every consumed claim anchor at least once and
  every selected check semantic argument exactly once, may target each operand
  role at most once, and must define one predicate for every transparent role.
  Reusing an anchor across distinct required targets is permitted; repeating a
  target or a byte-identical attachment is not. The attachment list is
  nonempty, and discharge-time role selection is exact and injective. The
  fixed PIR attachment-source spellings are `claim_anchor`,
  `producer_input_anchor`, `producer_inputs_anchor`,
  `producer_input_descriptors`, `producer_dependency`, and
  `producer_message`. The fixed attachment kinds are `semantic_parameter`,
  `material_ref_equality`, `value_identity`,
  `material_ref_vector_equality`, `common_material_ref_equality`, and
  `descriptor_digest`. The last uses the exact claim-vector helper of §3.
  Check and predicate maps are key-sorted and attachments are sorted by their
  canonical bytes before the rule digest is minted. Unknown constructors or
  ambiguous matches refuse; adding a constructor changes the
  protocol-vocabulary major.
- **Material binding is kernel carrier, not open vocabulary.** PIR has exactly
  `MaterialBinding(ValueRef, MaterialRef)` with the partial-function,
  reverse-injectivity, and exact-consumption rules of kernel §1.6/§4.1–§4.2. A
  future `MaterialAlias` would be a new checked edge with its own semantics and
  evidence; no alias id or free equivalence-class token is reserved now.
- **Reduction families.** The version-4 vocabulary admits the exact
  contracts `sigma`, `sigma_dleq`, `sigma_or`, `sumcheck`, `evalopen`,
  `kzg_batch`, `opening_value_rlc`, `kzg_equation_rlc`,
  `gkr_width2_addmul_layer`, `fri`, `grinding`, `r1cs_batch`, and
  `r1cs_sumcheck`. Broader GKR, WHIR,
  PLONK-permutation, lookup/logup, folding, recursion, and aggregation families
  are reserved. A family name is never matcher authority: each distinct
  local implication enters as an exact reduction contract.
- **Body policies**: `explicit_region` is admitted;
  `deterministic_expansion(contract_hash, params)` is reserved. Opaque recipes
  are not a body policy (kernel COV_obl).
- **Event route classes** (reserved): the non-`executable` projection
  route classes of kernel §6.1 — `fused_executable |
  conformance_row | residual | assumption | export | analysis_only` —
  with their per-class declaration requirements (fused: the covered
  event set plus a cited fusion rule; conformance_row: evidence refs;
  residual/assumption/export: route refs admitted by the SealPolicy;
  analysis_only: analysis policy only). PIR has no representation for
  these declarations: fail-closed absence means `executable`. Admitting them
  requires a versioned carrier and encoding extension. The PIR fusion-rule
  vocabulary is empty, so the fusion set is empty and `src` arrays stay
  single-position.

## 5. Check and hole contracts

`CheckContract` replaces the arity-only check-kind row and is digested under
the exact ASCII prefix `"zkc/check-contract\n"`:

```text
id -> {
  mode: opaque | transparent,
  predicate:
    {format: zkc-transparent-expression-v1}
    | {format: zkc-opaque-predicate-spec-v1,
       content_digest: sha256:...,
       entrypoint: printable-ascii-name},
  parameters: [sorted unique names],
  semantic_parameters: [sorted unique names],
  operands: [
    {role, class,
     multiplicity: exact(n) | capture(name, min)
                              | same_as(name)}
  ]
}
```

The vocabulary map key is a human-readable lookup and diagnostic handle, not
semantic or dispatch authority. The exact CheckContract content digest binds
the predicate descriptor and structural ABI and is the authority projected to
OIR; there is no second carrier-kind namespace. Neither id nor digest identifies
or attests a concrete executable adapter. Parameter, semantic-parameter, and operand-role names
are mutually disjoint. `exact(n)` and `capture(name,min)` require positive
counts; at most one independent capture may occur, and `same_as(name)` may
refer only to that earlier capture. The check instance's `params` and
`semantic_args` key sets are exact, not open dictionaries. These restrictions
give at most one segmentation; seal rejects an instance with no solution. A
transparent contract requires an expression and permits terminal use only
where the rule contains the matching normalized predicate. Its descriptor
commits to that binding mechanism, while the normalized expression itself is
instance/rule content. An opaque contract resolves one entrypoint from the
closed `predicate_specs` map and must expose every semantic argument and
verifier-visible operand needed for attachment and COV.

An opaque predicate spec is keyed only by
`SHA256("zkc/check-predicate-spec\n" || canonical(body))`; aliases and mutable
names are absent. Its body is closed `zkc-check-predicate-spec-v1` content with
`version: 1`, a title, optional references, and an entrypoint map. Each
entrypoint carries normative acceptance text — a non-empty, duplicate-free
clause list — plus the same structural
`parameters`, `semantic_parameters`, and operand-segment algebra as
CheckContract. The loader re-derives every key, requires the map to equal the
exact transitive closure cited by opaque contracts, resolves each entrypoint,
and compares the two ABIs structurally. Missing, extra, renamed, malformed, or
ABI-divergent preimages refuse.

Acceptance text distinguishes an unsupported environment or suite from a
decoded false predicate: unsupported means the admitted proposition is not
defined for that input domain, while false or decode failure is verifier
rejection. This content specifies the proposition; it does not prove that a
particular adapter executes it correctly. Adapter execution and conformance
remain a separate implementation-assurance facet. OIR projection carries the
contract id for diagnostics and its exact digest for dispatch authority;
protocol-family names never branch the matcher. The loader re-admits the exact
cited predicate closure before semantic closure is judged; nothing downstream
re-carries it.

### 5.1 Hole contracts

ProtocolVocabulary v4 adds the required `hole_contracts` source section.
`HoleContract` is the prover-side counterpart to a CheckContract and is
digested under `"zkc/hole-contract\n"`. Its closed content declares:

```text
kind                 commit | extend | evaluate | fold | open | pow_search
operands             typed scalar/vector value and handle segments,
                     anchored material, and for pow_search a sponge snapshot
results              typed value and handle segments; at least one
parameters           sorted typed static parameters
semantic_parameters  sorted digest-shaped semantic parameters
```

The typed signature is authority; `kind` is classification for diagnostics and
coverage. `contract_digest` is the sole `hole_call` dispatch authority. Hole
contracts have no hidden protocol effects: they do not absorb, squeeze, read or
write the wire, bind publics, or verify artifacts. Only `pow_search` may receive
and return one state-identical sponge value as a read-only peek.

Construction routes cite HoleContracts before seal and stamp cited content into
`vocab.hole_contracts`. Artifact admission re-resolves that exact cited closure
against one immutable protocol environment; prover projection consumes the
admitted contract schemas when it emits typed hole calls. The registry entry
does not identify a hole supplier or establish the supplier's internal algebra.
Every operand/result segment count and parameter binding is part of the
admitted ABI and is checked at the corresponding seal, admission, projection,
or execution boundary. For `pow_search`, the contract additionally pins the
nonce framing and following squeeze derivation, and requires the least valid
witness under the declared canonical search order.

## 6. Protocol object families and state alphabets

The object-family names are SubjectRef, Commitment, Oracle, VirtualOracle,
EvaluationPoint, Opening, AccumulatorObject, RecursiveArtifact, ChallengeCap,
ProofSlot, PublicBinding, and PublicRelease. Commitment and ProofSlot are
admitted in PIR flat form; the other names remain reserved. Each family has
a closed coarse state alphabet. The kernel constraint stands: state
transitions are events; alphabets here only name the states.

## 7. Challenge vocabulary

- **Domain policy**: admitted domain ids and separation namespaces (κ axis).
- **Sample spaces**: named spaces with sizes — the |C_i| that
  soundness rows consume — are admitted as challenge spaces.
- **Modes**: oracle model (a κ fact, per artifact); sampling rule
  (`uniform` for the unspelled scalar default and
  `uniform_independent` for the admitted vector form; rejection,
  distinct-index, and pow-conditioned sampling are reserved until their
  semantics and rows land; rule values are closed and fail closed); shape
  (scalar | vector⟨count⟩ — count is the identity-bearing sample
  multiplicity of one challenge event, priced beside the per-sample
  space, kernel §1.5). Reuse is a reduction-contract fact of the use, never a
  challenge-producer fact; ProtocolVocabulary v4 admits exclusive priced uses
  only. A future shared-use law is a versioned contract/theorem extension.
  Grinding is a mode fact priced by the admitted grinding rule; that rule
  prices a separate accepted-PoW premise rather than inventing another carrier
  sampling rule. The canonical spelling is `uniform` exactly when count is `1` and
  `uniform_independent` exactly when count is at least `2`. Projection emits
  that spelling, and direct OIR verification rejects every other pairing.
- **Construction profiles (κ)**: codec, sponge, and iv-policy vocabularies are
  admitted through `registry/construction-profiles.json`, which is the exact
  authority for the admitted entry set. Sponge entries declare alphabet order,
  capacity, and rate; codec entries declare pure squeeze shape, digested at
  admission. `mod_reduce` maps a uniform value in
  `N = alphabet_order^symbols` modulo the challenge space `q`, with exact bias
  r(q−r)/(Nq). `tuple_bijection` instead requires `q = N` and then has exact
  zero bias; every other target is a refusal, not an implicit reduction. The
  Soundness Kernel derives codec bias from the sealed challenge, sponge, and
  codec facts (`soundness.md` §5.2); bias is never a declared registry value.
  Each challenge event
  selects its codec through its semantic
  payload class; there is no distinguished global `chal` codec route. A sealed
  artifact pins the content digest of every consumed entry — the
  kappa sponge and every codec a payload class routes through — in
  the vocabulary table's `construction_profiles` section, unconditionally on
  consumption (a codec's decode width is transcript bytes and proof
  ABI whether or not any hop prices it; zkc-E229 fails closed at seal).

  A Plonky3 profile name alone is not evidence of Poseidon2 execution. The
  registry does not carry permutation constants, overwrite/length framing,
  output-pop order, or challenge values; those are supplier behavior.

  Supplier behavior is nonetheless identity-relevant: two suppliers that frame
  differently derive different challenges from the same transcript, so
  whatever the cross-implementation gate covers has to be stated somewhere.
  The pinned duplex profile's framing is fixed here as a supplier contract
  rather than registry content — the rate slots an absorption did not
  overwrite are zeroed, the absorbed length is added into the first capacity
  slot, outputs pop last-in-first-out, and the IV is absorbed as big-endian
  four-byte chunks with a short final chunk. That is a zkc extension over the
  upstream challenger, which does neither the rate zeroing nor the length
  binding, so the pinned replay harness — which runs upstream's own
  construction — does not cover this rule. The
  `plonky3_bb31_low_bits` mapping is defined only for a target `q = 2^b`,
  where masking low bits equals reduction modulo `q`; every other target
  refuses. An FRI transcript may mix
  extension-field draws with low-bit index draws; the class-routed codec
  model represents that distinction. Registry admission establishes only codec
  selection and bias reconstruction, not backend transcript conformance.

## 8. SealPolicy modes

`closed_proof, residual_artifact, host_exporting_artifact,
assumption_allowed_artifact, analysis_only_artifact`. Each policy defines its
permitted sink kinds, permitted check modes, permitted body policies,
composition-obligation stance, and minimum conformance tier. A policy name is
not shorthand for a weaker subset of those fields.

## 9. Endpoint kinds

`verifier` and `prover_skeleton` are admitted. `verifier_gadget` is reserved
and must be refused by OIR. Endpoint kind names MUST NOT name backend
libraries, field/hash profiles, or recipes.

## 10. Signature vocabulary

This section is canonical for the closed vocabulary a signature may name.
The declarations themselves live in `registry/soundness-signature.json` and
their semantics in [`soundness.md`](soundness.md): a rule states a typed
conditional transformation, a binding connects it to an exact protocol
occurrence, and an applicability condition is either discharged by a named
machine decider or carried as an explicit external hypothesis. Nothing about
a declaration reaches the artifact, and no label counts as discharge by
itself.

A formalization receipt records a mechanized statement asserted to correspond
to a declaration. It separates what a machine establishes from what a person
asserts: the declaration's printed type and its axiom profile are obtainable
without proving anything and are recorded so a later reading can be compared
against them, while the correspondence itself, and how far it reaches, are the
author's. The state is one of three, because a hole appears in two independent
places — a statement whose proof is admitted is about the right object and is
not proved, and a statement whose subject term is itself admitted would not be
about the right object even if every proof were discharged. An empty axiom list
is the claim that none were admitted, which is why it is a list. The
obligations a cited statement has no counterpart for are named as slots the
rule declares, and freezing checks them against it, so a coverage claim cannot
quietly fall out of step with the rule it is about.

A formalization absence is the other outcome of the same survey: the
repository and revision that were read for a counterpart declaration, the
statement the rule would cite in the author's words, and where the precise
demand is recorded. A rule without a receipt is then not silent — it says
what was looked for and what was not found — and when that repository's
counterpart lands, the absence is replaced by a receipt rather than
amended. A receipt and an absence may coexist on one rule when they name
different repositories: each speaks only for the repository it was read
against.

A receipt's recorded statement is the printed type in a normalized form —
whitespace collapsed and glyphs transliterated into the printable-ASCII
encoding domain a registry string is held to — and the reading driver
recomputes exactly that form from the checkout and compares it, so a
recorded statement that is not what the pin prints is drift, not prose.

Rule and binding *instances* are vocabulary; the kernel fixes only the
discipline — track and regime typing, the admitted security indices, and the
requirement that every unmet condition surface as a hypothesis.

The stage-bearing vocabulary is nevertheless **closed and exact**, and it is
owned by [`soundness.md`](soundness.md) §5.1: the admitted `SecurityIndex`
values (notion × track × variant × model, nine admitted), the closed nine-case
`RuleBody` variant with one exact index signature per body, and the
structurally monotone bound grammar. This page adds no second spelling of any
of them. No stage-node/edge/loss registry is part of the current vocabulary.
Stage names such as `rbr_knowledge`, edge ids such as `ss_entry` and
`sr_to_fs_duplex`, `Prem`/`Err`/`Adv[id]` loss constructors, and the
`zkc/theorem-row/v5` registry have no accepted current representation.

The intended effective path regime is the join `it ⊔ R = R`,
`comp(A) ⊔ comp(B) = comp(A ∪ B)`. Regime is never authored: it is derived
from the primitive-game support of the closed result (`soundness.md` §3.2).
The admitted catalog has no computational-entry/CSS bridge into RBR. Three
rules conclude at computational special soundness and no admitted body takes
that result as a premise. This deliberate sink keeps every KZG-terminated
protocol out of the Fiat–Shamir track. The executable-normal-form restriction
is specified in `soundness.md` §4.3.

- **Provenance and annotations.** A rule declaration carries a closed
  status inside its declaration digest: `admitted` offers the rule as
  executable, and `declared` records it while no binding may name it —
  a rule whose cited theorem was refuted and a rule that only states
  what a provider supplies are the same case, a declaration that is
  not executable. Status is content because it has effect; two
  signatures with the same digest offer the same executable rule set.
  Citations, source anchors, revisions, and review notes are
  annotations outside every declaration digest, so an editorial change
  never re-mints a rule and the presence of an annotation never
  discharges a premise. The kernel certifies no validity class:
  reproducing a superseded analysis is done by naming the historical
  signature by its digest, and there is no time-indexed policy gate.
- **Assumption objects**: name, object reference (a closed `algebra`
  vocabulary of curve/group ids, or a setup artifact digest),
  parameters bound to declared artifact quantities, game statement,
  citation. Deduped by content along walks. The admitted equality rule
  establishes exact equality of algebra coordinates only where a binding's
  declared arguments meet a rule's typed instance parameters.
  Artifact/SRS/decoder/relation-payload compatibility is a distinct
  applicability question; `zkc.side.algebra_match` and
  `zkc.side.degrees_within_srs` remain visible obligations until a
  digest-shaped carrier binding and admitted decider establish them. A short
  suite label such as `bls12-381` is not an SRS identity or such a proof.
- **Admitted entries**: the sigma family (`zkc.ss.sigma`, special
  soundness, k = 2 on the exact `sigma`, `sigma_dleq`, and `sigma_or`
  contracts — Schnorr, Chaum–Pedersen, and the CDS94 OR-composition; the
  entry carries the arity vector and no loss, because information-theoretic
  special soundness has extraction error 0 and the statistical price is
  generated by the SS-to-RBR hop); sumcheck ε_i = d_i/|C_i|
  (`zkc.rbr.sumcheck`, CCHLRR eprint 2018/1004 §5.2); the six FRI
  proximity regimes (`zkc.rbr.fri.capacity` — declared, its cited
  conjecture family refuted as stated — `zkc.rbr.fri.johnson`,
  `zkc.rbr.fri.udr`, `zkc.rbr.fri.johnson_linear`,
  `zkc.rbr.fri.random_words`, and `zkc.rbr.fri.threshold_halving`,
  each reading the rate from the declared `log_blowup` reduction
  parameter under the shape side condition); the opening and
  RLC entries (`zkc.rbr.evalopen`, `zkc.rbr.ordered_rlc`); the GKR
  layer (`zkc.rbr.gkr-width2-layer`); and the application-relation
  batching entry (`zkc.rbr.r1cs_batch`, s/|C| with the constraint count a
  declared analysis parameter surfaced as an explicit obligation).
- **Admitted hops and compositions**: SS ⇒ RBR (`zkc.rbr.from_ss`, BGTZ
  Thm 1.1), grinding (`zkc.rbr.grinding`, ethSTARK Thm 6 — one adjacent
  round scaled by the sealed pow exponent), RBR ⇒ SR
  (`zkc.sr.from_rbr`/`_knowledge.v2`), SR ⇒ FS under the duplex profile
  (`zkc.fs.duplex`/`_knowledge.v2`, Chiesa–Orrù eprint 2025/536), the
  special-soundness-preserving KZG batch (`zkc.pcs.kzg_batch` and its
  ARSDH-collapse sibling `zkc.pcs.kzg_batch_arsdh`, KLPS26), and the
  round-by-round sequential compositions
  (`zkc.rbr.gkr-width2-chain`, `zkc.rbr.r1cs_sumcheck-chain` — the
  premise's rounds followed by the occurrence's own, no bound combined,
  with the span guards recorded beside the body in `soundness.md` §5.1).
  `zkc.pcs.kzg_css` stays premise-only: admitted, bound by nothing,
  reachable only as an assumed external judgment. Shared-challenge
  conjunction (ProtoStar Lem 7) stays reserved.
