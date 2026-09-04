# F1-R1B Exact-Target Core Carrier and Bounded Admission

> **Kind:** Temporary F1 exact-source carrier/admission result
> **State:** F1-R1B complete for one bounded target Fresh Schnorr slice;
> F1-R1C0 now returns `CannotAnswer` on owner-view source determinacy and opens
> F0-V; R1C waits on that repair, while R1D, F1-I, and F2 remain open
> **Authority:** None. This result changes no current or target semantic law,
> profile identity, implementation admission result, Analysis judgment, or
> product claim.
> **Evidence:** The focused evaluator under
> [`evaluation/formal-source-target-core-f1r1b/`](../../../../evaluation/formal-source-target-core-f1r1b/README.md)
> passes 27/27 exact expected cases.

## 1. Question and result

F1-R1B asks the next question after exact target profile publication:

> Can one nontrivial subject be encoded in the complete target Appendix-A
> carrier, admitted under the owner-selected Interaction laws rather than only
> assigned a typed ID, and then used to form a Fresh Protocol only through the
> resulting admitted owner handle?

The bounded answer is **Affirmative** for the selected finite Schnorr slice.
The evaluator forms all fourteen Core fields and both Protocol fields under the
frozen target Interaction profile, authenticates exact K1 dependencies,
executes every target admission stage applicable to the slice, and mints
process-local admitted Core and Fresh Protocol handles. Target profile
substitution, retained IDs, missing or extra modules, wrong declaration kinds,
wrong algorithm ABIs, bad scopes, stale backlinks, future reads, private
Challenge conditions, invalid sharing, unresolved claims, missing fallback,
and Core/Protocol authority substitution are all classified exactly.

This result closes the carrier/admission prerequisite only at bounded research
resolution. The evaluator is not the current compiler's owner implementation,
does not implement every target constructor, and issues no owner static view.
It therefore establishes neither current Q0 admission nor Q1 admitted-source
correspondence.

## 2. Exact subject and identities

The positive interaction is finite additive Schnorr over `Z/3Z`:

```text
statement Y
  -> commitment A
  -> independent Fresh challenge c
  -> response z
  -> check z = A + cY mod 3
  -> guarded Accept
  -> unconditional Reject
```

This is an executable semantic discriminator, not a cryptographic-security
example. Its finite equation has 81 possible inputs, all checked by a
separately written term interpreter. K1 separately authenticates and evaluates
one accepting and one rejecting sample.

| Coordinate | Frozen value |
|---|---|
| target Interaction profile digest | `f21774d19ebf5e045b1d5c70f9bd0ee1c7eb1202dc11f948900eb067e102ce87` |
| exact-used protocol module digest | `de7f837dc849ff52fb045259839dfb9efde015a65781ad064feb5a91b0ae29b7` |
| Check algorithm digest | `86a47a88f56ed94a258b1e8215ec9b4f4537265f435bf32f7569d05f725722df` |
| target Core digest | `33f9d34abd61e22565b85fbfe03a35b3ca55f1a3980b71c5e9b729b3a93027f5` |
| Fresh Protocol digest | `5ef61d48cca624e042b89fdd56935c3e9137a0790a2625ce2dd4f7da9ca92f94` |
| profiled Core body | 8,179 octets, fourteen top-level fields |
| portable Check preimage | 179,147 octets |

The Core carries one public Statement input, one root scope and binding, one
Challenge declaration, one Check declaration, two Terminal declarations, and
six occurrences. Unused target families remain exact empty sequences. One
semantic module owns the Challenge domain, Fresh law, and commitment/response
message channels. Its unused local catalogs also provide mutation coordinates;
they do not become extra Core module roots.

The Check ABI is exactly `(Z3,Z3,Z3,Z3) -> Bool` with an empty failure row. A
separate `(Bool) -> Bool` portable algorithm guards `Accept`. The accepting
terminal requires the Check; the final unconditional `Reject` supplies finite
fallback.

## 3. What was implemented

The reference evaluator follows the written ten-stage order:

| Target stage | Bounded implementation |
|---|---|
| 1 authentication | one ledger for prior-meta basis, target profile, Core, direct modules, algorithms, algorithm module closures, and contract |
| 2 carrier | complete fourteen-field body, bounds, exact branches, dense tuple coordinates, no unknown supported constructor |
| 3 exact dependencies | derived `DirectOwnerModules`, exact-used equality, nominal declaration resolution, exact algorithm/contract bundles |
| 4 typing | K1 ValueTypes, message/Challenge outputs, exact total Boolean Check and Guard ABIs |
| 5 scopes and availability | unique root, bounded child-opening rules, binding completeness/uniqueness, exact prior-prefix reads |
| 6 order and backlinks | one-to-one Challenge, Check, and Terminal occurrence backlinks |
| 7 visibility | Challenge conditions must be public; verifier-private influence is refused |
| 8 challenge policy | Independent/Exclusive admitted; unsupported joint closure and invalid zero-consumer Shared use fail closed |
| 9 liveness | supported initial-claim sources, Check-before-Terminal order, and claim closure on every explicit Terminal |
| 10 fallback and minting | final `Always/ReachTerminal` requirement followed by one process-local admitted handle |

Fresh Protocol formation requires the identical admitted Core handle. A bare
Core candidate, another formed-but-unadmitted Core ID, a retained Protocol ID,
or a profile mismatch cannot substitute. Serialization is explicitly not the
handle. The Python token is a research model of the target lifecycle, not a
production capability-security mechanism.

Two implementations construct the complete Core and Protocol body datums. The
second shares K1's constitutional encoding and typed research carrier but does
not call the reference target body compiler. They agree on the positive Core,
six additional Core carrier shapes that exercise otherwise empty families,
and the Fresh Protocol. Agreement therefore checks the Appendix-A mapping and
top-level profile wrapper, while remaining weaker than an independently
implemented admission checker.

## 4. Design conclusions

### 4.1 The owner split survives this pressure test

No new `FormalKernel` or theorem-prover authority is needed to form this
subject. The successful responsibility chain is:

```text
Foundation authentication and K1 executable dependencies
  -> target Interaction profile selection
  -> Interaction-owned carrier and semantic admission
  -> exact process-local AdmittedCore
  -> Interaction-owned Fresh Protocol formation
```

Foundation can validly identify arbitrary target-profiled canonical data, but
that operation does not admit an Interaction subject. Conversely, Interaction
does not reimplement K1 identity, canonical values, algorithm typing, or module
closure. This is the intended profile-to-qualified-owner-judgment split.

### 4.2 Core modules and algorithm modules remain different closures

The Core's `used_modules` contains only modules directly named by Core
semantics. The portable Schnorr algorithm authenticates its own K1 primitive
module closure separately. Copying that primitive module into Core
`used_modules` would create an unreferenced extra and is refused. This confirms
that algorithm dependencies do not donate ambient semantics to the Core.

### 4.3 Exact authority must follow admission, not serialization

Fresh formation cannot safely accept only a `CoreId`: another body can receive
a well-formed ID without satisfying target admission, and an old admitted ID
does not prove which evaluator admitted it. The retained live handle binds the
Core, target profile, completed admission stages, and evaluator instance. R1C
must preserve this lifecycle when issuing views; F1-I must later replace the
offline research issuer with live implementation authority.

### 4.4 Fail-closed partiality is preferable to false generality

The target law is broader than the selected subject. This evaluator returns
`Unsupported` for exact well-formed families it does not implement, rather
than accepting them through generic records or treating them as false. The
bounded affirmative result should therefore be read as one exact fiber of the
target law, not as general target conformance.

## 5. Mutation evidence

The 27 cases include seven affirmative controls, nineteen exact
nonaffirmative mutations, and one explicit unsupported-family control.
Important discriminators include:

- retaining the Core or Protocol ID after changing its body;
- omitting a direct owner, adding an unreferenced owner, or withholding its
  preimage;
- resolving a Challenge domain through the message-channel kind;
- replacing the four-input Check with the one-input Guard algorithm;
- opening a child scope at an absent occurrence;
- duplicating each of the Challenge, Check, and Terminal backlinks;
- reading a future Prover message from a Check;
- feeding a verifier-private input into public Challenge conditions;
- selecting `Shared` without the required exact reduction consumers;
- leaving a live initial claim unresolved at a terminal;
- guarding the final fallback;
- substituting another profile coordinate; and
- forming a Fresh Protocol from a different Core ID or a bare Core record.

The gate requires the named outcome and code for every row. Agreement with an
arbitrary failure is insufficient.

## 6. Gaps and assurance position

The following remain outside this result:

- complete target admission for constants, derived values, Oracles,
  reductions, module effects, joint coins, general claim/reduction paths, and
  all nested-scope combinations;
- strategy decisions, invocation, Fresh resolution, execution, replay, and
  relation grounding;
- the Section 11 `PCGraph`, public-coin eligibility, and all six owner static
  views;
- field-coordinate resolution, the exact required-read fixed point, source
  binding, and capability issuance;
- exact Relations roots and Protocol correspondence;
- live compiler-owner issuance, package integration, provider correspondence,
  theorem environment/truth/applicability, any cryptographic property,
  transition preservation, OIR projection, and realization; and
- a second independent admission implementation or machine-checked evaluator.

| Assurance level | F1-R1B result |
|---|---|
| Q0 current source admission | open; evaluator is offline research code |
| Q1 exact admitted-source reification | open; no owner views/package/live authority |
| Q2 provider correspondence | not started |
| Q3--Q6 theorem and property | not started |
| Q7--Q10 transition through realization | not started |

## 7. F1-R1C entry contract and determinacy result

R1C should reuse this exact Core/Protocol pair and require only the identical
admitted handles. It must implement the target `PublicBindingView`,
`StrategyDecisionView`, `PublicCoinView`, `EffectView`, `ClaimReductionView`,
and Fresh `ExecutionView`, including owner-profile checks, complete bodies,
atomic field coordinates, and the least required-read fixed point.

The highest-risk part is not copying the displayed records. It is deriving the
complete producer, scope, guard, order, type, visibility, and law-reference
closure without trusting the requested manifest. The evaluator should derive
the full view and closure first, then require exact requested/realized equality.
R1C needs at least these mutations:

1. omit a producer/type/order dependency from one requested leaf;
2. add a phantom or dormant view leaf;
3. alias equal-valued occurrence coordinates;
4. substitute a Core or Protocol ID while retaining a view body;
5. wrap a Fresh `ExecutionView` under another profile;
6. reconstruct rather than pass the admitted handle;
7. inject a verifier-private path into the public-coin sink closure; and
8. substitute a semantic-law declaration reference of the right outer kind.

If the exact target source does not determine a required leaf or closure edge,
that is an F0 owner-observability defect. If it does determine the fact but no
evaluator exists, that is an R1C implementation gap. The distinction should
remain explicit before R1D packages any result.

The subsequent
[`F1-R1C0 source-determinacy audit`](f1r1c-owner-view-source-determinacy.md)
resolves this branch as an F0 defect. It preserves this exact admitted
Core/Protocol and process-local handle result, but finds that the Interaction
profile does not publish the closed view-schema catalog, nested canonical body
grammars, field-to-law map, and authority-envelope bodies required to derive
an exact manifest independently. Its 13/13 expected observations therefore
aggregate to `CannotAnswer/F1R1C-C-SOURCE-DETERMINACY`, and the K2 view shape is
explicitly refused as a substitute.

F0-V must repair and independently republish that PIR-owned boundary before
the evaluator and mutation program above resume. This requires no new Core
field, no change to the Core/Protocol split, and no Analysis-owned schema.
