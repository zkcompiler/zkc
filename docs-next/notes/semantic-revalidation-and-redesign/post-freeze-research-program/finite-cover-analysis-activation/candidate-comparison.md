# Candidate Comparison

> **Kind:** Temporary architecture decision record
> **State:** Selected
> **Authority:** None

## Decision criteria

Candidates were compared against the same requirements:

- preserve the exact raw verifier semantics, including noncanonical accepted
  `Nat64` values;
- bind the exact response-difference extractor rather than an extensional
  shortcut;
- produce a finite replayable run without materializing the raw carrier;
- keep semantic algorithms distinct from checker implementations;
- expose coverage, congruence, and transfer as independent obligations;
- avoid root-regime rotation when an ordinary module suffices; and
- keep the resulting claim limited to the exact finite subject.

## Alternatives

| Candidate | Benefit | Decisive problem | Decision |
|---|---|---|---|
| Enumerate the complete raw carrier | No quotient proof | Eight `Nat64` leaves make the product intractable and obscure verifier observability | Reject |
| Enumerate only canonical pairs without a quotient contract | Small run | Does not cover accepted noncanonical commitment and response encodings | Reject |
| Use honest-prover witness and nonce tuples as representatives | Easy generation of accepting pairs | Introduces private provenance not observed by the verifier and risks circularly assuming the witness being extracted | Reject |
| Return constant witness `3` for statement `8` | Extensionally succeeds on this fixture | Does not bind or test the selected extraction algorithm and turns the fixed statement into a loophole | Reject |
| Add one opaque `schnorr.extract` primitive | Small implementation | Hides the response-difference formula and has no reusable meaning outside this fixture | Reject |
| Add modular arithmetic to the Foundation root profile | Straightforward global availability | Rotates the shared semantic regime and every dependent identity without cross-domain necessity | Reject |
| Reuse the existing fixture-only primitive module | Minimal code change | Gives durable meaning to a test-scoped module and couples the new subject to unrelated fixture primitives | Reject |
| Exact verifier-observation quotient plus owner-local modular-arithmetic module | Small finite run, explicit transfer laws, reusable arithmetic, narrow identity cone | Requires exact certificate and provider work rather than a test-only enumeration | **Select** |

## Selected architecture

```text
raw accepted pair
      |
      | portable normalization
      v
canonical representative ----> portable candidate extractor
      |                                  |
      | canonical stream                 v
      +--------------------------> candidate witness
                                           |
                                           v
                              representative success

coverage capability + congruence capability + success-transfer capability
                              |
                              v
               checked finite-cover Analysis judgment
```

The five checker bindings remain exactly the representative stream,
representative-domain predicate, representative embedding, candidate, and
representative-success operations. Normalization, raw membership, output
congruence, and raw success remain semantic parts of the authenticated target
and certificate obligations; they are not silently replaced by extra checker
authority.

## Implementation consequence

The executable package now supplies an exact extension-provider path for the
new ordinary module without changing the default Foundation evaluator. The
provider is operational support only: module bodies, primitive law sources,
portable terms, and algorithm identities remain the semantic authorities. Its
identity cache retains exact immutable algorithm objects and therefore does not
admit a different preimage that merely repeats an identifier.

This implementation work must preserve the default evaluator's existing
behavior and prove by mutation that advertising an ID without a matching
module body, type rule, denotation, or cost rule yields a closed noncompletion
rather than accidental execution.
