# Composed numeric state

Changing numeric shapes, actual received messages and returned retry decisions
share the ordinary mathematical pipeline and interpreter. The maintained clients
in [composed-state.mlir](../../compiler/test/fixtures/mathematical/composed-state.mlir)
exercise shrinking inner-product state and a growing commitment batch. They use
BLS12-381 field/group kernels, both installed BLS transcript suites, typed proof
messages and persistent native attempts.

The clients are algebraic execution controls. Their test bases have known discrete
logarithms and the final messages disclose coefficients. They do not establish
zero knowledge, knowledge soundness or compatibility with a range-proof system.

## Representation and execution

- Dynamic numeric tensors carry field and group vectors. Their lengths can change
  between repeat iterations while their MLIR types stay fixed. The producer also
  carries its affine RNG through each loop and sends one fresh scalar per round
  before the challenge. Those bytes bind the transcript without changing the
  algebraic recurrence.
- `protocol.repeat` retains a compact body, carried state and immutable captures.
  Each role receives its own state and actual messages after projection.
- Partial splitting, indexing, inversion and shape-sensitive arithmetic are
  contracted local calls. Scalar total arithmetic remains mathematical SSA.
- The verifier compares received group vectors with its independently calculated
  next vector, including length. It then carries the actual received value.
- Native proof construction derives participant transcript operations. The
  existing attempt host preserves the producer RNG and cumulative work, creates
  fresh transcript state for each attempt, and publishes only a completed buffer.
- The same authored clients also compile to structured-message interactive
  bundles. Their driver still executes the ordinary participants and codecs.

The public specification owns [iteration](../spec/profiles/compiler/structured-iteration.md),
[proof messages](../spec/profiles/compiler/structured-proof-messages.md),
[attempts](../spec/profiles/compiler/native-proofs.md#native-attempt-policy)
and [interactive bundles](../spec/profiles/compiler/run.md).

## Shrinking inner product

The public input is a group vector `G`, claimed commitment `C`, and round count
`n`; the producer supplies coefficients `a`. An attempt draws a salt `s`. For
nonzero `s`, start with `a / s` and `C / s`. A zero salt requests retry and the
verifier refuses it.

In each round split `a` and `G` into equal halves and send:

```text
L = sum(a_left[i] * G_right[i])
R = sum(a_right[i] * G_left[i])
x = transcript challenge

a' = x * a_left + inverse(x) * a_right
G' = inverse(x) * G_left + x * G_right
C' = C + x^2 * L + inverse(x)^2 * R
```

The invariant is `C = sum(a[i] * G[i])`. The producer sends `G'`, and the
verifier checks it against its own fold before carrying it. At the end the
producer sends the residual coefficient vector. The verifier checks its MSM
against the final claim. Partial folding is permitted: the terminal vector need
not have length one. Zero rounds preserve the initial relation, including empty
vectors. A reached split requires a positive even length; invalid lengths stop.

## Growing commitment batch

The public input is `G`, `C` and a count `n`; coefficients `a` belong to the
producer. Apply the same attempt salt. Start with empty field/group vectors and
identity group accumulators. For each index:

```text
D_i = (a[i] / s) * G[i]       # producer sends the contribution
x_i = transcript challenge
coefficients.append(x_i * a[i] / s)
bases.append(G[i])           # producer sends the growing group vector
sum += D_i
weighted += x_i * D_i
```

The verifier checks every received prefix against the public bases. It checks
`sum == C / s` and the final received coefficients' MSM against `weighted`.
This exercises append, indexed access, changing field and group state, and two
terminal subjects. The claim covers the first `n` coefficients and bases; either
input may contain an unused suffix. A reached out-of-range index is fatal.
Empty batches are valid for the identity commitment even with nonempty inputs.

## Retry and failure meaning

`inverse` is a local conditional: zero yields zero with `ready = false`; nonzero
executes the partial inverse and yields `ready = true`. The producer accumulates
readiness and returns it to the attempt host. The verifier has ordered nonzero
guards. Shape, index, budget and explicit-stop failures stay fatal.

This is a complete-attempt schedule. A failed readiness predicate does not skip
later draws, messages or calculations. Consequently it does not implement early
abandonment of a protocol round. [Conditional entry completion](entry-completion.md)
supplies that control mechanism, but this client retains its complete-attempt
behavior. Changing it requires comparing the exact retained prefix and resource
custody. Successful proof equality alone cannot justify that transformation.

Deterministic tapes supply each attempt salt followed by its actual round draws.
They force retry, exhaustion and persistent RNG advancement
in proof execution. Interactive provider tapes additionally force a zero round
challenge. No test replaces the hash output of either installed Fiat-Shamir suite.

## Program and bundle admission

These clients use three admission rules:

1. Source-size validation recognizes runtime-count loops in the single
   `zkc.program/2` executable contract.
2. Interactive bundles need an exact carrier match for structured messages.
   `zkc.run/1` embeds `zkc.program/2`, uses the existing compact
   schedule validation, and admits the installed variable-size native codecs.
   Fixed-width codecs still require their exact encoded width; all messages
   retain per-message and cumulative byte limits and receiver-side decoding.
   Only the exact `zkc.run/1` and embedded `zkc.program/2` tags are admitted.

3. Native random-service queries in loop frames use the same program contract,
   retaining the entry/loop frame, service-port and method checks.

The same execution path supports [nested records and ragged data](nested-data.md).
Provider and domain support is described by the
[structured proof contract](../spec/profiles/compiler/structured-proof-messages.md).

## Maintained checks

[Compiler generation](../../compiler/test/native_composed_state.py) retains compact
loops and produces both proof deployments and interactive bundles. The
[execution client](../../crates/zkc-tools/examples/native_composed_state/main.rs)
checks independent equation/transcript reconstruction, actual received values,
zero rounds, empty inputs, unequal unused batch suffixes, changing shapes,
malformed framing, retry/exhaustion, fatal failures, persistent RNG state,
cumulative work, context binding and cleanup.
It compares normal, unsimplified, storage-release and combined modes. Canonical
altered messages must reach the authored guard or terminal predicate; malformed
frames remain typed decode stops. Independent [bundle controls](../../crates/zkc-tools/tests/run.rs)
cover exact tag and record matching, nested records and alternatives, dynamic leaves,
actual replacements, wire limits and pending-message cleanup.

[Cross-language tests](../../tests/protocol/test_native_mathematical.py) also run
producer and verifier in separate CLI processes and check failed publication.
Current evidence is bounded to the declared clients, installed domains, transcript
suites and tested input ranges. It does not close all foundation combinations.
