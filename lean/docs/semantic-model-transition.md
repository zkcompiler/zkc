# Typed construction and executable model transition

The authoritative meaning of a constructed instruction is
`Construction.Domain.step`; whole participants use `Domain.participant` over
the admitted program. The metered Code interpreter adds resource accounting
and delegates instruction behavior to that meaning. The byte interpreter is a
separate actual stage, related to Code by checked native correspondence.
Neither a type-preserving rename nor an unchanged theorem statement proves
that its dependency meanings stayed unchanged.

This document describes the maintained interfaces and their scope. The
historical instruction interpreters and duplicate Uniform proof stack are
removed; full GKR and composed Sumcheck use checked Domain/source connections.
The final model-transition inventory and independent replay remain separate
acceptance evidence. A successful finite artifact check is not an
execution-correspondence theorem.

## Admission, execution, and security have different owners

| Boundary | Evidence | What it does not establish |
|---|---|---|
| Export to admitted program and participant | Exact structured import, construction and projection checks | Equivalence of executions or security |
| Actual participant to a readable source proof | All-reply open-process correspondence, including stops and effects | Honest success or a probability bound by itself |
| Actual byte instructions to metered Code | `DomainVM.checked_execute_metered` with finite native admission and local helper preparation | Correctness of an unmodeled Rust execution |
| Metered Code to participant observation | Budget-independent pruning; equality/success when sufficient resources are proved | Acceptance from a resource bound alone |
| Source proof to fixed security request | Property-specific proof of the requested game and all required stage links | A different adversary, oracle, representation, or deployment model |

`checkLowering` always validates canonical normalization and both input and
output schemas, including when the instruction lists compare equal. Its
accepted certificate obtains semantics from
`CanonicalNormalization.accepted_sound`. Native admission separately checks
actual local instructions, helper signatures, occurrences and frame/loop
custody. These finite facts are inputs to the execution theorems, not
assumptions that a whole execution already agrees.

## Sumcheck: preserved claims and changed intermediate meanings

The retained Sumcheck source binding covers every typed public table, claim,
round count, initial history, proof stream and lawful monadic challenge. It
assumes neither the relation nor a valid table shape. Excess rounds refuse;
terminal helper tests retain their actual order and resource boundaries.
`SumcheckProof.compiled_transform` relates the actual `ScalarVerifier.verify`
to the original source transform. `compiled_transform_rounds` additionally
uses the mathematical premises needed to interpret a decoded table.

The executable connection has three separate consumers:

- `SumcheckProof.executable_metered` observes the actual byte interpreter
  through `DomainVM.metered`. This replaces an intermediate historical Code
  meaning; it is an intentional model change.
- `SumcheckProof.domain_prunes` has the fixed byte-endpoint type: actual native
  validation can only remove acceptance from the actual constructed verifier,
  using the actual receive plan and bytes after the 40-byte header. It covers
  all budgets, decoders, framed byte strings and typed public values.
- `SumcheckProof.executable_transform_prunes` keeps the original source-byte
  proposition, composed through the maintained constructed-verifier theorem.

`SumcheckCompleteness.honest_accepted` keeps the concrete actual-native
acceptance proposition. Its hypotheses remain field-coordinate codec
inversion and message-size bounds, a 32-byte binding, table length
`2 ^ rounds`, rounds within the static maximum and budget at least
`72 + 59 * rounds`. It requires no inverse law for unrelated payload types.
The proof combines mathematical honest success, sufficient resources, exact
message decoding and native correspondence. Success includes the returned
Boolean and consumption of the whole proof.

The parameterized family now derives mathematical honesty from local helper,
occurrence and price laws, then proves actual native byte acceptance. Its
generic dependency closure excludes the concrete Entry and whole-program
success combinators. The retained Entry instantiates it with append price two;
a second checked native fixture changes the entry, oracle keys and maximum.

This is a changed family interface, not an assertion that every old admission
record remains admissible. Four origin-presence facts did not establish typed
draw requests. A checked counterexample retains those facts while replacing
the request by an unsupported tag; canonical native admission refuses it.
The new family requires the actual typed request, receive schema, coordinate
resolution, projected-key and suite laws. The model-transition inventory must
record this explicit boundary separately from the preserved concrete byte
proposition. No execution-success premise conceals the change.

Historical comparison proofs and old intermediate statements are retained in
Git/archive evidence, not exposed as compatibility aliases. The former raw
`spec_transform` theorem related two historical interpreters on lists of a
particular length; it did not check a Domain input schema. No unconditional
raw-input equivalence is asserted for it.

## Why universal historical equality is false

The historical model could consume both round messages before refusing a
Boolean in Sumcheck's scalar claim slot. Domain refuses at the input schema
and leaves those messages unread. A malformed guard declaring a Boolean
result likewise distinguishes the old model from Domain. Such counterexamples
prevent replacing the historical interpreter's definition and calling the
change semantics preserving.

The maintained source theorem covers the exact admitted, typed subject.
Malformed raw exports are rejected during admission. False claims and
wrong-shaped tables of admitted types remain adversarial inputs; they are not
removed by a relation premise.

## The selected oracle and history boundary

`Origin.withoutCoordinates` structurally removes dynamic coordinates from the
execution suffix before invoking the selected scalar challenge function and
its cache. The arbitrary initial history remains an opaque prefix. The source
connection proves the actual message, challenge and delivery occurrences at
every reached iteration; delivery remains a send, distinct from a draw.

This preserves the selected scalar oracle's effects, including its state and
query count. It does not identify that oracle with an independently sampled
oracle indexed by all nominal histories. Distinct nominal keys may project
to the same scalar key. A new nominal random-oracle game needs its own
sampling, adversary and cost theorem.

The byte bridge preserves the returned observation and unread suffix on
successful execution. On failure it preserves the selected stop observation
and preceding effects; it does not claim equality of discarded raw bytes,
physical counters or cleanup frames. Cleanup is checked by its separate
execution invariant. Framing, binding and complete-proof acceptance remain
explicit parts of `validate`.

## Acceptance evidence

A final model-transition record must enumerate every protected root and its
type-and-proof dependency closure. Unchanged declarations, preserved
fragments with a correspondence theorem, intentional new meanings and retired
roots with named replacements are distinct dispositions. Standard axioms,
closed dependency bodies and exact artifact identities are checked before the
current model is accepted. Independent kernel replay checks that current
model; it does not prove equality with the historical model.

The archived historical failed comparisons and replay failures remain
historical failures. Neither refreshed lock files nor a majority of replay
checkers can turn them into a preservation result.
