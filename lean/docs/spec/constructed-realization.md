# Scalar constructed-participant realization

The actual native exporter and `Zkc.Source.Constructed.Snapshot.check` own the
constructed carrier. The scalar realization layer interprets that admitted body;
it does not replace selected Local functions with assumed protocol handlers.
`Snapshot.check_program` exposes a transparent typed body only after checking its
exact erasure against the complete export. A successful realization theorem is
an equality whose left side is that body's `Imported.denote`.

## Selected primitive model

The supported nominal domains are `bls12-381.fr`, `bls12-381.g1`, Boolean,
indices, and `transcript:merlin3.bls12-381.fr64be/0`. Field and group leaves have
fixed field/module meanings. Receives use arbitrary supplied proof values.
Primitive names and result products are preserved, including both results of a
challenge. Unknown leaves refuse. The automatic renderer additionally checks
exact signatures, arithmetic attributes, Local binding declarations, occurrence
frames, role direction, receive selectors and observation order. It decodes the
bounded native-origin template according to `Contracts/NativeOrigin.cpp` and
refuses child/loop paths outside this flat profile.

This is an explicitly selected **ideal typed transcript interpretation**. The
retained native descriptor still says Merlin. No theorem identifies Merlin,
its sampler, encoding, resource behavior, native arithmetic, or the host's root
initialization with this model. The host supplies a transcript initially binding
source, construction, application context and the full public statement. Native
conformance to that initialization and these primitives remains separate.

For Schnorr the initial binding contains base and public key. The key also
contains the received commitment. `OccurrenceContext` includes the exact policy
and primitive descriptors, so typed occurrence metadata is part of the binding.
The live transcript retains the sampled challenge, its delivery and the response
observation after the final challenge. The peer-owned Schnorr interpretation
supplies these fixed transition meanings.

For two-round Sumcheck `NativeConstruction.Schedule` contains the exact receive,
observation and challenge descriptors. It is included in `Binding` together with
source, construction, application context, all nine polynomial coefficients and
claim. The first oracle key is `(binding, firstMessage)`; the second is
`(binding, firstMessage, firstChallenge, secondMessage)`. A message is the existing
ordered constant/linear/quadratic triple. The transcript holds every observed
field value, including both challenge deliveries. A sampled challenge must be
delivered unchanged before the next message; incomplete prefixes, repeated draws
with a pending delivery, and unexpected occurrences refuse.

The native entry statement is fixed by the selected inputs; it is not inferred
from an outer artifact hash. Typed key binding is not a byte-injectivity theorem.
In particular, the full-prefix Sumcheck model does not silently remove previous
challenges to obtain a canonical challenge-free restoration key.

## Equations and observations

`NativeConstruction.experiment` for Sumcheck preserves the actual two guards,
query order and complete returned Boolean/transcript product. A guard failure
halts with `reject`. The actual-body realization theorem must prove this process
equality for every field, statement, claim and supplied proof. It has no
`Realizes` assumption. Algebraic rearrangements are discharged with ring laws,
independently of constructor admission.

`result` is a deliberate `Option Bool` projection. `experiment_accepted_iff`
identifies its acceptance at any fixed total oracle table with the two boundary
checks and final polynomial evaluation. `experiment_events` records the exact
zero/one/two-query trace under early stopping. Completing both rounds for a
security reduction is an additional observation argument: acceptance agreement
does not identify final caches, traces or returned native transcript state.

`challenge_empty`, `challenge_pending`, and `observe_wrong_delivery` prove
refusal for omitted messages, overwritten pending challenges and changed
challenge deliveries. Generated subject checks and mutations additionally test
actual SSA state threading and arithmetic. No passing finite control is a
provider-conformance or security theorem.

## Tool boundary

`lean/bridges/constructed/realization.py` accepts constructor data, a registered
protocol profile and exact receive selectors. It emits fixed Lean declarations;
requests cannot supply Lean snippets, meanings, tactics or assumed equalities.
It is a proposal generator, not a receipt issuer. The parent request checker must
freshly re-export the candidate, independently bind source selectors and the
constructed subject, kernel-check the generated declarations, and audit their
transitive axioms. Snapshot source/candidate digests alone authenticate nothing.

The selected experiment and all native/provider boundaries must remain in any
receipt. Probabilistic cached-oracle games, query budgets, extraction and
restoration bounds belong to the optional security consumers.
