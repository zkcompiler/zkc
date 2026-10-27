# Checked compiler stages

A security theorem transfers between compiler stages only through a proved
relation between their meanings. A structural check is useful evidence, but
acceptance yields that relation only when a soundness theorem says so. This
note describes the common architecture and its current coverage. The owning
specifications are [participant projection](../spec/participant-projection.md),
[transcript construction](../spec/fiat-shamir.md) and
[executable validation](../spec/executable.md).

## The common interface

A checked rule has five parts.

1. **Meanings.** Source and target have independently defined meanings. A
   process uses `PIR.Process` over a declared action interface; a consumer
   interprets its effects with explicit handlers.
2. **Certificate.** Untrusted data proposes a connection between exact source
   and target artifacts. It can describe a rewrite, an occurrence layout or a
   derivation. Artifact names alone do not establish identity.
3. **Check.** A total checker validates the certificate and its artifact
   association. A kernel-checked proof of acceptance establishes what the
   checker actually checks. Running a generator or recording a digest does not
   establish a semantic theorem.
4. **Relation.** The rule states precisely which values, effects, stops,
   observations and states correspond, including its free parameters.
5. **Soundness.** A theorem turns acceptance into that relation. A stage without
   this theorem still needs a separately checked semantic certificate for each
   artifact. Calling its admission check does not replace that certificate.

Rules compose only through compatible meanings and relations. The intermediate
artifact, environments, observations and actual reached state must match.
Matching a stage name or a return type is insufficient. Composition also
carries the assumptions and losses of each property-specific transport theorem.

## Relations by property

| Relation | What it establishes | Additional obligations |
|---|---|---|
| Exact Process equation | The same effects, continuations, stops and return values under the selected meaning | An equation to a transformed process needs a separate theorem about that transform to transfer security |
| Simulation or representation relation | Related source and target executions, frames, values and observations | Acceptance reflection can transfer soundness; completeness also requires honest progress, suitable codecs and sufficient resources |
| Probabilistic reduction | A specified comparison between security experiments | Adversary interfaces, parameter admission, query bounds and losses must match |

A full execution connection can serve more than one property. Completeness
uses it with the honest executions and actual reached states; soundness uses
it against arbitrary admitted replies. Neither property should weaken the
connection to the executions convenient for its proof. The security theorem
remains separate from the execution relation.

## One constructed meaning

`Domain.participant` is the nominal meaning of the constructed artifact, for
both plain and Fiat–Shamir profiles. Its Process retains typed values,
checkpoints, stops, frames, effects and returned data. The scalar ABI is a
partial presentation of this same Process through handlers. It is not another
Instruction interpreter.

`Domain.Correspondence` proves that a readable Process view equals the actual
artifact's execution for every environment and typed reply. The shared rules
cover individual instructions and their composition. The view can be generated;
its equation is kernel checked independently of the generator. It does not by
itself connect the artifact to the original source's mathematics.

`Original.Simulation` expresses that further connection, with source role masks,
input locations, helper laws, live-frame relations and complete output readback.
`Original.Simulation.participant` assembles a whole participant simulation from a
full body certificate. It does not infer that body certificate from structural
admission.

## Structural admission and the remaining soundness step

`project` walks the admitted original and exported role-local program in
lockstep. It tracks which values the role holds, follows protocol applications,
checks helper and calculation uses and matches repeat bodies with exported
loops. `checkCompiled` combines projection and transcript admission against one
`Structured.Imported` source. Selection additionally fixes the context, public
input order, service replacement, sorts and acceptance position.

These are finite admission facts. There is currently **no generic theorem from
`project` or `checkCompiled` acceptance to full source-to-participant simulation
under the current Domain meaning**. The old proof for a different reading is
not a theorem about this meaning. Maintained consumers instead provide checked
source and helper laws and explicit simulations.

For GKR, structural descriptors now supply physical input locations, nested
loop frames, operands, yields and return selectors to reusable proof templates.
Both the canonical layout and a changed layout obtain full checked connections.
This reduces maintenance per layout. The templates, mathematical laws and
remaining source connection are still authored work; this is not a generic
checker soundness result. See the [connection owner](../../security/ZkcSecurity/Realizations/Gkr/README.md).

The next connection unit uses the normal form as its anchor, installs helper
laws by body shape, assembles derivations and reports remaining obligations at
source locations. Its decisive theorem must turn a passing source-to-participant
check into a simulation for the current meaning, first for validators and then
producers. It must cover nested repeats and multiple component applications.
GKR and a structurally different protocol must exercise that generality before
using it to claim low per-protocol connection cost.

## Composition with security consumers

The maintained scalar consumers combine their full artifact binding and source
connection to obtain an equation of the following form:

```text
selected handler (Domain.participant artifact)
  = transform context challenge originalVerifier
```

The exact theorem includes its inputs, initial history, proof messages, unread
suffix, output selection and stop behavior. Extra hypotheses for decoded tables
or well-formed circuits belong to subsequent mathematical theorems, not to an
otherwise unconditional artifact equation. A security consumer applies its
registered transform theorem to this equation; a completeness consumer uses the
same connection with the honest execution laws.

For Sigma protocols and multi-round protocols the security methods differ.
Their request meanings and adversary interfaces stay fixed independently of the
chosen evidence. Query and field-size losses belong to the applicable theorem;
a structural compiler check does not establish them.

## Executable and native boundaries

The executable model relates instructions, typed proof data and byte consumption
to the nominal participant through its stated lowering and representation laws.
The normalization checker has a soundness theorem for the supported pure
calculation scheduling. Prepared helper bodies and their correspondence remain
explicit inputs. Stops due to resource exhaustion preserve acceptance reflection;
completeness additionally requires sufficient budgets and progress.

The byte transport theorems expose these premises, including
`checked_validate_sufficient`. They do not certify every implementation of a
native kernel or hash provider. A future realization checker must similarly
have a theorem yielding the required simulation, rather than another authored
connection for each protocol.

## Deterministic obligations of Fiat–Shamir

The occurrence encoder's `occurrence_inj` theorem establishes injectivity and
prefix separation for templates and iteration coordinates. Export decoding and
re-encoding check exact occurrence bytes. These facts are distinct from
injectivity of an entire suite's typed-history encoding, source correspondence,
and native transcript implementation correctness.

A complete deployment argument must connect the selected handlers and histories
to the suite's framing, labels and codecs, then to the actual hash and runtime
providers. Projection of nominal histories to a scalar presentation happens
before its oracle and cache; it must not silently identify two different
random-oracle interfaces. The specifications above state which maintained
consumers have each connection and which assumptions remain.
