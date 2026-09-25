# Concrete profiles are grouped apart from the common laws

The [specification](../spec/README.md#adopted-scope) keeps in its common
chapters only the value, binding and lifetime, analysis, representation and
codec laws that hold across concrete choices. Each particular vocabulary,
algorithm, representation or experiment is a
[profile](../spec/profiles/README.md), filed under one of six groups: source,
compiler, realization, providers, Sumcheck and services. A profile's
restrictions apply inside that profile and not to the whole language. Two
definitions are separate profiles when they have independent parameters or
conclusions, and their connection is then an explicit link. The
[writing rules](../spec/writing.md#content-and-structure) state the same
separation as an editorial rule.

## Alternatives

**Leave each concrete choice in the common chapter that uses it.** String
names, a dimension grammar, a finite phase algorithm, an instruction-list
machine and one eight-byte scalar codec can each be scoped correctly by a
sentence inside a common chapter. Placed there, they still read as requirements
on every frontend, checker and runtime.

**One profile per protocol.** The scalar round component returns a residual
scalar, the complete verifier returns a terminal Boolean, and the local prover
returns a cut before a later challenge. Framing adds a statement root and a
stateful query interface. A single Sumcheck profile would assume a common
terminal that these components do not have. The affine service and the
commitment-session scheduler likewise have different state machines and
observers.

**File a law under its first consumer.** The product-tape laws quantify over an
arbitrary local signature and draw type. Placed under Sumcheck, beside their
one-round consumer, they would lose that visible generality. The test cuts both
ways: the affine controller's expression policy stays with the affine service,
because it supplies the controller premise of that service's law.

**Give every chapter one uniform section template.** A template arranges a
page. It does not settle which page owns a definition.

## Reason

An author of a frontend, a checker or a runtime has to tell a law that binds
every implementation from a choice that one profile made. Grouping is
editorial: it introduces no intermediate representation, no protocol version
and no change of Lean namespace. The informative Sigma, Merkle and
message-shape clients stay in the inventory without becoming interoperable
cryptographic profiles.

## Reopen when

A new consumer exposes a missing boundary: it has to depend on a restriction
that only a common chapter states, or on a general law that only a profile
states.
