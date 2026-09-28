# Mathematical protocol fixtures

These examples use the independently defined mathematical source, before a
native carrier or placement checker. From `formal/`:

```sh
lake build Examples.Mathematical.Formation Examples.Mathematical.Encoding
```

- [Sigma](Sigma.lean) constructs an interactive Schnorr-shaped source over the
  additive group of F₅ with distinct nominal scalar/group sorts. All-reply
  prover/verifier characterizations expose received messages. Honest delivery
  uses the actual prover's emitted messages under a common supplied challenge
  and proves verifier acceptance.
  The finite algebra is not a discrete-log security claim.
- [Sumcheck](Sumcheck.lean) stores one indexed body for arbitrary dimension,
  with a prover-private quadratic polynomial and fixed-capacity challenge state.
  Its verifier queries a separately bound terminal evaluator. Concrete controls
  cover two rounds, rejection before sampling and zero rounds. The general
  Sumcheck security library is not yet connected to this new source by a theorem.
- [Components](Components.lean) separates sender aliasing from fresh receives,
  bystanders from participants, aliased service ports from separate roots, and
  repeated stored helper calls from fresh service allocation. Stopped state,
  events and invocation paths remain visible.
- [Formation](Formation.lean) rejects duplicate semantic sites and a foreign
  owner. Typed references enforce sort and availability constraints; the
  extrinsic formation predicate checks participants and site uniqueness even
  in dormant bodies. Canonical table admission is separate.
- [Outlining](Outlining.lean) separates arbitrary raw local-call replies from
  a total evaluator and checks that genuine service queries remain observable.
- [Encoding](Encoding.lean) independently converts valid vector JSON into the
  existing canonical logical-tree encoding. It is a fixture CLI, not a typed
  protocol reader or an untrusted JSON admission boundary.

The [public guide](../../../docs/guides/mathematical-protocols.md) explains the
architecture and the [support map](../../SUPPORT.md#shared-mathematical-protocols)
separates these results from the broader profile.
