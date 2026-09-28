# Mathematical protocol fixtures

Sigma uses the canonical admitted mathematical source and the installed BLS
carriers. The remaining small examples still exercise the earlier independent
model. From `formal/`:

```sh
lake build Examples.Mathematical.Formation Examples.Mathematical.Encoding
```

- [Sigma](Sigma.lean) exports the canonical authored source, executable admission
  and actual stored entry meaning. Its [prefix laws](SigmaPrefix.lean) prove
  fresh reception and query/pure/send sequencing using the admitted body, actual
  entry arguments and installed scale identity. The source encoding is compared
  with fresh frontend output. Standalone honest algebra uses the actual scalar
  modulus and curve subgroup; full trace honesty and security remain open.
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
