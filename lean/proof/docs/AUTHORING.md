# Authoring with the shared program/proof core

Start from a fixed request and a Process client. A request fixes the complete experiment,
admissible environments, negative relation or accepting observation, and quantitative
bound. Evidence supplies a proof of that meaning; it cannot select a weaker one.

The checked small clients are mathematical models, not imported zkc artifacts:

| Client | What differs | Reused path |
|---|---|---|
| `AdaptiveChecks` | History-dependent guesses, arbitrary rounds and nested batches | Upper/lower contracts, iteration, installation, root closure |
| `SharedState` | Persistent shared challenge, non-injective audit representation, compound services | Local representation, complete initial coupling, contextual substitution, roots |
| `OracleProximity` | Fixed oracle table, fresh sampled indices and an ordered query log | The same contracts and roots; exact repeated-query probability |
| `ServiceDecoding` | Different reply interfaces; malformed random word stops | One local service installation, arbitrary nested contexts, both event directions |
| `InterpretationModels` | Exact decoder, adaptive second call, nested batches | Deterministic interpretation and composition |
| `ExecutionControls` | Primitive/process stops, prefixes and mixed initial laws | Public full-execution semantics |

## Mathematics stays local

An operation specification consumes a potential for each full reply and reached state.
A local sampling law proves its agreement or inequality with the actual primitive kernel.
For a loop, the author supplies an indexed invariant and a body contract; the generic
iteration theorem handles all round counts. If a stopped path is possible, its potential
comparison remains an explicit obligation.

For example, `OracleProximity` uses

```lean
fun round ↦ reward (agreement table ^ (queryCount - round))
```

as a remaining-query potential. The component mathematics is the one-query averaging
identity. The common upper and lower roots prove exact acceptance probability
`agreement table ^ queryCount`. Canonical soundness and completeness follow for every
fixed public table. Neither a source visitor nor a separate probability evaluator is
written for this model.

`AdaptiveChecks` uses the same rules with a history-dependent strategy and nested loops.
`SharedState` proves that checking the same hidden bit twice does not give two independent
factors: its negative control refutes that proposed product bound.

## Install once, reuse in every caller

Use `Installation.reflexive` when the semantics already agree. Otherwise use
`Installation.ofMap` with a meaningful state/history representation, its local full-law
commutation equation, and the entire initial-law pushforward. Erasing an audit counter
is allowed only when those equations preserve the requested behavior and observation.

For a different operation interface, fix an `OperationInterpretation I J`: each logical
operation is a lower-level Process. `ServiceInstallation.ofMap` turns its local full-law
equations into an installation. `event_le` and `event_ge` transport arbitrary measurable
events through every caller. The proof uses `Internal.encode_interpret` and upstream
`FreeM.runKernel_liftM` once; an author does not recurse over the caller.

`ServiceDecoding` installs a word decoder, including its refused-input branch, once.
The same declaration proves equality of every full-record event for callers with two
separate uses and arbitrarily nested batches. State and event history are not reset at
component boundaries.

The deterministic `InterpretationContract` provides the corresponding exact laws,
including composition through an intermediate representation. Its negative controls
reject accepting malformed input and erasing an observable event.

## Close the requested property

`UpperEvidence` and `LowerEvidence` collect the fixed subject, local installation,
mathematical contract, initial budget and property-directed terminal implication.
Their `.establish` theorems close the request. No local-installation field asks for the
whole requested security theorem.

A security-changing step has a separate `UpperTransfer` or `LowerTransfer` with a proved
reduction and explicit loss. Losses compose by theorem. They are not guessed from shared
challenge syntax or component names.

Extraction and simulation use request-fixed Process algorithms, typed public input and
service access. Their mathematics, view relation and weighted-call bound remain explicit.
The existing profile controls check stops, observation differences, algorithm selection,
access and budgets. See [CLAIMS.md](CLAIMS.md).

## What remains authored and what is automatic

Framework theorems already handle execution, normalization, full-outcome substitution,
local-to-global transport, sequencing, branch and finite/nested iteration. The mathematical
library or companion supplies new algebra, meaningful representation relations, loop
invariants, terminal observations and security premises.

In these packages those theorems are applied using ordinary Lean code. Automatic discovery
of component rules, Region traversal, generated companion stubs and a common proof builder
belong to Package 3. Their implementation is not claimed here. They must later produce
these same checked propositions, without introducing a second semantics or a per-protocol
visitor.
