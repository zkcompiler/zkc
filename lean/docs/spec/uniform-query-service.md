# Uniform queries for structured participants

`ZkcSecurity.ProgramLogic.Oracle.StructuredUniform` defines a concrete optional
`ProbComp` handler at the structured participant boundary. It uses
`PIR.MonadHandler`, `PIR.Execution` and `VCVio.Execution.freshQuery`; generic
execution semantics are independent of this source interface. This is a
service construction in the independent mathematical model: native RNG,
provider dispatch, exporter/frontend correctness, concurrent scheduling and
Fiat–Shamir correspondence are separate claims.

## Constructor and exact route selection

`withUniformQueries network ports before after` delegates every receive and
send to `network`, preserving its actual replies, state, events and stops.
The network can randomize, adapt to its entire state, and return arbitrary
typed values. Its query branch is never called.

Each configured port is a tuple of qualified action site, nominal field domain,
and actual service handle. A matching query executes `freshQuery` with the
callbacks selected by that tuple. An unmatched query returns `stopped refused`
with the unchanged state and no events. All field domains have the
structured assignment `F`; this constructor does not introduce heterogeneous
field interpretations. Tuple membership selects a single implementation;
list order or duplicates cannot create competing query clauses.

`Examples.CausalSumcheck.UniformService.queryKey context handle` uses the
source-owned `SumcheckVerifierLaws.challengeSite` in the actual child context,
retains domain `bls12-381.fr`, and includes the handle. The
context describes an invocation; it is not reconstructed from mutable handler
state. Configuring a port does not establish a source invocation equation.

## Full execution law

`withUniformQueries_query` proves, for every network, initial state and pair of
callbacks, equality between the actual query action's `runM` and `freshQuery`.
The result type is `ProbComp (PIR.Execution S E F)`: outcome, final state and
ordered events all participate in the equality. The theorem has no honesty,
reachability, or successful-callback premise. `withUniformQueries_queryKey`
discharges membership for a singleton configured route. The receive/send and
unconfigured-route theorems give their corresponding exact equations.

The computation first runs `before key`. If that returns, it draws `$ᵗ F`,
then runs `after key r`. If that returns, the query returns exactly `r` with
the callback's state and `before.events ++ after.events`. A stop in either
callback retains that callback's complete record and every preceding event.
A before stop suppresses the designated draw; an after stop retains its effects
but returns no query value. Enclosing `followM` preserves the earlier prefix.

Callbacks may themselves use randomness, stop, and record events. They receive
no future designated draw before it occurs. Each invocation samples anew,
including repeated calls at one site and handle. Shared handles may share all
of `S`. No survival normalization, capacity assumption, or retry occurs.
Sampling does not invent a logging event; such an event belongs to a callback.

## Source connection boundary

The previous generated Sumcheck process transport is retired. The service laws
above remain available to common construction. Installing them at an actual
source call requires its checked service identity, arguments, reached state and
continuation; a distribution name alone does not establish that association.

## Probability interpretation

The owning optional manifests select the exact VCVio revision recorded in the
[dependency baseline](../dependencies.md).
In `VCVio/OracleComp/Constructions/SampleableType/Basic.lean`, the
`SampleableType.evalDist_selectElem_eq_uniform` field certifies the sampler's
uniform measure; `SampleableType.evalDist_uniformSample` exports that law.
`SampleableType/Measure.lean` derives singleton and finite-event counting laws.

A symbolic service name does not confer its law on another handler.
Imported-root bounds add exact exported-snapshot association and source
equations to this service law.
