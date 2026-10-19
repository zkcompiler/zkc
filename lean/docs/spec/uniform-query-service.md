# Uniform queries for structured participants

`ZkcSecurity.VCVio.StructuredUniform` defines a concrete optional
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

## General-count process transport

`ZkcSecurity.Examples.CausalSumcheck.Iteration` imports the shared module
`ZkcExamples.Structured.SumcheckVerifierProcess` and its
`SumcheckVerifierLaws.roundPresent` definition. It constructs a `Causal.Strategy` from the
two actual qualified receives and the actual send. HIGH receives LOW's updated
state and returns its own reply. The guard precedes service preparation and
sampling. The source normal form appends the sampled value and interpolates
using those two replies; no second round process or evaluator is defined.

`repeat_distribution_of_queryLaw` proves equality of full execution
distributions for arbitrary counts, starting points, claims and states. Its
only provider premise is a query law at every state. All continuation
substitutions use invariant `True`; no reachable-only obligation remains.
`repeat_uniform_distribution` discharges that local law with the constructor.

`repeat_uniform_publicTable_soundness` and
`repeat_uniform_residual_soundness` specialize the stop-aware causal bounds to
this shared process, installing the singleton route internally. They bound
the decoded public-table observation and the external original-table residual
observation by `n / |F|`. Callbacks and network actions may stop; the mass is
unconditional. The residual process has no Boolean terminal checker.

## Actual imported roots

`Examples.CausalSumcheck.SourceVerifier` composes the process theorems with the
source owner's callback, root-input, count-admission, output and terminal laws.
Its subjects are `SumcheckSourceViews.imported.program` and
`SumcheckReduceViews.imported.program`, retaining admission of each complete
exported snapshot. `source_present` and `reduction_present` are exact process
equations, including final output conversion and every earlier interaction or
stop. Their observation equations require no provider premise.

`source_returned_true_bound` bounds the unconditional mass of an actual present
`true` verifier result by `n / |F|`. It takes the original raw verifier vector,
its decoding as a table of dimension `n`, a claim different from that vector's
sum. The bound is nontrivial up to `n ≤ 2`, the exported maximum; for `n > 2`
the source refuses and contributes zero mass. The checked
terminal decision includes both
`point.length = n` and table extension equality. A padded coordinate conversion
alone is insufficient. Decoding and the admitted count discharge raw-vector
representability internally; successful iteration supplies the point-length
fact used by the actual source checker law.

`reduction_residual_bound` bounds the unconditional residual-observation mass
by `n / |F|` for an external original table of dimension `remaining + n`.
The bound is nontrivial up to four rounds, the exported maximum; above four
the root refuses and contributes zero mass. Its initial claim differs from that table's Boolean sum.
The observer reads the original verifier point/claim outputs. Prover vector and
dimension inputs remain arbitrary and optional, with no equality to the external
table. Reduction has no Boolean checker; this event is not acceptance.

Both headline bounds specialize the actual root to the empty parent context,
verifier role `1`, and peer `0`. The shared-process transport supports arbitrary
protocol contexts and role mappings. The source owner also provides a contextual
root equation; this package does not generalize its headline bounds to every
root context.

Both bounds install the actual qualified child query route internally and
quantify over arbitrary network behavior, resource/log callbacks and initial
states. No honesty, local query law, route membership, checker equation,
whole-run distribution equality or reachable-state premise is exposed. The
source equations retain missing inputs, malformed checks, count refusal and
overflow behavior. The headline bounds use present V inputs and internally
discharge count admission; they do not make excess counts executable.

## Probability interpretation

The owning optional manifests pin VCVio to
`d606eab018ab87bf4a0a6ac7b6d2da4fedfa53b0`.
In `VCVio/OracleComp/Constructions/SampleableType/Basic.lean`, the
`SampleableType.evalDist_selectElem_eq_uniform` field certifies the sampler's
uniform measure; `SampleableType.evalDist_uniformSample` exports that law.
`SampleableType/NativeMeasure.lean` derives singleton and finite-event counting
laws. The [dependency baseline](../dependencies.md) records the tested pins.

A symbolic service name does not confer its law on another handler.
Imported-root bounds add exact exported-snapshot association and source
equations to this service law.
