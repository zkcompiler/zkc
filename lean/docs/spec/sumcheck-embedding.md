# Sumcheck with an embedded base table

`Zkc.Polynomial.Multilinear.Embedding` transports the existing ordered Boolean
table semantics along an explicit ring homomorphism `e : B →+* E`. It proves
that Boolean summation and evaluation at embedded base points commute with
`e`, and that first-coordinate and ordered-prefix restriction commute at
embedded base points. For arbitrary extension points, the operation is instead
to embed every table entry and then restrict in `E`. The list decoding and
residual evaluation laws identify this operation with the existing
`fixPrefix` and `extension`; they never pretend that an extension challenge is
a base-field element.

`ZkcSecurity.Families.Sumcheck.EmbeddingPrefix.State` retains the original
`List B`, an ordered `List E` challenge prefix, the current `E` scalar and an
arbitrary caller frame. At remaining dimension `n`, its shape is exactly
`original.length = 2^(n + point.length)`. Its reference entries are
`restrictPrefixValues (original.map e) point`. Appending every extension
challenge commutes with restriction for every received endpoint pair,
including false claims. The representation has no truth-based admission
condition. The terminal sum is evaluation of the embedded original table at
the actual prefix.

The KoalaBear client uses the existing CompPoly base field of order
`q = 2130706433`, its proved octic extension and the existing constant
coefficient embedding. No field construction or axiom is added here. The
selected ideal draw has the octic carrier, whose cardinality is `q^8`.
`KoalaBearSumcheckSampling.sampling` proves the exact decoder pushforward and
the degree-one conditional charge `1/q^8` at arbitrary reached histories.
This is the mathematical ideal sampler, not a native byte sampling theorem.

`KoalaBearSumcheckSource` supplies checked typed source and exact helper-table
laws to the existing `Bindings.Template` machinery. The verifier receives two
octic endpoints, checks their sum, draws and delivers an octic challenge and
returns the affine residual together with that challenge. Its source inputs
are a scalar and service handle; it cannot inspect the reference table.
The producer embeds two actual base inputs and emits the two endpoint
packets. Missing returned fields stop the logical readback as incomplete.
Swapping the returned fields changes the readback even though their nominal
types agree.

`KoalaBearSumcheck.binding` identifies the entire verifier source computation
followed by logical readback with one round of the existing Sumcheck family.
Both `Contract.soundness` and `Contract.honest` consume this same equation.
The family client handles one residual round at every dimension; a concrete
one-dimensional client proves honest success from the checked producer's
actual emitted packets, consuming both packets and its one coin. The honest
operational handler uses only packets and coins. Its reference table appears
only in the proof invariant. `terminal_yes_iff` identifies terminal truth
with extension evaluation of a caller-supplied decoded base table.

This client is explicitly family scoped. Its indexed state requires exact
shape; it is not a total raw-root admission theorem. The strict list decoder
rejects an incorrectly sized original table. The accompanying `.zkc` fixture
passes native language checking, but the typed source body is independently
constructed. Connecting a native exported snapshot to this body, composing
the generic root and discharging a terminal opening remain integration
obligations. Neither nominal domain names nor the native fixture's successful
language check establish that correspondence.

`TestsSecurity.KoalaBearSumcheck` checks a challenge outside the embedded base
field, source-producer honest execution, the exact denominator, distinct
carrier and nominal identities, a shifted embedding, invalid shape, absent
or exchanged readback fields, and an initially equal view whose update fails
to commute. It also prints the axiom dependencies of the property consumers
and cardinality theorem.
