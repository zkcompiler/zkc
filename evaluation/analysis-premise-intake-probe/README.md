# Analysis named-premise intake probe

This package asks one exact question:

> Can a closed Analysis-owned named-premise catalog and intake operation make
> every required assumption explicit and identity-bearing for the finite
> Schnorr subject while failing closed on omission, extra keys, coordinate
> substitution, or any model-scope mismatch?

The frozen answer is
`Affirmative/API-A-FINITE-PREMISE-INTAKE` for the proposal-local finite model.

Run the standard-library-only check from the repository root:

```sh
python3 -B evaluation/analysis-premise-intake-probe/run.py --check
```

## Closed finite model

[`fixture.json`](fixture.json) contains twelve named premises of ten closed kinds.
Every premise has exactly these identity-bearing fields:

```text
kind
coordinate
bound_model_or_hypothesis
source
evidence_depth
model_scope
```

The evidence depths follow the existing research meanings: `T1` is a
source-grounded boundary mapping, `T2` adds a complete typed constructive
binding, and `T3` adds frozen executable falsification. A depth labels the
available evidence for the premise record; it does not establish the premise's
truth. Seven proposal or source-mapping entries are `T1`; the five exact finite
Schnorr relation and Plan coordinates have `T3` coordinate evidence. There is
no `T2` entry in this fixture.

The concrete catalog contains:

- one Fresh distribution hypothesis bound to the subject's exact nominal
  `pir.public-coin-law` declaration coordinate;
- sampler-adequacy and exact classical oracle-process hypotheses bound to one
  Analysis family coordinate;
- three provider maps over the same five-lane Fresh outcome partition and one
  separate operational-completion premise;
- the relation predicate and witness-type coordinates; and
- the Prover private-state, honest-commit, and honest-respond coordinates.

The `model_scope` carrier has the four owner cases `FreshChallengeOnly`,
`OracleModelOnly`, `ExactSubjectsOnly`, and `RebindRequired`. The complete lane
vocabulary has six cases. The selected Fresh Protocol's
partition has five because `InterpretationFailed` is profile-qualified and is
not available for this Fresh subject. The fixture represents that partition as
`ProtocolOutcomeLane(subject.fresh_protocol_id)` and requires each provider map
to be total in exact lane order. A map has `Image(value)` exactly for a lane in
the provider declaration's `modelled_lanes` and `Unmodelled` otherwise. The
option-layer and tagged providers model all five lanes. The Boolean provider
models only Accepted and Rejected, so it does not collapse operational
noncompletion to `false`. The owner profile currently publishes no provider
declaration, so these provider records are proposal-only and cannot form owner
premises in the shared Analysis model.

## Intake law exercised

Each question declares slots by exact `(slot, kind, coordinate)`. Intake binds
every slot to one catalog premise, authenticates its kind and coordinate, and
places the complete sorted premise-ID set in both the hypothesis set and the
judgment identity.

The probe checks six complete intakes: the six-premise relation-bound Fresh
Schnorr case, Fresh challenge intake, Fiat--Shamir challenge intake, two
separate provider-map cases, and one operational-completion case. It then
establishes the intended failure partition:

- deleting each of the six Fresh Schnorr bindings separately returns
  `CannotAnswer/API-C-MISSING-PREMISE`;
- replacing the public-coin premise by one bound to declaration ordinal one
  returns `Refused/API-R-PREMISE-COORDINATE`;
- adding one unrequested binding returns
  `Malformed/API-M-EXTRA-PREMISE`;
- mismatching each of the four model-scope variants returns
  `Refused/API-R-MODEL-SCOPE` before a judgment identity forms;
- Fresh names one distribution premise while Fiat--Shamir names sampler and
  oracle-process premises over the identical Core; and
- the option-layer, Boolean, and tagged maps over the same partition produce
  three different premise identities, and the two map-only cases produce
  different judgment identities;
- sending operational noncompletion to the Boolean image is
  `Malformed/API-M-PROVIDER-LANE-IMAGE`; and
- the operational-completion premise remains identity-distinct from either
  provider map.

[`model.py`](model.py) uses typed immutable premise records. The separately
structured [`independent.py`](independent.py) validates raw dictionaries and
reconstructs the same identities and outcomes without importing the typed
path. [`run.py`](run.py) requires exact agreement before comparing the report
with [`expected-findings.json`](expected-findings.json).

## What a pass establishes

A pass establishes only that this finite proposal is closed over its declared
schema and enums, that both implementations reconstruct the same catalog and
intake results, and that the named positive and negative controls have the
frozen outcomes.

## What a pass does not establish

A pass proves no theorem and establishes no protocol or cryptographic
property. It does not prove any named premise, transport a premise to another
model or subject set, validate a provider implementation, or publish/adopt any
Analysis or PIR owner text or profile. In particular, the proposal-only
provider declarations do not fill the owner profile's currently empty provider
catalog. The finite IDs are comparison keys, not owner authority; the fixture's
profile-qualified partition is not runtime or provider validation.
