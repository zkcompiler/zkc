# F2-O4: entry contract for the first Fiat--Shamir provider interpretation

> **Kind:** entry contract (formal-assurance research, provider correspondence)
> **State:** Proposed 2026-09-04; the executor contract
> ([`f0v3c-fs-runtime-entry-contract.md`](f0v3c-fs-runtime-entry-contract.md))
> has delivered the finite subject, its frozen runs, and its derivation
> table, with one owner gap (the application-domain declaration body) since
> closed on the canonical-framed page; the lane re-admits that subject as
> owner-determined and adds the one-shot construction before the
> correspondence.
> **Authority:** None. A contract fixes what a lane must deliver and what a
> result may claim; it changes no owner page.

## 1. The question

Does ArkLib's Fiat--Shamir transform of the reduction the ArkLib round
generated operationally correspond to the admitted finite canonical-framed
FS Protocol, run for run, when ArkLib's abstract challenge oracle is
instantiated by the migrated construction's exact derivation function?

## 2. Why the oracle is instantiated rather than matched

ArkLib's transform (`ArkLib/OracleReduction/FiatShamir/Basic.lean`) derives
the challenge of round `j` by querying `fsChallengeOracle` at the point
`(j, statement, messages before j)`; the oracle is abstract, and the
transform's verifier re-queries the same points from the proof. The migrated
construction derives the same challenge as a total function of the same
data: the application domain and construction identity are fixed by the
construction, the frames absorb the statement and the prior messages in a
fixed order, and the draw loop is deterministic. The page states that the
transcript absorbs nothing else. So the derivation is a function
`D(challenge, statement, prefix) -> value | exhaustion`, and instantiating
ArkLib's oracle with `D` makes the two sides compute the same challenges by
construction, which is not the claim. The claim is what remains once the
oracle is shared:

- ArkLib queries the oracle at exactly the points the construction derives
  from, no others and no fewer, with `prefix` equal to the zkc transcript
  prefix under the schedule and value maps (this is where a framing
  difference would show: a provider that hashed a different prefix would
  query a different point);
- the transform's prover and verifier agree with the zkc executor's run and
  the zkc verifier's decision on every input of the finite domain;
- exhaustion, where `D` has no value, is a lane ArkLib does not model, and
  the declaration says so.

`D` comes from the F0-V3C derivation table and is authenticated against the
frozen runs; it is an input of this package, pinned by content, never
recomputed by the provider side.

## 3. The provider, the subject, and the carrier

- Provider: ArkLib at the revision the ArkLib round pinned, the same
  toolchain and build; the generated reduction of that round transformed by
  `Reduction.fiatShamir`, with `fsChallengeOracle` implemented by a total
  table lookup over `D` restricted to the finite domain and refusing any
  point outside it.
- Subject: an FS Protocol of the F0-V3C executor over the finite Schnorr
  Core with a one-shot challenge rule (`maximum_draws` one and an acceptance
  algorithm that always returns true), added to that package as a second
  admitted construction, so that sampling exhaustion is unreachable and every
  run ends in a lane the provider models. The executor's first construction
  retries and measured six exhaustion runs on the domain; those runs are
  reported by count as occurrences of the unmodelled interpretation-failure
  lane and are outside the affirmative claim, which is the honest reading of
  the carrier packet's rule for a provider whose oracle is total.
- Carrier: the transformed reduction's verdict, `Option Unit` once the
  option layer is run, with the declaration derived from the execution
  model as the ArkLib round did (`modelled_lanes` at least `Accepted` and
  `Rejected`); the canonical-framed profile's partition has six lanes, and
  `InterpretationFailed` is `Unmodelled` unless the lane can show a
  provider construct that produces it, which the abstract oracle cannot.

## 4. The correspondence relation

1. **Schedule.** The transformed protocol's message sequence maps totally,
   injectively, and in order to the source occurrences; the challenge
   occurrence maps to the oracle query, not to a message.
2. **Values.** Every mapped source value carrier agrees with the ArkLib
   type, including the challenge type the oracle answers with.
3. **Oracle points.** For every run, the sequence of oracle query points
   ArkLib's prover and verifier issue equals the sequence of
   `(challenge, statement, prefix)` points the zkc executor derives from,
   under the maps; a superfluous, missing, or differently framed query is a
   negative finding, not a `CannotAnswer`.
4. **Checks and terminals.** The verifier's computation is the M2 denotation
   of the Check term applied to the provider's values together with the
   re-derived challenge; the provider's outcome equals the image of the
   source lane under the declared map on every run; a lane that occurs on
   the domain has an image; exhaustion runs, if F0-V3C measured any, are
   the unmodelled lane and are reported by count.
5. **Traces.** The proof the transform emits and the zkc completed record
   agree step by step under the maps, receipts excluded (a receipt is a
   zkc-side artifact of the derivation, not a provider observable).

## 5. Independence, trust, and acceptance

The generator may be any program; nothing it emits is trusted. The checker
authenticates the F0-V3C table against the frozen runs, re-admits the Core
and FS Protocol cold, elaborates the transformed module under the pinned
ArkLib, executes every run with the table-backed oracle, and compares. The
certificate pins owner pages, manifests, and this package's inputs (the
F0-V3C table and vectors included, by content) and no research note or
sibling findings. Residual trust: the Lean kernel, ArkLib's and VCVio's
oracle-computation semantics, the finite domain, the checker adapter.

`Affirmative` only when all five clauses hold on the whole finite domain and
the declaration is determinate; `CannotAnswer` with the exact clause
otherwise. A passing result is the first provider correspondence for a
Fiat--Shamir Protocol under the migrated text. It establishes no security of
the transition suite or of the transform, no theorem, no random-oracle
result, and nothing about the duplex-sponge profile, which gets its own
contract against `Reduction.duplexSpongeFiatShamir` once a duplex executor
exists.
