# Decision packet: the provider outcome carrier and the lanes a provider does not model

> **Kind:** decision packet (formal-assurance research, provider correspondence)
> **State:** Proposed 2026-09-03 from the first provider-interpretation attempt
> ([`f2o2-provider-interpretation.md`](f2o2-provider-interpretation.md));
> awaiting the owner's decision on the three items of Section 4.
> **Authority:** None. It proposes an Analysis owner-text change and a
> profile-level declaration; it changes no owner page by itself.

## 1. What the attempt found

The first provider interpretation of the migrated Schnorr source is
affirmative on schedule, values, checks and guards, and traces over its
complete finite domain of 81 runs, and `CannotAnswer` on the terminal clause
with code `F2O2-C-TERMINALS-CLAUSE-4`. The entry contract had declared VCVio's
carrier to be the Boolean the verifier returns and, in the same breath, asked
that every lane the Schnorr Protocol can reach have an image under the
carrier premise, naming `OperationalNoncompletion` among those lanes. A
Boolean has no image for that lane except one it already uses, so the clause
could not be met by the carrier the contract itself specified.

## 2. The facts the decision rests on

- **VCVio's carrier is a bare Boolean.** At the pinned revision
  (`de0a3108140e3e04a7ebf0075aa110b459ee6e8a`, toolchain
  `leanprover/lean4:v4.33.1`) an oracle computation is the free monad of the
  oracle specification's polynomial functor; it has no failure of its own,
  and failure enters only where a module opts into the option transformer.
  The sigma-protocol fields `commit` and `respond` are probabilistic
  computations over that monad and `verify` is a pure Boolean, so the
  generated interaction's outer carrier is exactly `Bool`. Declaring an
  option layer for it would describe a provider that does not exist.
- **The owner page fixes how consumers map the partition.** Section 12.4 of
  `docs-next/pir/interactive-core.md` says that every run ends in exactly one
  lane of `ProtocolOutcomeLane(P)`, that `OperationalNoncompletion` is any
  kernel-qualified noncompletion producing no record, and that a consumer
  needing a Boolean, an option layer, or any other carrier maps the partition
  in its own domain, never reads a verdict as a Boolean, and relabels no lane
  as another. Mapping noncompletion onto the image of `Rejected` relabels a
  lane; the page forbids it.
- **The Analysis premise is total but says nothing about lanes a provider
  lacks.** `AnalysisProviderOutcomeCarrierMapBody` in
  `docs-next/analysis/analysis-model.md` carries a total map from the
  partition into canonical values of a closed carrier. It offers no way to
  say that the provider's model has no outcome for a lane, so the only total
  maps a Boolean admits are relabelings.
- **Noncompletion never occurs on the correspondence domain.** All 81 source
  runs complete; the lane is environmental, present for every Protocol, and
  no property of the Schnorr Protocol's semantics reaches it.

## 3. The reading adopted for the contract

The entry contract now states its terminal clause as agreement with the
image of the source lane: for every run of the domain, the provider's outcome
equals the image of the lane the source run ends in. A lane that occurs on no
run carries the explicit marker `Unmodelled`, or an image that the provider
declaration justifies by naming the construct producing it. The marker is a
fact about the provider's model, consumed by applicability as a premise, not
a correspondence failure. Under that clause the Boolean is adequate for the
Schnorr subject and the attempt's four affirmative clauses stand unchanged.

What the marker costs is exactly where it should: a provider theorem
transports to the union of the lanes whose images lie in the theorem's event.
Soundness needs no more, since its event is `Accepted` alone. Completeness
states that every honest run is accepted, which in the partition also says
that no honest run ends in an unmodelled lane; transporting it therefore
needs a named premise that, in the environment of the transported statement,
the unmodelled lanes have probability zero. That premise is a tenth named
premise kind, and its absence makes completeness `CannotAnswer` in the intake
already designed, rather than silently true.

## 4. The three items to decide

1. **Analysis owner text: the lane image with an `Unmodelled` marker.**
   Change the map's codomain to `ProviderLaneImage<carrier> =
   Image(CanonicalValue<carrier>) | Unmodelled`, keep the map total over the
   partition, and add the law that an `Image` for a lane outside the
   provider's producible outcomes is refused unless the provider declaration
   names the producing construct. Recommended: adopt.
2. **Analysis owner text: a completion premise kind.** Add the named premise
   kind `OperationalCompletion`, whose body binds a Protocol and a provider
   declaration and states that every run in the property's environment ends
   in a lane the provider models; property transport consumes it exactly when
   the property's PIR event is not a union of modelled lanes. Recommended:
   adopt, with the Schnorr completeness page as the first consumer.
3. **Profile-level declaration for VCVio.** Publish, in the cryptographic
   property profile, the provider declaration `{ system: vcvio, source_pin:
   the content digest of the checkout at the revision above, toolchain:
   leanprover/lean4:v4.33.1 }`, the closed carrier `Bool`, and for the Fresh
   Schnorr Protocol the map `Accepted -> Image(true)`, `Rejected ->
   Image(false)`, `Aborted -> Unmodelled`, `StrategyStopped -> Unmodelled`,
   `OperationalNoncompletion -> Unmodelled`. Recommended: adopt once items 1
   and 2 are in the owner text; the source pin is computed at publication,
   not copied from the certificate, which records the revision and the
   generated module's digest only.

## 5. Identity effect and sequencing

Items 1 and 2 change the Analysis kernel and property profiles and therefore
every premise, intake display, and qualified judgment whose identity closes
over them; the Analysis premise review's expectations and the intake probe
change with them. The admitted PIR Core, Protocol, and six view identities do
not change. The change is applied after the second Analysis review round
lands, in the same repair commit, so that the round's pins are not drifted
while it runs.

The provider-interpretation package then needs a second round: its checker
hard-codes the three lanes the old clause named and its frozen findings
record the old aggregate. The expected outcome under the restated clause is
affirmative on all five clauses, with the secondary finding
`F2O2-C-TERMINAL-MECHANIZATION-PENDING` retired once the mechanized
first-active reading is available to it.

## 6. Reversal condition

Withdraw this packet if the PIR owner changes the outcome partition or its
consumer rule, or if the Analysis owner selects a carrier discipline in which
a provider must model every lane; in the latter case VCVio is not a provider
for any Protocol until it carries an option layer, and the packet's item 3
is void.
