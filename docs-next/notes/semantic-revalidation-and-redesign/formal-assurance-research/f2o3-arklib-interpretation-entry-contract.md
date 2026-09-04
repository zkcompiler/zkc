# F2-O3: entry contract for the second provider interpretation, in ArkLib

> **Kind:** entry contract (formal-assurance research, provider correspondence)
> **State:** Proposed 2026-09-03 for the lane that follows the second VCVio
> round; it applies the restated terminal clause of
> [`f2o2-provider-interpretation-entry-contract.md`](f2o2-provider-interpretation-entry-contract.md)
> to a second formal system whose outcome carrier has a different shape.
> **Authority:** None. A contract fixes what a lane must deliver and what a
> result may claim; it changes no owner page.
> **First attempt:** run 2026-09-03 as
> [`f2o3-arklib-interpretation.md`](f2o3-arklib-interpretation.md); aggregate
> `Affirmative/F2O3-A-FINITE-CORRESPONDENCE` on all five clauses over the
> complete finite domain. The attempt refused this contract's Section 3
> premise that two producers reach the empty verdict
> (`Refused/F2O3-R-NO-PROVER-FAILURE-PRODUCER`): at the pinned revision the
> prover's run is lifted from the failure-free base oracle computation, so
> only verifier rejection produces `none`. Section 3 is corrected below; the
> declaration it derived is `Option Unit` with modelled lanes `Accepted` and
> `Rejected`, and the provider-map premise waits on the owner's publication.

## 1. The question

Does an ArkLib reduction generated from the migrated Schnorr formal source
operationally correspond to the admitted finite Schnorr Fresh Protocol, and
which lanes of the PIR outcome partition does ArkLib's execution model
realize?

The first half repeats the VCVio question for a provider whose verifier does
not return a Boolean. The second half is the reason to run it: the
provider-carrier decision packet
([`f2o2-provider-carrier-decision-2026-09-03.md`](f2o2-provider-carrier-decision-2026-09-03.md))
made a provider declare the lanes its execution model can end in, and VCVio
tested only the case where a Boolean models `Accepted` and `Rejected`. ArkLib
tests a carrier with an empty case that two producers reach.

## 2. The provider

ArkLib at revision `fad5cbf808774838924dc8273715724c6a6caa1f`, the revision the
formalization-receipt audit already pins, built under `leanprover/lean4:v4.31.0`
at `/home/wonjae/code/ArkLib` with its own VCVio pin (`cbd4144b`), whose
`OracleComp` is again a free monad without failure of its own. The relevant
definitions are in `ArkLib/OracleReduction/`:

- `ProtocolSpec n = { dir : Fin n -> Direction, Type : Fin n -> Type }` and
  `FullTranscript pSpec := (i : Fin n) -> pSpec.Type i`;
- `Prover` as a state machine over rounds with input and output, `Verifier`
  with `verify : StmtIn -> FullTranscript pSpec -> OptionT (OracleComp oSpec) StmtOut`,
  and `Reduction` pairing them;
- `Reduction.run` in `OptionT (OracleComp (oSpec + [pSpec.Challenge]))`,
  drawing challenges from the challenge oracle, and `Reduction.verdict`
  projecting the verifier's output statement.

The generated artifact is a `Reduction` for the three-step specification
`[P_to_V commitment, V_to_P challenge, P_to_V response]` with the statement
type as `StmtIn`, the witness type as `WitIn`, and `Unit` as `StmtOut` and
`WitOut`: the prover's rounds from the Plan's two recipes with the nonce as
persistent state, the verifier from the Check term whose denotation M2
proved equal to `z = a + c . y` in the field of three elements, and the
challenge as the uniform draw the challenge oracle provides, which is what
the Fresh distribution premise binds to the public-coin-law coordinate.

## 3. The carrier question this contract must settle

`Reduction.verdict` returns `Option Unit` once the option layer is run. Its
`none` is produced by the verifier's failure, which is rejection. This
contract first supposed that a failure of the prover's run could produce it
too, because `Reduction.run` sequences the prover inside the same option
layer; the first attempt showed that at the pinned revision `Prover.run` is
lifted from the failure-free base oracle computation and cannot fail, so the
verdict has one producer of `none`. The question the lane had to answer
remains the right one for any provider whose verdict is an option: decide
the declaration from the execution model rather than from the verdict type.

- If the generated prover is total on the finite domain and the lane
  executes prover and verifier separately (`Prover.run`, then
  `Verifier.run` on the produced transcript), the two producers of `none`
  are distinguishable and the declaration may name `StrategyStopped` as a
  modelled lane with the prover's failure as its image; the honest Plan
  never reaches it, so it never occurs on the domain.
- If the lane keeps `Reduction.verdict` as the carrier, `none` has two
  producers and the declaration may model only `Accepted` and `Rejected`,
  with the prover's totality stated as the reason the second producer is
  unreachable; that totality is then a premise, named in the note.

Either choice is admissible under the packet's rule; a declaration that
lists a lane whose image another producer can also reach is not. The lane
records which it chose and why, and the proposed ArkLib declaration
(system, source pin, toolchain, carrier schema, `modelled_lanes`, and the
five-lane map) in the shape of the packet's Section 4a.

## 4. The correspondence relation

The five clauses of the VCVio contract apply unchanged, read against ArkLib's
types:

1. **Schedule.** The `ProtocolSpec` directions and the prover's rounds map
   totally, injectively, and in order to the source occurrences, with exactly
   the two prover decisions of the Plan as prover rounds.
2. **Values.** Every mapped source value carrier agrees with the step's
   ArkLib type, including the challenge type the challenge oracle draws from.
3. **Checks and guards.** The verifier's computation is the M2 denotation of
   the Check term applied to the provider's values; equality is checked on
   every input of the finite domain.
4. **Terminals.** For every run of the finite domain, the provider's outcome
   equals the image, under the declared map, of the lane in which the source
   run ends; a lane that occurs on the domain has an image; a lane that
   occurs on no run carries `Unmodelled` or an image the declaration
   justifies by naming its producer.
5. **Traces.** The `FullTranscript` and the `ExecutionView`'s completed
   record agree step by step under the maps above.

## 5. Independence and trust

The generator may be any program; nothing it emits is trusted. The checker
re-admits the Core and Protocol through the cold canonical-byte path,
authenticates every pin in the certificate, evaluates the portable Check and
the mechanized first-active terminal independently, elaborates the generated
module under the pinned ArkLib and Lean toolchain, executes every run, and
compares. The residual trust items are the Lean kernel, ArkLib's and VCVio's
`OracleComp` semantics, the finite differential evidence between evaluators,
the Fresh distribution premise, and the unproved checker adapter. The
certificate pins owner pages, manifests, and this package's inputs only; it
pins no research note and no sibling package's findings.

## 6. Acceptance

`Affirmative` only when every clause of Section 4 holds on the whole finite
domain and the declaration of Section 3 is determinate; `CannotAnswer` with
the exact clause otherwise. A passing result establishes operational
correspondence for one subject and one provider and a proposed declaration
for the owner; it establishes no property, theorem applicability, security,
or correspondence for any other subject or provider, and it publishes
nothing. A second provider that fits the packet's rule with a different
carrier shape is evidence for the rule; a provider that does not fit is a
reopening of the packet, recorded as a proposed delta.
