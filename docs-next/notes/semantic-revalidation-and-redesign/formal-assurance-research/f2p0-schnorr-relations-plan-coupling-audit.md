# F2-P0 Schnorr Relations--Plan Coupling Audit

> **Kind:** Temporary bounded audit of the Relations--Plan property-premise seam
> **State:** `CannotAnswer/F2P0-C-EXACT-COUPLING-UNDERDETERMINED`
> at cutoff `de49641aba0086b1e3f7eff48f5276ffd8af2845`
> **Authority:** None. This note and its executable package change no owner
> semantics, subject identity, Plan, relation, provider term, Analysis result,
> or roadmap selection.
> **Executable evidence:**
> [`evaluation/formal-schnorr-relations-plan-f2p0`](../../../../evaluation/formal-schnorr-relations-plan-f2p0/README.md)

## 1. Exact question and answer

F2-O0 found that the F1-R1B Schnorr target's six views have no coordinate for
five VCVio property premises: relation predicate, witness type, Prover private
state type, honest commit, and honest respond. This audit asks whether the
current Relations and Plan contracts alone can supply an exact finite
definition/model/instance and strategy-role coupling for that target.

There are two answers at different levels:

1. **Conditional structural expressiveness: yes.** Separately authored and
   admitted objects can be attached through `ProtocolRelationBinding`,
   `PlanRealizes`, `PlanWitnessSurface`, and `PlanWitnessBinding` without an
   ownership cycle.
2. **Exact reconstruction from the current target and contracts: no.** The
   contracts specify carriers and checked attachment judgments. They do not
   select the relation language or payload, semantic evaluator, per-invocation
   public values, Plan private material, randomness, state, or recipes.

The second is the question's operative result. Missing operands are retained
as `CannotAnswer`; the verifier equation and role-site names do not fill them.

## 2. Contract route

The permitted route is:

```text
Definition -> Interface -> SemanticModel
                      \---> Instance

Protocol -> ProtocolRelationBinding -> Interface

Plan -> PlanRealizes -> PlanStrategyStep
  \---> PlanWitnessSurface -> PlanWitnessBinding -> Interface
```

The two attachment paths are independent by design. `ProtocolRelationBinding`
reads no Plan. `PlanWitnessBinding` reads the source-ID-free witness surface,
not the Plan identity or its private source map. They may be retained together
by a checked aggregate without creating a new semantic owner.

The exact clauses are frozen in the package contract ledger:

- Relations definition/interface/instance/model/satisfaction: relation model
  lines 562--584, 672--716, 759--810, 847--937, and 1007--1070;
- independent attachment cut: Relations README lines 74--86;
- Protocol binding: relation model lines 1607--1688;
- Plan witness binding: relation model lines 1917--1962;
- Plan subject, recipes, and `PlanRealizes`: Plan contract lines 687--753 and
  853--1029;
- `PlanRealizes` non-claims: Plan contract lines 1184--1189;
- adapter/private-state execution: Plan contract lines 1267--1378; and
- witness surface: Plan contract lines 1623--1688.

## 3. Premise result

| Premise | Existing F1 role site | Coordinate if an exact bundle is later supplied | Current result and residual |
|---|---|---|---|
| relation predicate | Statement binding 0 names only the public side | semantic-model evaluator and occurrence-local satisfaction | `CannotAnswer`; no selected model, totality basis, provider translation, or acceptance correspondence |
| witness type | none | Interface private-witness type plus Plan-witness edge | `CannotAnswer`; no admitted Interface or binding |
| Prover private state | none | Plan persistent-state vector and adapter state | `CannotAnswer`; no admitted Plan or checked provider-state projection |
| honest commit | decision 0 only | decision recipe 0 and its exact strategy step | `CannotAnswer`; no recipe and no relation-relative honesty judgment |
| honest respond | decision 2 only | decision recipe 2 and its exact strategy step | `CannotAnswer`; no recipe and no relation-relative honesty judgment |

All five therefore have a contract-defined **destination family**. Commit and
respond additionally have current **role-site coordinates**. None has a
current **premise coordinate**. After authoring the missing operands, owner-
local coordinates would exist, but three separate obligations would remain:

- the Relations satisfaction machine is partial until a separate termination
  basis justifies a total provider Boolean;
- the Plan adapter's private state is richer than a bare Plan state vector, so
  a provider `PrvState` representation needs a checked translation; and
- `CheckedPlanRealizes` establishes structural dataflow and state closure, not
  relation-relative honesty or completeness.

## 4. Two reconstructions and non-uniqueness

The forward path admits the typed F1 Core and Fresh Protocol, reads the
Statement and decision sites, and follows the contract constructors. The
reverse path uses the B1 clean-room view compiler, independently decodes the
same role sites, and interprets all 81 values of the finite verifier term. The
paths share no reconstruction code and agree on the complete report.

Both enumerate two deliberately non-authoritative completions of
`z = a + c*y mod 3`:

- `x : Z3`, relation `y=x`, nonce state `r`, `a=r`, `z=r+c*x`: 27/27 honest
  runs accept; and
- `unit : Unit`, always-true relation, unit state, `a=0`, `z=c*y`: 9/9 honest
  runs accept.

All 36 plus-one response controls reject. The two completions disagree on all
five missing premises. They are ambiguity witnesses only, not candidate target
semantics. Their coexistence proves that neither verifier acceptance nor the
generic contract shape uniquely reconstructs the missing relation and Plan.

## 5. Disposition

No owner-page change is proposed. The existing contracts already state the
independent dependency cut and their non-claims. Consequently this result does
not create a delta-ledger proposal block.

A later lane may author one or more exact relation and Plan candidates and ask
for checked correspondence or applicability. That would add named operands
and evidence; it must not reinterpret this `CannotAnswer` as an implicit
selection or treat either finite ambiguity witness as the intended Schnorr
relation.

## 6. Non-claims

The 30 findings are bounded evidence over one finite target, 18 pinned contract
ranges, and two reconstruction paths. They do not admit a relation, model,
instance, Plan, binding, satisfaction result, provider translation, theorem
application, completeness result, or cryptographic property. They do not show
that the contract vocabulary is complete for every protocol family or that a
future authored bundle will satisfy its admission checks.
