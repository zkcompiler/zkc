# F2-P1 Exact Schnorr Relations and Plan Candidates

> **Kind:** Temporary bounded candidate construction for the F1-R1D
> Relations--Plan step
> **State:**
> `CannotAnswer/F2P1-C-SCHNORR-CANDIDATE-BINDING-INCOMPLETE` at cutoff
> `1464c8be0fac7d3dd63909f41e7d5051ddd91f98`
> **Authority:** None. This note and its executable package do not publish or
> modify a relation, Plan, Protocol, provider term, theorem application,
> Analysis result, or owner-page identity.
> **Executable evidence:**
> [`evaluation/formal-schnorr-relations-plan-f2p1`](../../../../evaluation/formal-schnorr-relations-plan-f2p1/README.md)

## 1. Exact question and answer

F2-P0 showed that the Relations and Plan contracts offer destination families
for all five missing VCVio property premises, but the admitted F1-R1B subject
selects none of their operands. F2-P1 asks one question: can one exact intended
finite-additive Schnorr relation and one exact honest Plan be authored as
candidates, bound to the exact F1-R1B Fresh Protocol, and reconstructed along
two independent paths, including the requested initial-claim meaning?

The answer separates the candidate bundle from one impossible requested edge:

1. **The relation and Plan candidates form.** The two paths agree on all
   bodies and all 15 package-local candidate identities. The Protocol
   statement and phase edges, `PlanRealizes`, witness surface, and witness
   binding check. All five F2-O0 premises receive named candidate coordinates.
2. **The requested initial-claim meaning does not form for this Protocol.**
   The admitted F1-R1B Core has `claims=()`. Relations Section 7.3 requires an
   actual K2 `ClaimRef`, and specifically `InitialClaim(BindingRef)` for an
   initial meaning. Creating one would alter the Protocol claim graph and
   rotate its identity.

The aggregate is therefore `CannotAnswer`, with blocker
`F2P1-C-INITIAL-CLAIM-ABSENT`. Missing claim authority is not converted into an
affirmative relation meaning or a negative protocol claim.

## 2. Exact candidate algebra and relation

F1-R1B is finite and additive. Its statement `Y`, commitment `A`, challenge
`c`, and response `z` all use the three-element `Z3` value type, and the check
is

```text
z = A + cY mod 3.
```

The candidate interprets this without introducing a multiplicative group:

```text
scalar carrier       Z/3Z
group carrier        (Z/3Z,+)
group operation      (u+v) mod 3
generator            G=1
scalar action        s . g = repeated addition, represented by s*g mod 3
relation             Y = x . G
```

Because the fixture uses the same `Z3` carrier for scalars and additive-group
elements and chooses `G=1`, relation truth is exactly `Y=x mod 3`. This is a
finite discrete-log analogue only; the notation does not assert
exponentiation or a production group.

The four Interface roles are:

| Interface role | Candidate vector |
|---|---|
| public instance | `[Y : Z3]` |
| private witness | `[x : Z3]` |
| Oracle statements | `[]` |
| phase inputs | `[c : Z3, z : Z3]` |

The `RelationSemanticModel` evaluator decides `Y=x.G`; it accepts `c` and `z`
at the phase-input coordinates but does not use them to determine relation
truth. The candidate instance family contains all 27 `(Y,c,z)` tuples, with
`(1,2,1)` as the frozen representative. Definition and model agree on all 81
`(Y,x,c,z)` rows.

## 3. Protocol binding and the claim boundary

The `ProtocolRelationBinding` names the exact F1-R1B Fresh Protocol and binds:

| Relation source | Protocol target | Meaning |
|---|---|---|
| `PublicInstance[0]` | Statement public binding 0 | `Y` |
| `PhaseInput[0]` | Challenge 0, emitted at occurrence 1 | `c` |
| `PhaseInput[1]` | public output 0 of occurrence 2 | `z` |

Oracle edges, reduction meanings, commitment groundings, and claim meanings
are empty. The statement and phase portions admit under the package's bounded
contract rendition.

An initial `ClaimMeaningBinding` cannot be added. The exact reason is not an
underdetermined owner field: `relation-model.md` Section 7.3 lines 1856--1860
requires a K2 `InitialClaim(BindingRef)`, while
`formal-source-target-core-f1r1b/reference_model.py` line 794 fixes
`claims=()`. No owner-page delta is proposed because the contract is clear;
the supplied brief assumed a claim coordinate the selected subject does not
have.

## 4. Plan, realization, and witness binding

The Plan's strategy role has two recipes over the exact Prover decision sites:

```text
private material      x : Z3, WitnessIngress
private randomness    r : Z3, first available at decision 0
persistent state[0]   nonce r : Z3, initialized to 0

decision 0            A := r; emit A; replace state[0] with r
decision 2            read state[0], prior challenge occurrence 1, and x;
                      z := r + c*x mod 3; emit z; keep state[0]
```

The `PlanRealizes` candidate covers every and only decisions 0 and 2, checks
typed recipe ABIs and move shapes, confines the response recipe to a guaranteed
prior challenge read, and checks one-shot nonce use and total state updates.
This is structural Plan realization, not relation-relative honesty.

The source-ID-free `PlanWitnessSurface` contains only `x : Z3` with role
`WitnessIngress` and class `SuppliedForGeneration`; nonce randomness and
persistent state are absent. `PlanWitnessBinding.witness_edges[0]` maps the
whole relation `PrivateWitness[0]` to the whole `x` entry and checks type
equality.

## 5. Five named premise coordinates

| F2-O0 premise | Exact candidate coordinate | Operand meaning |
|---|---|---|
| relation predicate | `RelationSemanticModel(...).evaluator` | `Y=x.G` in additive `Z/3Z`, `G=1` |
| witness type | `RelationInterface(...).private_witness[0]` joined by `PlanWitnessBinding.witness_edges[0]` | `x : Z3` supplied at witness-ingress key `x` |
| Prover private state | `ProverPlan(...).persistent_state[0] -> PlanExecutionState[0]` | nonce `r : Z3` |
| honest commit | decision-0 recipe node 0 into `PlanStrategyStep(0)` | `A := r` |
| honest respond | decision-2 recipe node 0 into `PlanStrategyStep(2)` | `z := r+c*x mod 3` |

These are the named operands later correspondence work may inspect. They do
not yet discharge the F2 entry contract: no provider translation, theorem
hypothesis map, relation-relative algorithm correctness, or theorem
applicability judgment is authored here.

## 6. Independent construction and bounded evidence

The forward path admits the F1-R1B Core and Fresh Protocol with the typed F1
checker, constructs typed candidate records, checks each binding, and executes
the Plan. The reverse path starts from the independent F1 owner-view builder,
constructs ordinary dictionary bodies in a different order, validates the
same contracts without importing the typed candidate path, and independently
executes the evidence and mutations.

They agree on every body, all 15 identities, all five premise coordinates, the
single blocker, five mutation outcomes, and aggregate digest
`e810a54ef817bfac87c7bd0236a999eaf4c281e122e0d57ca65f102ae3afa75b`.
The `candidatev0` identity labels are deterministic package-local comparison
keys, not owner-issued `zkcidv0` identities.

For each valid relation pair `(Y,x)` with `Y=x`, each nonce, and each challenge,
the bound Plan's `A=r`, `z=r+c*x` run passes the exact F1 equation: 27/27.
Replacing `z` with `z+1 mod 3` rejects 27/27 controls.

Five directed mutations preserve the following boundaries:

| Mutation | Result |
|---|---|
| wrong Statement edge | `Refused/F2P1-R-STATEMENT-EDGE` |
| swapped equal-typed challenge/response roles | `Refused/F2P1-R-PHASE-ROLE-SWAP` by exact candidate identity |
| Boolean relation witness against `Z3` Plan surface | `Refused/F2P1-R-WITNESS-TYPE` |
| decision 2 reads its own response outside the guaranteed prefix | `Negative/F2P1-N-PLAN-READ` |
| wrong Protocol identity | `Refused/F2P1-R-WRONG-PROTOCOL` |

The swapped-role case is structurally type-correct. It demonstrates why exact
authored candidate identity, rather than generic edge shape, carries the role
choice.

## 7. Disposition and non-claims

No owner-page change is proposed. The owner contracts supplied enough fields
for every candidate body and correctly refuse the absent claim edge. There is
therefore no `Proposed delta` section and no edit to Relations, PIR,
Foundation, or Analysis owner pages.

The 39 findings are bounded candidate evidence only. They establish no theorem,
no completeness or other property, and no security. In particular they do not
establish `Schnorr.sigma_complete` applicability, provider-field
correspondence, totality in another carrier, knowledge or soundness, discrete-
log hardness, Fiat--Shamir security, implementation/backend correctness, or
production validity. Finite `Z/3Z` enumeration is not a theorem.

## Handoff

- Branch: `lane/rf-schnorr-relation-plan`.
- Commit hash: unavailable in this runtime because the clone's `.git` metadata
  is mounted read-only; `git add -A` fails while creating `.git/index.lock`.
  The external handoff reports the unchanged base `HEAD` and working-tree
  state. Independently, a commit cannot contain its own final hash without
  changing that hash.
- Validation (writable clone-local alternate staged index; all successful
  reruns are over the full staged content before this handoff text was
  recorded):
  - `python3 -B checks/run.py validate`: exit 0, wall 0.04 s;
  - `python3 -B checks/run.py run --tier developer`: exit 0, wall 0.85 s,
    7/7 checks passed; and
  - `python3 -B checks/run.py run --check research.schnorr-relations-plan-candidates`:
    exit 0, wall 1.23 s, 1/1 check passed.
  - The first developer-tier invocation exited 1 after 0.47 s solely because
    `uv` could not create a temporary file in the read-only default cache; the
    successful rerun used `UV_CACHE_DIR` inside this clone and `UV_OFFLINE=1`.
- Aggregate outcome:
  `CannotAnswer/F2P1-C-SCHNORR-CANDIDATE-BINDING-INCOMPLETE` with sole bundle-
  completion blocker `F2P1-C-INITIAL-CLAIM-ABSENT`.
- Non-claims: candidate status only; no theorem, property, security,
  owner-page publication, provider correspondence, or production claim.
- Surprises: the relation and Plan candidates, five premise coordinates, all
  finite runs, and all mutations closed cleanly; the exact F1-R1B subject has
  zero claim declarations. The runtime also mounts both `.git` and the default
  `uv` cache read-only; the latter was handled with a clone-local cache, while
  the former prevents the requested commit.
- Where this brief was wrong: it requested an initial-claim meaning for a
  claim-free admitted Protocol. Satisfying that request would require changing
  the Protocol body and identity. Its request for the final commit hash inside
  the same commit is also self-referential. In addition, this runtime's
  read-only `.git` mount makes the requested commit itself unavailable.
