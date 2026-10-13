# Implementation review

This review asks whether an accepted security claim is about the actual imported
program and authored relation, whether its experiment is explicit, and whether
the architecture supports reuse without copying proofs for each source form.
The reviews below were separate passes by the implementing agent, not an external
independent review. The [support matrix](../support.md) owns the supported claims.

## Architecture and composition

The core imports Mathlib and has no ArkLib, VCVio or Clean dependency. Security
adapters and the Clean relation exporter have separate Lake packages and exact
shared dependency pins. Module-header and declaration-body audits enforce the
direction from generic semantics to protocol contracts to source clients.
Particular source examples do not enter generic security consumers.

`Certificate.verify`, contract adapters and property consumers provide typed
extension points. The custom rejection consumer demonstrates a downstream
property for an imported Schnorr program without a compiler or registry change.
Sumcheck residual contracts and the factor-opening example test sequential
composition with shared state, adaptive replies and a bad-opening event in one
joint experiment. Their error bound adds the opening loss; no independence is
inferred from separate service names.

## Semantics and source boundary

The review distinguishes a returned false decision, rejection, handler stops,
missing replies and an unfinished observation prefix. Well-founded open processes
embed into the machine model, with resumption and completion laws. Native loops
and external waiting remain outside the imported profile.

Native differential execution reads SSA independently of the exporter and
compares full selected observations with the Lean executable over Z/97. Generated
programs exercise arithmetic, role restrictions, communication, service queries,
guards and helper expansion. Malformed inputs and a deliberately changed
arithmetic operation test rejection and discrepancy detection. These are finite
adequacy checks, not a proof of production arithmetic or compiler correctness.

## External proof chains

The ArkLib adapter proves the polynomial-message representation, statement and
domain laws, statement-oracle realization, reached-query execution equality and
accepted-event equality before applying ArkLib's native interactive Sumcheck
soundness theorem. The public two-round degree-two interface admits causal
coefficient-message strategies and arbitrary private probabilistic mixtures
chosen before fresh verifier draws.

The VCVio adapter proves a bijective uniform-sampling transport for Schnorr's
honest transcript and witness-free simulator, including the actual imported
verifier's outcome. This is a fixed honest-challenge, one-session simulation
claim. Neither adapter establishes Fiat–Shamir or malicious-verifier security.
The factor-opening example has a proved public-polynomial instance and a
conditional opening-error bound; it does not supply a PCS security theorem.

## Author intent and proof construction

The named specification selects the contract, property, experiment, roles,
inputs, effect sites and authored target. The interface resolver checks the
source identity and actual selectors, then exports the relation's formula body.
A matching name alone cannot establish the relation. Lean connects the admitted
formula and actual verifier through a generated target special-soundness theorem.

Candidate construction and requested-subject checking reconstruct the source
separately. Controls reject a valid certificate for a different program, copied
positive identities, false relation bodies with expected names, wrong relation
certificates, stale selectors and unsupported experiments. Transitive axiom
checks reject proof holes; the audit controls also test unused axioms, native
evaluation axioms and empty module selections. The resolver and renderer remain
reviewed/tested trusted software boundaries, stated explicitly in receipts.

## Findings resolved during implementation

| Finding | Resolution |
|---|---|
| Latest VCVio removes modules still imported by ArkLib | Pin and test a coherent dependency closure; record the concrete incompatibility |
| A generic `Examples` Lake library collides with upstream examples | Use `ZkcExamples` and test standalone downstream imports |
| Prior source syntax and identities were stale | Re-export from current DSL and recheck exact correspondence |
| A valid protocol proof can hide a wrong authored relation | Check the actual formula body and reconstruct the requested relation subject |
| Constructor rendering could ignore surplus instruction fields | Check exact array arities and source identities before generation; add malformed-export controls |
| Upstream builds contain unrelated proof holes | Audit the transitive dependencies of every claimed owned result |
| Clean's unrelated VM development fails on the new Mathlib | Keep the isolated flat-AIR adapter; prove channel refusal for arbitrary channel operations |
| Deleted models left stale native documentation claims | Remove obsolete proof claims while retaining native mathematical obligations |
| Core checks could resolve optional dependencies | Select core-only boundaries in the default runner; check integrations explicitly |
| A negative test could accept signal termination as refusal | Require an ordinary positive error exit |

## Reproduction and further research

The [package guide](../../README.md) gives source-only reproduction and maintained
commands. `just test-lean-native` runs differential execution, the source/property
matrix and authored-target controls; `just test-lean` runs core boundary and audit
controls plus a standalone consumer. Optional security and Clean commands retain
their own clients and fixture checks. Reports record their inputs and outcomes.

The next research extensions are broader source admission, observation-based
refinement, reusable relation adapters, richer adversary interfaces and explicit
PCS/Fiat–Shamir compositions. They require new definitions and proofs; current
success receipts do not stand in for them.
