# Property-interface review and disposition

The property-interface unit received a central semantic, architecture and code review against
the accepted framework-completion plan. No external reviewer/delegation tool was exposed in
this run, so the earlier independent review below is not presented as a review of these changes.

| Review question | Resolution and evidence |
| --- | --- |
| Can evidence weaken a built-in meaning? | `Claim` stores the entire typed request and derives `Meaning`; custom propositions have a separate constructor. Wrong-extractor and false-statement receipts are refused. |
| Does proximity falsehood collapse into exact nonmembership? | `PromiseProblem` has disjoint Yes/No regions with a permitted gap. Gap acceptance passes; negative/adaptive acceptance fails. |
| Is honest success conditioned on acceptance? | `Experiment.observe` preserves all mass. The half-abort client has half completeness; perfect completeness is refused. |
| Can extractor evidence choose a witness-searching replacement? | The actual `FreeM` algorithm, target, witness relation, handler and guarantee belong to the request. Wrong returned witnesses and wrong target statements are refused. |
| Is a vacuous success function labeled useful extraction? | `ExtractionGuarantee.positive` and `positive_success` connect the fixed threshold to positive actual success. A zero function above an informative threshold is impossible. |
| Does call accounting overstate efficiency? | It uses pinned PolyFun charge semantics and explicitly counts only weighted abstract operations. No PPT or host-runtime claim is exposed. Zero-call budgets fail for a one-call program; adaptive calls retain the worst continuation. |
| Can a simulator depend on the private witness? | `SimulationProfile` fixes its algorithm and context-dependent services before witness quantification. Both simulation meanings refuse a leaked witness. |
| Are statistical and selected-test security conflated? | Separate typed requests quantify over all measurable events or the selected normalized observer family respectively. No automatic computational-ZK label. |
| Do assumptions vanish inside receipts? | `ConditionalReceipt` retains its premise; `close` needs its proof. An impossible premise does not establish a false closed claim. |
| Are empty populations or vacuous parameters hidden? | Admission, error and resource assessments have explicit positive, negative and unchecked forms. Kernel validity stays independent of proof provenance. |
| Is there a parallel legacy path? | `Experiment` moved below `System`; definitions were split, not copied. `ViewRequest` was replaced by `ViewComparison`. Existing clients use the same migrated soundness type. |
| Is upstream machinery duplicated? | The initially local charge formula was replaced by pinned PolyFun `OpSpec.charge`; VCVio remains the sole probability interpreter. |

The property interfaces are a semantic surface, not a full cryptographic method library.
`ExtractionRequest.establish` closes success and resource obligations; it does not prove a
forking theorem. Exact-view closure uses an actual law equality; nonexact comparisons remain
ordinary mathematical obligations. The later contract/transport and construction packages
remain separate. Production binding and intended-relation adequacy are not silently supplied.

Module review removed an unnecessary simulation dependency on the game-transfer module and
moved the exact-view theorem beside its mathematical comparison. Public meaning definitions
use `@[expose]`; no new evaluator, axiom, proof-route audit, compatibility alias or toolchain
upgrade was introduced. The migrated adaptive and shared-state proofs retain their bounds.

See [VALIDATION.md](VALIDATION.md) for the final current gate, distinct from the historical
checkpoint evidence below.

---

# Original checkpoint: independent review and disposition (`276b63146`)

An independent AI reviewer, `gpt-6.1-sol` with `xhigh` reasoning, reviewed the frozen standalone
package on 9 November 2026. It read all package sources, both complete clients, the boundary
controls, the design/plan/interface documents, and the selected upstream interpretation,
coupling, transport and specification-fold proofs. It verified all 22 frozen file hashes and
the selected VCVio, PolyFun and Mathlib source revisions. It reused the passing build evidence;
it ran no builds and made no edits.

Verdict: accept the bounded standalone implementation, with one minor documentation correction.
There were no blocking mathematical, semantic or architectural findings.

## Finding and resolution

The old interface summary said quantitative assertions require countable states. The primary
bridge actually accepts arbitrary measurable state and final-result spaces, with countable
operation answers. Countable state and final-result types are needed only by the convenience
form allowing arbitrary, rather than explicitly measurable, terminal functions. `INTERFACES.md`
now states that distinction. This documentation correction does not invalidate the Lean build.

## Substantive conclusions

- Root closure derives the exact fixed request through local installation, initial-law coverage,
  mathematical contracts and the correct terminal implication. The mathematical contract still
  needs a proof; the root does not discover it or take the actual request's conclusion as input.
- Joint answer/state couplings preserve correlations and full marginal mass. A noninjective map
  cannot justify discarding a later observable dependency or an unpreserved terminal event.
- Adaptivity, nested finite iteration and hierarchical components use generic theorems. The
  examples do not introduce another interpreter or a per-client structural induction.
- The examples establish nontrivial complete model-game claims. The shared-state theorem is
  about its specified two-verification client and admitted environments, not every possible
  caller of an interface that also offers challenge revelation.
- Module boundaries and thin upper/lower wrappers are proportionate. No additional abstraction
  layer or code reorganization was recommended.
- Recovery and view requests fix their algorithms and quantifier order. They do not establish
  full knowledge extraction or computational zero knowledge without the respective experiments,
  reductions, resource theorems and mathematics.

The complete review and its frozen hashes are retained with the goal's research and validation
archive. The central review adopted the documentation correction and also checked the authoring
and validation guides added at closeout. No proof or request was weakened to close a finding.

## Later integration gate

Before production adoption, bind the fixed actual subject and adversary interface to this path;
prove the real local answer/state laws and initial coverage; supply the protocol's mathematical
contracts and exact sampling assumptions; then validate the connected claim and its security
transformations. Those obligations remain separate from acceptance of this independent core.
