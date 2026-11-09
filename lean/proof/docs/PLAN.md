# Standalone framework plan

This package implements the top-level proof architecture independently. It imports only pinned external mathematics and interaction libraries; it does not import zkc execution, source readers, generated artifacts or existing clients.

## Acceptance

1. Fixed soundness and completeness requests have explicit meanings over complete probabilistic executions. Evidence cannot select the request's event, relation, experiment or assumptions.
2. A root closure theorem derives the actual request from local component installations, initial-state representation, the mathematical contract, and event transport. It must not take the requested conclusion as a premise.
3. One contextual substitution theorem covers every finite well-founded client of a typed operation interface, including adaptive continuations, branches, shared state and nested finite iteration. Use cslib's existing free interaction monad, not a new protocol IR.
4. Quantitative contracts compose through expected continuation potentials. Independence is never inferred from syntax or service names. Completeness observes rejection and abort; soundness quantifies over admitted adversarial environments.
5. Complete small models exercise iterative residual checking, stateful oracle queries, and shared-challenge conjunction; representation changes and explicit refusal theorems test the boundaries. These are model clients, not production protocol proofs.
6. Independent sol 6.1 xhigh review, fixes, one focused package build, axiom audit and documented reproduction. Existing pipeline builds are outside this independent package's validation scope.

## Work order

- Research and select the semantic core; record alternatives and falsification criteria.
- Implement requests and the root theorem against explicit interfaces.
- Prove and instantiate the common installation and contract composition rules.
- Complete heterogeneous model clients and counterexamples.
- Review the whole package, fix findings, validate affected modules, checkpoint.

Production connections and migration require a later reviewed unit. The old implementation worktree is preserved.

## Original completed checkpoint (`276b63146`)

The fixed requests, both root closure theorems, the generic component and contract rules, the
two complete model clients and the refusal controls are implemented and checked. Independent
xhigh review accepted the bounded package; its documentation finding is resolved. The full
incremental package build and all-declaration axiom audit passed. See [VALIDATION.md](VALIDATION.md)
and [REVIEW.md](REVIEW.md) for the exact evidence and limits.

That checkpoint was followed by the framework-completion research and the property-interface unit below. Connecting existing zkc execution or
starting protocol-specific migration is not part of this completed checkpoint.

## Property-interface completion unit

This unit implements the semantic/property surface from the accepted completion plan:

1. Preserve one `FreeM`/kernel execution substrate and the existing installation/closure proofs.
2. Add promise regions, optional witness relations and complete measurable observations.
3. Separate fixed recovery, bounded extraction and operational simulation profiles; expose the
   selected access, quantifiers, observations, guarantee and resource scope in their requests.
4. Index receipts by built-in request constructors or an explicitly custom proposition. Keep
   conditional premises and nonvacuity assessments explicit.
5. Migrate both complete model clients without a compatibility path. Exercise every built-in
   property kind with a closed receipt and a relevant refused mutation.
6. Review semantics, imports, names and source ownership; validate changed modules, then run
   one final incremental package build and all-declaration standard-axiom audit.

Production connections, imported protocols, runtime/PPT adequacy, a report generator and the
later construction/transport packages are outside this unit. The next unit is reusable contracts
and property-appropriate transport; no production client must be connected to accept this one.
