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

## Completed checkpoint

The fixed requests, both root closure theorems, the generic component and contract rules, the
two complete model clients and the refusal controls are implemented and checked. Independent
xhigh review accepted the bounded package; its documentation finding is resolved. The full
incremental package build and all-declaration axiom audit passed. See [VALIDATION.md](VALIDATION.md)
and [REVIEW.md](REVIEW.md) for the exact evidence and limits.

The next action is review of this standalone architecture. Connecting existing zkc execution or
starting protocol-specific migration is not part of this completed checkpoint.
