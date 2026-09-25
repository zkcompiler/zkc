# A transformation is accepted by checking its candidate, not by proving the optimizer

The [checked transformation](../spec/verification/refinement.md#checking-the-actual-candidate)
takes the retained source, a rule resolved by the consumer, a certificate and
the supplied candidate. It applies the rule, obtains the plan the rule itself
returns, and accepts only when the erased form of that plan equals the
candidate. The rule's soundness law then covers exactly the accepted plan for
exactly that source. How the candidate was found is no part of the judgment, so
[proposal generation](../spec/verification/analysis.md#factor-analysis-and-proposals)
may be heuristic.

The [external-candidate decision](external-candidate-checking.md) separately
explains custody from checking to execution and why phase evidence cannot be
substituted by execution refinement. This record owns the mathematical choice
of validating a candidate rather than verifying the search that proposes it.

## Alternatives

**Prove the optimizer correct.** A result that passes a sound validator is
justified with no statement about the program that proposed it. Tristan and
Leroy develop this separation and allow the validator to fail on
transformations it does not support [1, §2.1]. A proof of the search procedure
would add nothing to an accepted result, and would have to follow every change
of heuristic.

**Accept whatever a sound rule could have produced.** A rule's soundness
speaks about the plan that rule returns. Without the equality test, a plan
derived from another source, or a different plan for the same source, would
inherit a theorem that does not mention it. For the same reason the candidate
cannot select the interpretation of its own operations: a rewrite that holds
for a semiring multiplication fails for an operation that merely has that name.

**Check with a general solver or proof search.** The trust boundary does not
need one. Rules are specific to their model, a rule with no search data needs
only a trivial certificate, and finite certificate formats and the resolution
of native rules are left to explicit profiles. A solver or proof search remains
free to produce evidence for the same judgment.

## Reason

The cost is incompleteness. A candidate the rule does not reproduce is
unsupported, which is neither a proof that no refinement holds nor permission
to run something else. The initial relation stays part of the claim: a rule
proved over an empty initial domain yields a theorem about no invocation, so
the consumer establishes that relation for the actual environment and state.

## Reopen when

A transformation that is needed has no rule whose check is materially cheaper
than its search, or a rule refuses correct candidates often enough that the
lost rewrite matters. Proving that generator then competes with validating each
of its results.

## References

1. Jean-Baptiste Tristan and Xavier Leroy, "Formal Verification of Translation
   Validators: A Case Study on Instruction Scheduling Optimizations," *POPL*
   2008, pp. 17–27, §2.1.
   [Author PDF](https://xavierleroy.org/publi/validation-scheduling.pdf).
