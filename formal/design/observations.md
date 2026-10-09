# Results, observers and disclosure

The independent formal models select explicit execution relations and observers.
The [realization](../../docs/spec/realization/representations.md) and
[property](../../docs/spec/properties/experiments.md) specifications own the laws.
These choices do not establish native security or arbitrary target-code safety.

## Relate complete results

A returned handle gets its meaning from the state the execution leaves. Slot
`0` denotes `7` in heap `[7]` and `8` in heap `[8]`. Comparing return values alone,
or decoding them only in the initial state, misses stale contents and lost writes.
Comparing complete results retains residual states, return values or stop reasons,
and ordered projected events. A failed call does not erase its earlier effects.

Equal heaps would forbid valid representation changes. Instead the consumer
selects state and value relations. Reading values in the final states lets
sequencing pass the actual related results to a suffix and lets transitivity
retain the middle execution as its witness.

This relation concerns completed atomic calls. It does not prove a native
callback terminates. Admitted initial states and capacity/progress premises stay
explicit. Asynchronous or diverging interfaces may need a trace or simulation
relation beyond this one; adding an unused divergence constructor would not
supply a termination argument. [Leroy's compiler-correctness account](https://xavierleroy.org/publi/compcert-CACM.pdf)
illustrates why the selected behavior class matters.

## State the experiment and context

Handler relations transport observations through a common reply-adaptive body.
That context class is narrower than arbitrary code linked against a target. Full
abstraction or robust preservation would need a target-context model specifying
linking, code inspection, intervention and provider access. No such general
native model is supplied by these laws. See
[Abate et al.](https://arxiv.org/pdf/1807.04603) for the distinction among secure
compilation criteria.

Artifacts are observations too: equal runtime results do not hide code generated
from a secret. Equal projected events also say nothing about timing, memory or
allocation unless the observer includes them. Each release or transport claim
keeps its actual observer and any residual provider effects.

A security claim additionally fixes the original statement, initialization,
strategy class, randomness and terminal decision. A local execution equality or
finite differential test cannot replace that experiment. The
[interactive Sumcheck result](../../docs/spec/profiles/sumcheck/interactive.md#honest-execution-and-interactive-soundness)
has its own degree, independent-uniform-challenge and direct-terminal premises;
it is not a generic extraction, zero-knowledge, commitment-opening or
Fiat–Shamir theorem.

For a resource-bounded adversary, transport must also keep the translated
adversary within the admitted class under the stated resource accounting. Output
equality alone does not establish that. Simulation or rewinding interfaces need
concrete consumers and experiments rather than a universal record filled in
advance. An unsupported requested property remains unsupported.

## Prove the joint release

When artifact and runtime channels share randomness, their marginals do not
determine their joint disclosure. An artifact `r` and runtime bit `s xor r` are
each uniform for either secret `s`; together they reveal it. Two separate
couplings can therefore be incompatible.

The [joint-release law](../../docs/spec/properties/disclosure.md#randomized-joint-release)
uses one coupling with the actual marginals on which both released coordinates
agree. Requiring identical outputs under the same seed is sufficient but can be
too strong: a secret change may be matched by a translation of hidden masks.
For deterministic release, permission for each coordinate suffices under the
same permitted-world relation.

The selected discrete laws are normalized. Stopped runs retain their probability
mass; unsuccessful runs are neither discarded nor renormalized. Missing mass
would need a meaning such as divergence and its observation policy. Exact
couplings provide no protocol secrecy by themselves; statistical or computational
claims need their own comparison and loss. The coupling method follows
[Barthe et al.](https://arxiv.org/pdf/1607.03455), whose broader subdistribution
setting does not change these selected assumptions.
