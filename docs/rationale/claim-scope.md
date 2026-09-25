# A requested claim is carried as its named experiment or reported unsupported

A compiled result carries execution and refinement claims and the admission
judgments its endpoint policy requests. It carries a security property only as
a named experiment with its actual operands. The companion experiment is
[interactive Sumcheck](../spec/profiles/sumcheck/interactive.md#honest-execution-and-interactive-soundness):
the actual original statement, degree at most two, messages chosen before their
independent uniform challenges, exact terminal evaluation, honest completeness,
and acceptance of a false claim bounded by `2*n/|F|`. The bound is
parameterized and is stated also where it is uninformative. A request for a
property with no such experiment, such as zero knowledge, extraction, a
succinct opening or native side-channel resistance, is reported unsupported.
Simulation and extraction stay
[parameterized claim boundaries](../spec/properties/experiments.md#simulation-and-extraction-claim-boundaries)
with no selected universal instance.

## Alternatives

**Answer a stronger request with a weaker local certificate.** An execution
equality lifts through a common body under its handler relation. It
[does not choose](../spec/properties/experiments.md#observation-based-transport)
the experiment's initialization or a larger strategy class, and it cannot
replace the challenger with a deterministic counter. A certificate of it
therefore does not establish the requested property.

**Count finite differential agreement as a native security theorem.** It is
evidence of native correspondence at its recorded scope. The native integration
still binds its actual source, inputs, prover interface, challenger and
terminal to the experiment's operands. Native trust, resource and progress
premises stay in the [assurance report](../assurance.md).

**Attach a guarantee against a limited adversary whenever results agree.** A
transformation can replace a computation whose cost falls outside the admitted
class. The original execution that the argument needs then does not exist, and
the transport fails although every output agrees. Such a claim states the
admitted programs and adversaries, the resource accounting of both protocols,
and a translation of an adversary against the transformed protocol into one
against the original inside those limits. The accounting used for calls and
preparation measures neither.

**Fill a universal simulation or rewinding record in advance.** It would select
commitments with no consumer to validate them. The affine disclosure and
commitment-session examples stay as contrasting regressions with their own
observers. They are not generic zero-knowledge or commitment theorems.

## Reason

Naming the experiment keeps the statement, the strategy class, the challenger
and the terminal attached to the bound that was proved for them. An answer of
"unsupported" leaves that binding intact. A weaker certificate returned under
the requested name would break it.

## Reopen when

A concrete consumer needs one of the unsupported properties. Its profile then
states the experiments, the permitted strategies and access, auxiliary input,
quantifier order, comparison and loss. A shared interface is extracted only
after distinct protocol families have been compared.
