# Protocol models and clients

These clients exercise distinct interpretations of the same execution and
contract infrastructure. Their exact statements and premises are in
[support](../support.md); they do not establish corresponding native protocol
implementations.

## Sumcheck and opening reductions

[Sumcheck profiles](../spec/profiles/README.md#sumcheck-components) distinguish
quadratic statements, scalar rounds, the complete interactive terminal, typed
framing and local prover cuts. An early scalar return is not full acceptance.
The [virtual-product example](../../Examples/OpeningReduction/README.md)
returns a scalar and ordered point followed by explicit opening obligations.
Flattening a formal product to its Boolean table can preserve the initial sum
while changing evaluation away from the cube; the example retains that distinction.

## Merkle and FRI

The Merkle model binds an actual root, query index and ordered path to an
interpreted leaf/node computation. A local cache law depends on actual immutable
bindings, validity and invalidation. It does not prove full FRI soundness or a
native verifier. See [domain correspondence](../correspondence/domains.md) for
the exact source and cache clients.

Lossless encoding and pruned-proof reconstruction have different contracts.
Pruning can erase inconsistent redundant digests rejected by a full-wire verifier;
honest reconstruction alone does not establish equality on hostile full wires.

## Correlated setup and sessions

The captured-program service fixes its source, setup-authorized captures,
controller and publication/history observer. A cut request returns `U`; a full
request returns `(U,V,tag)`. The cut is selected before that response. Delivered
values update history, and residual tape persists. Service completion is not
proof acceptance; an interaction between `U` and `V` requires another operation
boundary.

[Installed](../../Zkc/Protocols/CapturedPrograms/Inputs.lean) connects actual
inputs and source issuance. [Execution](../../Zkc/Protocols/CapturedPrograms/Execution.lean)
preserves complete runs and history. [Probability](../../Zkc/Protocols/CapturedPrograms/Probability.lean)
transports the selected correlated law at its stated observer. A stronger
deterministic state relation does not enlarge that privacy observer.

## Acceptance and continuation

[Accepted continuations](accepted-continuations.md) join an actual source,
installed policy, fresh target, retained verdict and isolated consumption. No
authorized export follows a stopped arm. This atomic single-export law does not
turn an arbitrary Boolean into an accepted relation or supply multi-export,
transferable or persistent custody.

## Choosing another client

A new client is useful when it exposes a missing operation, law or boundary.
Arithmetic, physical roles, virtual data, correlated resources, claim reductions
and terminal acceptance should retain their own premises. Complete argument
security and native execution need their explicit connections rather than
inheriting a claim from a similar local model.
