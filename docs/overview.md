# zkc: a compiler for proof protocols

zkc makes the computation and interaction of a proof protocol available to a
compiler. Its purpose is to reuse analyses, transformations and checking across
protocols while retaining the conditions under which each change is valid.
This overview explains that approach. [Status](status.md) records what runs;
the [specification](spec/README.md) defines the model and the
[PIR guide](guides/protocol-model.md) explains it.

## 1. What zkc compiles

zkc compiles the computations and interactions of a proof protocol. Its input
describes how participants compute messages, use challenges and setup, invoke
modules, and check claims. A relation specifies the statement being proved;
an algorithm for generating and checking a proof is additional input.

For example, supplying a circuit or a statement/witness relation does not by
itself choose a commitment scheme, a round structure, or an honest prover
algorithm. A frontend or library may make those choices and expose them to
zkc. The compiler then has an explicit protocol to analyze and transform.

The useful structure is larger than an arithmetic expression. It includes
factor and oracle computations, loops, branches, message order, stateful
calls, allocation, reusable preparation, and the information available to
each participant. These details determine both optimization opportunities
and the conditions under which an optimization is valid.

The intended product is reusable compiler infrastructure that existing proof
systems can adopt incrementally. A backend may continue to supply field
arithmetic, commitments, codecs or other modules through explicit contracts.
zkc can compile a selected component without first replacing the entire stack.

## 2. Three descriptions of one implementation problem

The model distinguishes:

| Subject | What it specifies | Example |
|---|---|---|
| Protocol interaction `P` | Permitted actions, participants, phases and reply domains | Receive a round polynomial before obtaining that round's challenge |
| Role algorithm `Aρ` | The computation performed by a participant, with its inputs and permitted observations | Compute the honest polynomial, or check a received polynomial and update a verifier claim |
| Execution plan `Lρ` | How that computation uses representations, storage, schedules and module implementations | Prepare immutable tables, share justified computations and choose native kernels |

These subjects can be packaged together, but their obligations remain
distinct. A faster prover algorithm need not change the protocol interaction.
Changing which messages are exchanged can change the security experiment.
Choosing a native representation requires a correspondence with the logical
values and execution that it implements.

The [model chapter](guides/protocol-model.md) makes these distinctions precise, including
the difference between an honest algorithm and an adversarial strategy.

## 3. A small meaning beneath a structured representation

PIR has a mathematical execution reference with typed operations and replies,
sequencing, explicit stopping, retained state and ordered events. Module
interpretations give calls their actual meaning. Probabilistic execution
includes the provider's evolving state and failures as part of the result.

The compiler-facing representation retains more structure: typed values,
arithmetic, reductions, branches, public bounded loops and module calls. This
is what enables analyses and transformations. Its connection to the reference
must be justified; merely representing both programs as operations does not
prove they correspond.

This separation supports both structured implementations and library calls.
A module can expose a body when useful for optimization, or an interpreted
contract when its implementation stays external. An effect or purity label
has force only through the law it denotes.

## 4. What an optimization must preserve

Consider repeated immutable preparation inside a stateful protocol component.
The compiler may discover that two requests use the same interpreted
computation and complete inputs, then reuse prepared data. To justify that
change it must establish the key meaning, cache validity, effects, outcomes
and relevant observations. If an intervening write invalidates a logical
fact, the analysis must account for it even when a separate immutable cache
entry remains valid.

The existing research establishes scoped instances of this composition. It
also separates saved work from lookup and storage overhead. Correct reuse is
not a claim of universal speedup, and the same contract infrastructure can be
used by an equally capable library implementation.

More generally, three kinds of change have different obligations:

- **Local computation:** preserve the selected interaction, results, state
  relation and observations while changing computation or storage.
- **Representation:** relate logical and represented values, including
  decoding, malformed input, errors and any remaining input or state.
- **Protocol change:** establish the property-specific translation between
  experiments, strategies and assumptions, with its losses and resource
  requirements.

A local equality can be a premise of a larger argument. It does not establish
that larger argument by itself. Changing challenge generation, batching or
the messages accepted by a verifier requires the corresponding justification.

## 5. What provides assurance

The maintained Lean package supplies mathematical definitions, reusable proofs
and executable references. The C++/MLIR compiler implements structured
operations, analyses and lowering; Rust supplies tools, adapters and execution.
The [architecture](architecture.md) describes their responsibilities. Each
implemented connection retains its own correspondence obligations.

A common compiler theorem may assume that a backend implements an explicit
module contract. Switching between implementations of that same contract
need not change the common theorem. The backend's satisfaction of the
contract must still be proved or declared as trust, and zkc must justify its
own source binding and transformations. Two implementations satisfying an
insufficiently specific postcondition are not automatically interchangeable.

Keep four questions separate when reading a result:

1. Is the intended meaning defined?
2. Which proposition is proved, under which premises?
3. Which actual source or implementation is connected to that proposition?
4. What do measurements or finite controls establish for their tested inputs?

The [formal support map](../formal/SUPPORT.md) identifies the maintained
definitions, propositions and their premises. [Status](status.md) identifies
the corresponding native routes and gaps; [assurance](assurance.md) explains
how to interpret proof, checker and test results.
Protocol security claims remain specific to their experiments. A successful
build is not a proof that every represented protocol is secure.

## 6. How to read the model

The [semantic guides](guides/README.md) start with PIR subjects and scope, then
connect execution, composition, properties and native realization. They include
contrasting protocol interpretations and a worked compiler transformation.
[Theory](theory.md) explains the methods behind those laws.

[Architecture](architecture.md) explains implementation roles and alternatives;
[status](status.md) separates current evidence from production support;
[roadmap](roadmap.md) orders the next work. The
[documentation decision](rationale/documentation-structure.md) explains these
homes.
