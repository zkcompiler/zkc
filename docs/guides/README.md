# Understanding the model

These guides explain the selected semantics through examples and failure cases.
The [specification](../spec/README.md) owns the definitions; the
[theory map](../theory.md) connects them to their mathematical tools and primary
references. [Language documentation](../language/README.md) covers authoring syntax.

Read the first three chapters in order, then follow the boundary relevant to your
work.

| Question | Guide |
|---|---|
| What are the protocol, participant algorithm and plan? | [Subjects and scope](protocol-model.md) |
| What does running a program preserve, including failure? | [Execution, observation and refinement](execution.md) |
| How are source values, captures and permissions bound? | [Source formation and inputs](source-and-inputs.md) |
| How do rounds, selected programs and installed services use the model? | [Effectful source interpretations](effectful-sources.md) |
| What can a caller assume, and what survives state changes? | [Contracts, state and reusable facts](contracts.md) |
| When may interactions be sequenced or repeated? | [Composition and atomic sessions](composition.md) |
| What does acceptance permit a later computation to do? | [Accepted continuations](accepted-continuations.md) |
| Which experiment, probability law and terminal check establish a property? | [Security properties and premises](security-properties.md) |
| How are identities and evidence bound to actual artifacts? | [Artifact binding](artifact-binding.md) |
| How do native values, codecs and state implement the model? | [Realization and native boundaries](realization.md) |
| How do these abstractions apply across protocol families? | [Contrasting protocol interpretations](protocols.md) |
| How does a transformation connect source, proof and implementation? | [Worked transformation](adding-a-transformation.md) |
