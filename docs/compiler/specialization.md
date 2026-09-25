# Generic specialization

Generic source is checked before closed instantiation. The following design
separates the source subject, selected instance, physical representation and
runtime invocation; [original-source validation](library-design/validation.md)
states implemented checking and correspondence coverage.

## Selected boundary

Use a bounded typed generic source representation and instantiate it into closed,
domain-typed MLIR. Keep the generic source, public requirements and immutable
instance selections as independent checking inputs. Instantiation fixes static
type/operation identities; it does not lower polynomial, PCS or group algorithms
into scalar instructions, nor project participants prematurely.

Symbolic generic MLIR is a possible later carrier for analyses that justify its
cost. It would require parameter scope, associated identities and requirement
entailment in every participating operation verifier and conversion. The current
native operations resolve concrete domains and constructions. Sharing parsed
source bodies and requirement results before instantiation captures the immediate
reuse benefit without making physical consumers interpret open terms. This is a
placement decision, not a claim that generic MLIR is less expressive.

The elaboration boundary has a real cost: checking only the generated closed
source would trust C++ instantiation. The Lean path must independently interpret
the original generic source and selected bindings. The existing raw portable
interpreter is not automatically covered by the typed library theorem. The
[validation design](library-design/validation.md) specifies independent source formation,
candidate-local checking, source mappings and complete resource obligations.

## Objects and types

Keep generic definitions, semantic instances, physical specializations and runtime
invocations distinct:

| Object | Required contents |
|---|---|
| Generic definition | Scoped parameters, type/operation terms, checked public requirements, body, original sites. |
| Semantic instance | Definition reference, immutable mathematical and construction bindings, static arguments and child instances. |
| Closed logical callable | Actual domain-typed signature and instantiated body, with an explicit semantic environment. |
| Physical callable | Logical callable reference, exact physical ports, implementation bindings, ABI and converted body. |
| Invocation | Dynamic inputs, caller origin, participant/session identity, frame lineage and authorized resource view. |

Logical types retain nominal domains or construction identities. A physical type
is `(logical type, representation identity)`. Public wire codecs are construction
contracts; physical storage order is a representation contract. They must not be
conflated in a backend profile.

The native [closed-binding profile](../spec/profiles/source/operation-bindings.md)
supplies the concrete carrier: explicit operation applications in common and
participant artifacts, `pir.operation_binding` symbols, and fully qualified
logical/physical ports. Rust admits this carrier into the same fully typed runner
as other explicitly bound artifacts and executes it against independently installed contracts.
The independent Lean consumer checks original generic formation, nominal
specialization, local physical bodies and participant control. Rust retains its
checked argument/call maps and executes them in the shared runner and scheduler.
This structural check is distinct from the original-source generic and artifact
interpreters; their native comparisons provide separate bounded execution evidence. The [local interactive host](../runtime/inputs.md)
uses original ports and explicit per-input/per-receive setup policy.

For example, two physical versions of `ProductRound<Fr>` may receive respectively
logical MSB-order tables and Arkworks bit-reversed tables. They share the logical
specialization but have different physical signatures. A crossing call needs an
executed, checked conversion. Both representations must occur in the same actual
artifact; aliases for identical storage do not demonstrate this property.

A nullary call such as `poly::empty_point::<F>()` needs explicit static arguments
or a local result annotation such as `let p: Point<F> = poly::empty_point();`.
Its elaborated common call always has a selected environment/result domain. Operand inspection cannot supply every
binding. Conversely, a pure domain-independent helper does not inherit unrelated
PCS parameters solely from its containing namespace.

## Requirement fragment

The native engine in `Compiler/Requirements` handles equality, associated-member
congruence, named relations with ordered arguments, and explicitly installed
unary capability implications. It emits shared topological derivations. The
Lean checker validates actual conclusions, premise indices and declaration
indices; its soundness theorem is relative to a model satisfying the assumptions
and installed rules.

The generic source layer is responsible for sorted terms and installed nominal
consistency. The requirement engine deliberately treats roots as uninterpreted
identities: it does not decide that two arbitrary names denote distinct fields.
Public assumptions must derive body obligations. Unproved obligations remain
unresolved. Runtime preconditions, cryptographic hypotheses, target eligibility
and author support policy retain their distinct owners.

The solver does not construct arbitrary terms or discharge arithmetic/security
theorems. Alternatives are separate applicability queries. Adding a fast variant
therefore cannot silently strengthen the public algorithm's requirements.

## Preservation obligations

- Operation lookup uses explicit declarations and selected environments. BLS
  profile spellings elaborate to exact defaults before common admission.
- Physical assignments belong to values and interfaces. A crossing between
  representations requires an executed, checked conversion.
- Logical operation contracts and installed physical kernels have independently
  checked signatures and effects at native admission.
- Original logical origins survive specialization. Generated code names do not
  replace transcript domains or resource invocation identities.
- Conversions retain complete stopping behavior. Allocation may fail; conversion
  steps cannot be erased or moved across observations without their resource law.
- Original-source Lean interpretation and admitted Rust artifact execution are
  independent paths; agreement between two generated closed sources cannot
  replace either one.

Storage order, nullary operations, extension-field openings, challenge
consumption, source-origin renaming and conversion exhaustion are discriminating
cases for these obligations. This list is not a coverage claim; the
[validation reference](library-design/validation.md) states which scopes are
currently exercised.
