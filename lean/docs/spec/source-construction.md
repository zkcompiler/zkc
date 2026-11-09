# Common quantitative source construction

This interface constructs proofs about the existing `Zkc.Source.Region` and its actual
`RegionMeaning`. It introduces no second source language or execution semantics. Native
source admission and generated-controller correspondence remain separate connection boundaries.

## Fixed meaning and request

`ProtocolProof.OperationSpec.toWPMonad` adapts the existing quantitative `wpFold` to the pinned
upstream `Std.WP` interface. The ordinary order establishes lower bounds; the exact order dual
establishes upper bounds. Both retain the result or precise stop reason, reached private state,
and complete ordered event history. Importing the adapter does not install a default meaning.

`construct_region` requires its request type to be fixed before selecting rules or mathematical
choices. The source body, operation interpretation, returned/stopped observations and requested
bound are inputs. Intermediate continuation potentials may be derived; none of these inputs may
be inferred from the proof that happens to be available.

The constructor produces ordinary Lean terms. Existing `UpperEvidence` and `LowerEvidence`
remain the root interfaces: operation installation, the entire initial distribution, the model
bound and the property-directed terminal comparison are still required. Exact correspondence
continues to use `Region.Derivation`; a quantitative contract is not exact correspondence.

## Structural rules and mathematical inputs

| Responsibility | Interface |
| --- | --- |
| Lexical operands, result order and caller placement | Shared Region rules and typed environments |
| Return, every stop, sequencing and primitive continuations | Process/WP rules |
| Selected branches and closed callback substitution | Operation-specific proved rules |
| Finite iteration | Generic induction with a typed remaining-iteration invariant |
| Operation behavior, representation, algebra, probability and meaningful invariants | Named mathematical/library laws |
| Actual service state, histories, aliasing and dependence | Fixed operation semantics and installation |
| Whole-experiment claims | Existing request and evidence assembly |

An operation's interpretation owns when and how its regions execute. A generic Region rule
does not run every callback or assume that their services are disjoint. Finite iteration does
not reset private state or infer independent sampling. A zero iteration count executes no body.

Named `@[spec]` laws are ordinary checked theorems. A contextual law is applied to the actual
body, interpretation, arguments and postconditions, including the stopped postcondition.
Lexical renaming transports operands; it does not silently substitute a different provider,
role, setup authority or mathematical meaning. Definition laws can quantify over semantic
premises and over other named laws.

The supported quantitative reference profile includes the canonical Region constructors,
scalar ordinary operations, selected control and finite repetition. Other operation libraries
can register proved specifications. Missing rules are reported as infrastructure gaps: the
constructor does not export residual `Region.denote`, `wpFold` or `WP` structure as mathematics.
This profile does not assert admission of every native operation.

## Choices, templates and companions

`construct_region with_invariants [term, ...]` elaborates each mathematical value against the
required fixed invariant type. The terms may use the existing `zkc_companion` resolver. A value
is not evidence: initialization, preservation, terminal conditions, stop behavior and the root
budget must still be established. An ill-typed explicit choice or proof does not silently fall
back to a different registration.

The module order is definitions and obligation templates, companions, then assembly. Existing
`companion_goal` emits a closed type alias for the complete declaration telescope before any
proof is authored. A header with parameters denotes the universally quantified template, not
a function that can be applied as if it were a predicate definition. Mathematical predicates
may be named separately and instantiated after a value has been selected. No template is an
axiom or a declaration that its payload holds.

`report_construction_goals` uses the existing companion-obligation record for remaining fixed
mathematical propositions and their full local context. The record is authoring information,
not a security receipt. Native source identity is absent for model-only clients; the tool does
not fabricate a source span from a proof-search position.

## Implementation and evidence

The default constructor uses upstream one-step VC generation and its specification database,
with checked dependent application where projected Region value types require ordinary
elaborator unification. Continuations are exposed before applying a preceding call's law.
Otherwise an opaque operation expectation can hide later reusable calls inside a semantic fold.
Only privately introduced intermediate potentials are synthesized. Generalization follows
Lean's delayed-assignment abstraction map, preserving state and branch-hypothesis dependencies.

Complete model tests include:

- A history-adaptive multiround source with arbitrary finite outer count and inner width,
  including zero counts; complete soundness and honest-completeness roots reuse existing
  challenge mathematics.
- A selected admission guard around that complete source, with explicit refusal and honest
  admission premises.
- Persistent publication and two decoded oracle reads, where the first reply selects the
  second position; exact acceptance, a proximity corollary and honest completeness.
- A non-injective implementation representation that erases an audit counter while preserving
  the complete store, outcomes and histories, installed at the whole oracle root.
- Fixed typed scales and mathematical recurrence/budget templates, independent companion
  registrations and assembly; malformed choices, false initialization, changed meanings and
  invalid explicit selections are rejected.

- A held-out multi-result Region that recovers a private Boolean challenge from the first
  equality reply and checks it at a second call. Both whole-experiment bounds are one, while
  the stronger observation requiring both checks to accept is proved impossible. Its local
  laws preserve the private challenge, advance the retained counter by two and retain history.

The held-out client was selected after the common rules and constructor were frozen. It
requires no new constructor or semantic rule. Stored-proof audits check both query-law
applications, repeated/nested calls and count-independent finite-loop theorem references.
See the [authoring and measurement guide](../development/source-construction.md) for the
complete scope, author inputs and reproduction commands.

These are independent model clients, not completed native Sumcheck/FRI connections. Actual
source association, generated-controller correspondence and the original security endpoints
remain separate obligations. The constructor does not certify an arbitrary native operation
or infer the intended security property from executable code.
