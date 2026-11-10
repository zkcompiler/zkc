# Common quantitative source construction

This interface constructs proofs about the existing `Zkc.Source.Region` and its actual
`RegionMeaning`. It introduces no second source language or execution semantics. Native
source admission supplies the actual typed Region. Generated-controller correspondence remains a
separate connection boundary.

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

## Proposition-valued readings

The constructor is generic in the `WPMonad` of `Process`. Besides the quantitative
potentials above, it constructs the proposition-valued readings of
[weakest-precondition interfaces](weakest-preconditions.md): the charged reading at an
escape judgment (the exact judgment, which excludes no reply, or a bounded judgment, which
charges each query site) and the pathwise cost reading. Their assertions are
`ProtocolProof.Truth`, a structure around `Prop` ordered by implication. The constructor
composes un-applied entailments and derives intermediate bounds as lattice elements;
upstream VC generation introduces the state of an assertion that is syntactically
`σ → Prop`, so the carrier is a structure that keeps the entailment shape.

One path leads from a typed `Region` to an endpoint:

1. `construct_region` derives a charged triple and a cost triple of the actual process,
   using one `@[spec]` call rule and one stop rule per reading. The remaining goals are the
   mathematical obligations of the nodes: for each query site, a probability bound on the
   replies whose continuation fails (bounded judgment) or the continuation for every reply
   (exact judgment); for each loop, the initialization, preservation and terminal
   conditions of the supplied invariant.
2. `charged_of_triple` and `costBound_of_triple` turn the triples into
   `Interface.Charged` and `ZkcSecurity.FiatShamir.Typed.ChargedCostBound`.
3. The retained Fiat–Shamir theorem `ZkcSecurity.FiatShamir.Typed.soundness_charged` or the interactive theorem
   `ZkcSecurity.Interactive.soundness_accepted` bounds acceptance by the prover's and the
   verifier's charges.

`Zkc.Tools.Protocol.Readings` registers the node equations with the structural
normalization and the residual equations with `construction_residual`. The residual set reads
entailments between explicit propositions as implications over the quantified histories,
messages and replies. Its registration is global wherever `Zkc.Tools.Protocol.Readings` is
imported, but the constructor applies it only to the goals that remain after every rule has been
applied and whose statement mentions `ProtocolProof.Truth`, its constructor or its projection;
a goal of any other reading is never rewritten by it. On each such goal it is applied twice,
immediately before and after the structural simplification of that goal. Stepping never uses
it, so it cannot remove the entailment shape while rules are being applied; when no lemma is
registered it is skipped. A request may be stated through a reducible triple abbreviation such
as `ChargedTriple`; the constructor exposes the triple.

## Selected and decided conditions

A conditional program splits on its condition. When the bound before the conditional is
derived, the constructor builds it as a dependent conditional on the same condition and
splits on that condition, so a condition that itself contains a conditional is not split
inside. A condition whose `Decidable` instance reduces to a fixed answer selects its branch as
written: the branch is not reduced, so a named program in it keeps its law, and the other branch
is not visited. `Decidable` is a structure, so a decided instance reduces to
`Decidable.intro b proof` with a Boolean literal `b`.

An operation meaning by cases may register its equations as `@[spec]` equations. A
candidate equation whose left side differs from the actual program in a constructor-headed
argument is rejected before unification: after unfolding the operation, full unification
could otherwise accept the equation of another case and leave its unused parameters
unassigned.

## Decided premises, evaluated definitions and instance parameters

A law may have proposition-typed premises; after its application they are obligations. A
premise that evaluation decides is settled when the law is applied: an equation between
Boolean terms that both reduce to literals, such as the membership of a literal role in a
literal set. When it holds it is closed by reflexivity. When it fails, the law does not describe
the actual program and the next candidate is tried, so laws for one operation that differ in a
decided premise select one another. A premise of another form, or one over a value that
evaluation does not decide, remains an obligation.

Structural normalization evaluates the definitions registered with `construction_eval`. An
application of a registered definition is replaced by the result of unfolding it and reducing
the matches of its body, whose scrutinees are decided by evaluation; a number that evaluation
decides becomes its numeral. An application whose match is not decided stays as written, so a
symbolic argument never exposes a match. This serves definitions indexed by a decided value,
such as a transport along the membership of a literal set: no equation rewrites them, because
the two sides of such an equation have types that agree only after evaluation. Typed slot
access is reduced with reducible unfolding, which suffices for a context written as a list;
when that stops at a match, because the context is a list only after evaluation, the access is
evaluated in the same way.

A parameter of a law that the program, its interpretation and its postconditions do not
determine is not chosen, with one exception: an instance of a class is found by instance
synthesis.

## The core language

`Zkc.Tools.Verification.CoreConstruction` makes the constructor walk the meaning of an imported
[core definition](core-language.md#readings-of-a-side) for a literal side, with the steps of
`Zkc.Verification.Core.Steps`. Each step is an equation at the root of the program whose
premises are memberships. `open_core_definition` opens the definition being proved;
`register_core_entries` registers the entry equations of the importer, so a `call` or an `apply`
exposes the callee's named meaning and a registered law about it is applied. The transcript
interface `Zkc.Core.Transcript.interface` gives the readings of the side.

## Actual source association

`import_source` quotes one literal `zkc.structured-source/0` checkpoint into the existing
`Snapshot` vocabulary. Rendering source bytes into Lean data remains a named trust boundary.
The ordinary admission checker must return a program; its success and the materialized program's
exact equality are kernel checked. The literal participates in the module's dependency graph.
Materialization does not replace admission or introduce a second semantic tree.

`source_helper` and `source_protocol` select declarations from that admitted program. The
signature, entire body, output layout and membership equation are derived from the selected
member. A spelling or digest only locates a candidate. Equal keys do not make different bodies
interchangeable. The helper association contains the full signature and erased body tree.

`bind_source_helper` and `bind_source_protocol` install common rules against the actual linked
unit. They retain its semantic dependency closure, ordered actual arguments, role substitutions,
service handles, callback captures and stopping outcomes. Present optional operands can reuse
the same closed helper law. Optional Math calls retain dependency-precise behavior; absence is
not replaced by a blanket strictness assumption.

The caller supplies a named mathematical law for the selected body and interpretation. The same
checked law is instantiated at each actual call. A changed dependency requires a law valid under
the new table or an independently proved transport; body membership alone establishes neither.
The public participant rule retains the selected role and both input and output placement.
Boolean protocol branches check both arms and execute only the selected arm. Missing active
selectors stop as incomplete; inactive participants execute neither arm.

Typed environments resolve a lookup from the ordered type context and variable position, even
when an operation's result tuple is abstract. This is structural infrastructure. Companions do
not reconstruct lexical slots, empty mark results or enclosing frames.

The installation path uses ordinary named theorems and the existing specification database.
Operation libraries may register their operational equations; these equations expose the same
interpreter rather than copying its traversal into a protocol companion. Pure equations require
proof of the corresponding total computation on their stated domain. Stateful, failing and
probabilistic contracts retain the full outcome-aware meaning. Law coverage, interface
conformance and a proof of a fixed claim remain distinct judgments. A direct checked proof does
not require law registration, and it does not discharge an unrelated public coverage promise.

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
Named laws for the actual body are tried before generic constructor unfolding;
priority orders candidates within each group, and application checks their complete types.
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

Proposition-valued model clients include:

- A multilinear Sumcheck verifier written as a typed Region: its charged triple from a false
  claim, its cost triple, `(queries + count) / |F|` at the Fiat–Shamir endpoint and
  `count / |F|` at the interactive endpoint, from one per-site root-counting lemma and one
  loop invariant.
- The same verifier receiving a table handle first: soundness for a statement the prover
  chooses and sends in the clear. An accepted run returns a handle whose table sums to the
  claim, at the same Fiat–Shamir endpoint. The postcondition has the shape of an extraction
  statement whose extractor is the identity on the received handle; no commitment is opened.
- A three-move verifier under the exact reading: every returning run appends the commitment, an
  occurrence of the challenge site and the response to the history, and returns them with the
  challenge and the check's decision.
- A setup-shaped opening verifier in its ideal algebraic game: the prover's representations are
  fixed before the secret is drawn and no reference string is published. One setup site is
  charged `(n + 1) / |F|`, at the interactive endpoint; this is a root-counting bound, not
  evaluation binding of a commitment scheme with a published setup.
- Controls refuting an accepting request under a failing check, a returning run required to
  stop, the obligation a forgetful loop invariant leaves, and an unpaid query. Refusal and failed decoding satisfy
  every rejection-oriented triple while their runs stop; over a total interface an exact
  triple with false stop assertions shows that every interactive run returns.

Clients over imported core packages (`Zkc.Tests.Verification.Core`) include:

- The Schnorr verifier under the exact reading: the reached history and the model's check of
  the response, for every model.
- The Sumcheck verifier under the charged and cost readings: the contract of the round protocol
  proved once at the side it is applied at, the whole protocol by a loop invariant that applies
  that contract through `apply`, and the interactive and Fiat–Shamir bounds, under explicit
  laws of the model that a model is shown to satisfy.
- The setup and the verifier of an opening protocol under the exact reading, with the secret
  answered as a query: the six events and the pairing check; no soundness statement.

These are independent model clients, not completed native Sumcheck/FRI connections. Generated-controller correspondence and concrete protocol security endpoints
remain separate obligations. Actual-source construction tests establish their stated source laws,
not full native protocol security. The constructor does not certify an arbitrary native operation
or infer the intended security property from executable code.
