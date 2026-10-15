# Structured native import

## Purpose and subjects

The shared `Source.Region` carrier needs a checked connection to actual native
structured programs. Its generic formation laws do not establish that a native
helper, capture map, domain, or result list was imported faithfully. The scalar
`zkc.common-source/0` bridge also cannot express these subjects: it expands pure
helpers and has neither declaration identity nor structured callbacks.

Import the original protocol-profile module after native formation and before
preparation. Keep its declarations and contracts. Preparation can select finite
algorithms without scalar simplification, expands Local helpers, and eventually
realizes total mathematics. A snapshot taken there is a different subject; it
cannot establish the source side of a transformation it has already applied.
Native MLIR remains the production representation.

The structured format is a sibling of the scalar format. Native parsing and
verification precede export. Lean independently checks the supported vocabulary,
binding interfaces, declaration references and static profile restrictions before
constructing canonical regions. It supplies the operation meanings; input files
cannot supply a semantic oracle.

## Protocol verification targets

### Schnorr

The first complete endpoint is the verifier of the helper-based Schnorr DSL
Entry. Its open process receives a commitment, queries the actual challenge
service, sends the challenge, receives an independent response, and returns the
Schnorr equation's Boolean result. This equation must hold for arbitrary replies
and stopping prefixes, with the public inputs and service binding explicit.

Establish `Protocols.Schnorr.Common.VerifierContract` once for this imported
subject. Its existing consumers then give perfect completeness and special
soundness. The maintained VCVio honest-view consumer is a subsequent target once
the corresponding source-view equation is established. Native group arithmetic,
probabilistic knowledge extraction, and Fiat–Shamir require further arguments.
Schnorr tests helper sharing and participant binding; it is not a finite-loop
example.

### Sumcheck

The first complete endpoint is the maintained two-round quadratic verifier,
including both early rejection checks, fresh ordered challenges, arbitrary
causal coefficient messages, and the final evaluation Boolean. Establish its
existing `Protocols.Sumcheck.Common.VerifierContract`, then reuse completeness
and the false-claim acceptance bound `4 / |F|` under the stated finite-field and
independent uniform-challenge premises. Early rejection and returning `false`
remain different outcomes. The native service is not proved uniform by its tag.

The final parameterized target is an n-round quadratic native verifier matching
the existing n-round reference, with the polynomial dimension tied to the actual
round count. It requires an interactive `protocol.repeat` profile and a matching
native subject. The library's multilinear pair-message protocol and the Lean
quadratic three-coefficient reference are different protocols. A Local finite
fold importer does not bridge that difference. ArkLib proof reuse follows the
appropriate source-to-experiment equation and its real premises.

## Structural and semantic requirements

The initial maintained import profile has one participant, immutable Booleans,
unsigned indices, BLS12-381 scalar values and vectors, closed helpers, finite
folds and nested Local control. It deliberately refuses group and service
values, communication, affine resources and general interactive repetition.
The complete Schnorr and Sumcheck goals above guide later extensions; they are
not completion claims for this infrastructure package.

- Preserve ordered result tuples, including no results. A zero-result operation
  can still stop or interact.
- Preserve closed helper definitions and references. Capture order, helper
  identity, call ownership and the state/item/argument/capture partition are
  checked interfaces.
- Keep every domain constructor in admission order, including unused ones.
  Empty iteration cannot bypass failed admission.
- Check dormant branches and callbacks. Dynamic nonexecution is not permission
  to admit malformed or unsupported syntax.
- Keep Algebra and Local admission distinct. Algebra callbacks require the
  appropriate totality and bound provenance; Local callbacks can stop. Initial
  supported types can exclude affine resources rather than invent ownership
  laws for them.
- Interpret indexed reads as checked reads. A static bound discharges a failure
  case; it does not redefine an invalid read to return an arbitrary value.
- Retain source identity, relation annotations, roles, sites, helper origins and
  preconditions separately from dynamic process equality. Equal processes can
  have different static contracts.

The first import gates are the actual `finite/total-state.mlir` and
`finite/unit-state.mlir` fixtures. They exercise a two-result accumulator and a
zero-result stopping fold, respectively. Result swaps and changed helper bodies
can be well-formed programs with different meanings; the checker must not
misclassify every semantic difference as malformed input.

## Initial checkpoint and next obligations

The maintained clients now prove complete process equations for both actual
exported fixtures, universally over vectors and scalar/Boolean inputs. The
total-state client returns the ordered pair fold. The unit-state client aborts
exactly when enabled and nonempty. Both retain the `2^64` vector-length admission
condition and prove refusal outside it. Transparent constructor data is checked
against fresh native exports; the proof clients compute admission of that data
and use the common region and finite semantics, rather than assuming a source
correspondence equation.

This establishes a usable import and proof interface for structured immutable
programs. It also exposes the next proof obligations: checked helper lookup,
semantic soundness of exact return-identity and bound propagation, and general
read safety under an explicit valid-input relation. Those results are needed
before using Math totality to justify eliminating or moving calls. They should
precede a generic native realization theorem; finite Runner comparisons remain
regression evidence for that later boundary.

The next whole-protocol extension should preserve open interaction and explicit
participant bindings for Schnorr, then add the matching quadratic Sumcheck native
subject and interactive repetition. These extensions reuse this declaration and
region boundary. They must establish the verifier contracts above before
transporting the existing security proofs to their imported subjects.

## Evidence boundaries

Formation proves typed interfaces. Static admission checks the selected profile's
additional contracts. A source-to-reference equation concerns the elaborated
Lean process. Native export tests check that the writer emits the intended
subject. These obligations have different owners and cannot replace each other.

The byte digest identifies a subject; it does not establish its meaning. The
export writer and native formation remain reviewed executable components. The
imported denotation does not prove frontend translation, participant projection,
finite realization, native backend arithmetic, runtime cleanup or capacity
behavior. Unbounded semantic equations require a separate realization relation
before they can justify claims about a bounded native execution.

MLIR's [language reference](https://mlir.llvm.org/docs/LangRef/) explains region
dominance and `IsolatedFromAbove`; zkc's native regions already require explicit
captures. Its [dialect conversion framework](https://mlir.llvm.org/docs/DialectConversion/)
checks configured legality. Neither mechanism supplies a denotational correctness
theorem by itself.
