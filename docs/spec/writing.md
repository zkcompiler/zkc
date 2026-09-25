# Specification writing rules

These are the editorial rules for the chapters listed in the
[specification index](README.md). They do not add protocol or implementation requirements.

## Content and structure

1. Define each object and its meaning directly. An obligation to supply a
   definition does not replace the definition of an adopted concrete profile.
   A parameterized interface is complete when its parameters and required laws
   are explicit; it need not select one implementation of those parameters.
2. Introduce a concept briefly, give its definition or rules, and add an example
   when it helps. Use descriptive titles. Do not impose the same subsection
   template on every topic or make old review IDs the reading structure.
3. State types, binding, quantifiers, assumptions and applicable domains.
   Define failure, empty cases and boundary behavior where they affect meaning.
   Reuse a named definition rather than restating it with a changed meaning.
4. Use grammar for syntax, judgments for validity, equations for mathematical
   computation, and precise algorithms for decoding or transition procedures.
   A declarative judgment need not prescribe its checking algorithm. Lean or
   MLIR syntax is not required to understand a general definition.
5. Distinguish definitions, derived properties and implementation requirements.
   Normative definitions and requirements remain normative without capitalized
   keywords. Mark examples and explanatory notes as informative; they add no
   independent requirement. A theorem statement is not its proof receipt.
6. Use `MUST`, `MUST NOT` and `MAY` for explicit implementation obligations and
   permitted choices, naming the responsible implementation or interface.
   Prefer ordinary declarative prose for mathematical definitions. Avoid
   unbounded recommendations where interoperability needs an exact rule.
7. Separate common objects and laws from selected profile parameters and
   restrictions. A profile gives its exact interpretation, accepted domain,
   format and failure behavior. An unselected extension stays outside adopted
   scope rather than receiving an invented default.
8. Keep design alternatives, research, historical decisions, proof inventories
   and implementation progress in their existing external homes. Retain semantic
   limits beside the definitions they qualify. When definitions move, update
   incoming references and Formal correspondence to their actual new homes,
   including every part of a split definition. Remove superseded files and
   navigation-only sections after checking those references. Historical receipts
   retain their original hashes and validation scope.

## Tone and notation

Write English in the present tense, using direct, neutral sentences. Prefer
"is", "consists of", "is defined by", "returns" and "evaluates to" when
describing objects and behavior. Use "if and only if" only for a definition or
an established equivalence, not for a sufficient checker condition.

Explain a symbol at its first use or cite the precise earlier definition.
Use one name consistently. Equations and their accompanying prose describe the
same model. Resolve a disagreement through review of the intended definition
and its Formal counterpart; neither implementation convenience nor a theorem
about another subject settles it automatically.

Keep paragraphs focused. Tables suit constructor signatures and parallel
constraints. Examples stay short and exercise an informative case such as a
failed continuation, ordered operand mismatch or repeated factor. Avoid repeated
status disclaimers, dense ownership preambles and a separate miniature checklist
after every definition.

## Reference example

The following specimen preserves the existing [sequencing definition](core/execution.md#sequencing).

### Execution sequencing

An execution consists of an outcome, a final state, and an ordered sequence of
events. Let `S` be the state type, `E` the event type, and `A` the result type.

```text
Stop = reject | abort | exhausted | incomplete | refused
Outcome A = returned(a : A) | stopped(r : Stop)
Execution S E A = Outcome A × S × List E
```

The function `follow` sequences an execution with a continuation. For a result
type `B`, the continuation has type:

```text
k : A → S → Execution S E B
```

Sequencing is defined by the following equations. All operands are well-typed,
and `++` denotes list concatenation.

```text
follow((stopped r, s, es), k) =
  (stopped r, s, es)

follow((returned a, s, es), k) =
  let (out, t, fs) = k a s
  (out, t, es ++ fs)
```

When the first execution stops, sequencing preserves its stop reason, state,
and events. The continuation is not invoked.

When the first execution returns, the continuation receives its returned value
and final state. The resulting execution retains the earlier events followed
by the continuation's events, including when the continuation stops.

*Example (informative).* If an execution records a request and then stops with
`exhausted`, sequencing preserves the request event and the state at exhaustion.
It does not execute the continuation.
