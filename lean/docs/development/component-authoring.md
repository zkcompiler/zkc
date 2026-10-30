# Authoring proofs from reusable components

The source program fixes the execution and its relation applications. A Lean
library supplies mathematics and proofs about that execution. Generated bindings
connect the two. A receipt proves the request's fixed meaning; a method cannot
replace the relation, verifier, extractor, model or requested stage.

```mermaid
flowchart TD
  S[Joint protocol source] --> I[Independently admitted structured program]
  I --> B[Checked body and boundary bindings]
  M[Mathematical references and family laws] --> C[Component contracts]
  B --> C
  C --> A[Connections and structural composition]
  T[Fixed source target and input clauses] --> A
  A --> H[Actual honest execution proof]
  A --> D[Adversarial soundness derivation]
  H --> R[Canonical request receipt]
  D --> R
```

## Choose what is new

| Change | Author-owned mathematics | Reused infrastructure |
|---|---|---|
| Compose installed components | Root target coverage and any new connection law | Body binding, call/role routing, composition and request checking |
| Change a representation | Decode/readback, helper and update laws; exact sampler law if it changes | The existing mathematical reference and family security theorem |
| Add a family | Reference, honest computation, invariant or certificate, bad-event bound and terminal adequacy | Process semantics, derivation rules, fixed meanings and receipt checking |
| Add a proof method | A proof of the existing meaning, possibly using a checked certificate | The same request and property semantics |
| Add a security property or execution stage | A separately reviewed fixed meaning and its correspondence laws | Registration and receipt machinery after that meaning is installed |

These categories describe responsibilities, not a promise that every source
shape already has a generator. An unsupported shape must produce an explicit
obligation or refusal. A new method is an ordinary indexed Lean proof; it does
not require global type-class search or a second interpreter.

## Define the mathematical boundary

[`ClaimRelation`](../../Zkc/Obligations/ClaimRelation.lean) separates an
affirmative witness relation from `No`. Exact relations can use the complement
of validity. Proximity contracts instead retain a gap: a word can be outside the
code without being far enough for the soundness theorem. Matching affirmative
predicates alone does not justify transporting `No`.

A source relation has one fixed interpretation. A formula uses its admitted
Math body. An opaque relation uses an installed registry entry with the exact
family, version, typed static arguments, flattened ABI and argument purposes.
That installation belongs to the mathematical library. Evidence supplies a law
about the installed interpretation, rather than a replacement predicate.

The reference can come from a checked analysis of the joint program, an installed
component or authored mathematics. Honest-producer correspondence proves that
the actual producer computes this reference on valid inputs. It does not make
whatever the producer happens to compute the definition of truth. GKR's circuit
evaluation and the separate extensions of its four gate factors illustrate why
this distinction matters.

## Keep source facts independent of the proof method

The core `Zkc.Source.Structured` modules own input visibility, source-template
association, occurrence presentation and loop presentation. Their theorems have
no probability or security-package dependency. A mathematical library can reuse
these facts for either participant, with the full returned row and visibility
mask preserved. Construction certificates use the same visibility laws when
connecting the source to its compiled participant.

Mathematical family laws live under `ZkcSecurity.Families`. Adapters that read
particular source templates, layouts or exported programs live under
`ZkcSecurity.Bindings`, even when that adapter is reusable across several
programs in one family. For example, the Sumcheck source adapters reuse its table
mathematics without making the mathematical family import concrete programs.
Restricted proof elaborators may be shared by these layers; source emitters and
example catalogues remain outside the mathematical dependency boundary.

A displayed process is a derived view. The untrusted `ZkcTools.ProcessView`
elaborator checks definitional equality to its input expression; it supplies no
separate evaluator. The present-input printer additionally emits a theorem from
the admitted source to its checked normal form. That theorem covers the selected
available-input pattern. Adversarial claims must use the appropriate optional
input pattern and cannot infer universal input availability from this view.

## Install source presentations and counted loops

`install_source_template association using_pattern pattern` applies the existing
exact source association. It checks the complete signature and raw typed body,
then infers the role, context, arguments, captures and full masked return from
the goal. It computes only visibility and scope side conditions. A missing
mathematical body equation remains an ordinary Lean goal. The Sumcheck family
uses this installer for both participants; SmallSumcheck and TwoSums select the
same reusable family with different bounds.

A counted reference can expose checked zero/successor equations ending in
`index`, `count` and the complete state. The callback must be independent of the
remaining count, and the continuation must increment the index by one. The
installer reads the existing recursion equation and applies the corresponding
`LoopContracts` theorem; it does not interpret a second loop language.

- `install_source_loop_no using_invariant invariant using_rules [rules]` carries
  the actual reached history, current index, remaining count and complete-state
  No invariant.
- `install_source_loop_pair using_invariant invariant using_rules [rules]`
  carries both complete honest states and requires the terminal paired relation.
- `install_source_loop_cost per_iteration price using_rules [rules]` bounds
  every callback state and reply, independently of No or honest execution.

The author still supplies the invariant, callback mathematics and any budget
inequality. Missing premises remain typed goals; unsupported continuation or
frame shapes cannot establish a theorem. Nested loops compose by installing an
inner loop contract as the outer callback. GKR's output and layer rejection
proofs now use this shared induction, while retaining their existing polynomial
and Sumcheck mathematics. This removes repeated induction structure; it does
not yet eliminate GKR's representation or physical-placement proofs.

## Bind one component

[`ComponentInterface`](../../Zkc/Obligations/Component.lean) records:

- the actual `PIR.Process` body and its runtime arguments;
- logical parameters and input/output claim relations;
- a scope over the runtime arguments and reached transcript history;
- partial input and output readbacks, returning `Option`.

Logical parameters can contain an original table or circuit used in a proof.
They do not become verifier-readable inputs. A missing runtime observation is
`none`; it cannot be replaced with a convenient mathematical value.

`SoundnessContract` consumes both the actual scope and a defined input `No`, and
produces a derivation for the output `No`. `SoundnessContract.ofFamily` reuses a
family through an exact body equation and checked entrance/exit implications.
The same body equation is available to honest execution proofs. It covers all
replies and stops, rather than only a successful trace.

For Sumcheck, the reusable reference is the residual sum after a prefix; the
family proves the round polynomial's boundary, degree and evaluation laws. A
representation supplies the concrete message/readback and restriction equations.
For GKR, the split-variable layout proves which factor is independent of the
active variable. A generic four-factor product cannot silently inherit the
degree-two bound.

## Prove the connections explicitly

A `Connection` contains an actual runtime route, a mathematical statement map
and a commuting readback equation. Its honest and sound uses share that equation
but require different logical laws. A matching field type is not a connection
proof: swapped claims, points or circuit layers can have identical types.

Pure helper conversion needs its actual helper equation, an operational domain,
defined readback in that domain, and preservation of the selected relation.
Opening or repacking a pending claim carries its obligation forward. A terminal
law explains why the actual returned accepting value discharges that obligation.
A conversion that queries an oracle or samples a challenge is a component with
its own execution and cost law.

The caller must establish the next scope at the reached state. In a conjunction,
the first component might process a true claim while only the second claim is
false. Therefore frame and scope preservation cannot depend on the first
claim's `No`. The generic
[`Assembly`](../../Zkc/Obligations/Assembly.lean) rules retain this independent
premise, both return values and the complete history. Honest composition likewise
threads actual producer/verifier state and the shared cache; a cold-start success
theorem for each component is insufficient.

## Close the root and inspect the receipt

The root supplies coverage from its fixed false target to the component
obligations, and an adequacy law from the final residual to actual acceptance.
Completeness additionally supplies the actual honest producer and input
preparation, including all failure and stopped mass. Structural generation can
assemble installed laws; it cannot invent a new polynomial identity, degree
bound, sampler law, application relation or extraction algorithm.

Inspect the request's property, model, target, input policy, stage and error
before interpreting `established`. A source-process theorem, an ideal compiled
receipt and a byte-level execution theorem have different correspondence
requirements. Cryptographic assumptions and stage links remain visible even
when the component proof is reused.

The [selected property adapters](../spec/selected-property-adapters.md) give
concrete limits: KZG's unconditional reduction and opening client are component
results; fixed two-cell recovery is a separately registered extraction property.
Neither supplies general computational hardness or committed-oracle knowledge.

When measuring author work, include reference/helper proofs, relation and
connection laws, configuration and generator extensions. Generated source size
and kernel checking cost are separate measurements. Moving a proof into a helper
does not make that work disappear.


## Source-addressed Lean companions

`ZkcTools.Companions` indexes ordinary Lean declarations with `@[zkc "identity"]`.
The source owner supplies the identity; the assembler fixes the expected type
before lookup. A generic declaration can serve multiple static instances. An
explicit instance takes precedence over its template, and an ill-typed explicit
instance is refused rather than replaced by a template proof. For example, the
checked API control uses:

```lean
@[zkc "Counter.base"] theorem base (n : Nat) : n + 0 = n := Nat.add_zero n

example : 3 + 0 = 3 := zkc_companion ["Counter.base"[3]]
example : 11 + 0 = 11 := zkc_companion ["Counter.base"[11]]
```

Contract values use the same lookup as proofs. An assembler supplies the actual
`LoopContract` or scope type, including its parameters; discovery cannot choose
a different contract. Registrations survive imports. Two visible declarations
for one identity are ambiguous, and registrations for removed identities are
reported as orphans.

`Companions.assemble` accepts an ordered list of default proof proposals. An
explicit companion overrides those proposals. A missing companion allows the
defaults to run; an unfinished explicit companion remains open. Every accepted
term has the fixed expected type and no unresolved metavariables or transitive
`sorry`. The enclosing declaration is kernel checked. Receipt acceptance still
requires its own exact meaning, premise, axiom and stage-link audit.

`Companions.report` records the actual attempted obligation, its source identity
and span, responsibility, expected type, method failures and stub location.
These authoring statuses are separate from canonical receipt statuses. Static
proof-search addresses do not become source labels or random-oracle keys.
`appendStubs` only appends unseen identities and never rewrites an existing
companion file. A proof stub uses Batteries' `proof_wanted`; a value stub is a
commented declaration template. In the pinned Batteries version, `proof_wanted`
creates a private `ProofWanted P` placeholder, which contains no proof of `P`.
The lookup recognizes that placeholder as an open obligation. The printer adds
the registration with a separate `attribute` command because the pinned wanted
command does not preserve arbitrary declaration attributes.

The lookup, ordered method selection, report and append-only printer are checked
in `Tests.Companions`, `Tests.CompanionAssembly` and `Tests.CompanionReport`.
Their integration with generated frame/goal modules and the source authoring
command is a separate assembly step. The existing module-level method selection
remains active until that cutover; this API does not implement claim defaults or
change the request registry.
