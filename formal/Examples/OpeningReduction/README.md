# Virtual-product Sumcheck and opening obligations

This executable example tests the selected PIR semantics on a product of three
multilinear tables, arbitrary adaptive rounds, and a consumer of the actual
returned evaluation claim. It is built and audited with the main formal package.
Its domain types remain example APIs pending the contrasting memory/FRI clients.

## What executes and what is proved

For fixed tables `A,B,C : {0,1}ⁿ → F`, the virtual polynomial is
`P(x) = MLE(A)(x) * MLE(B)(x) * MLE(C)(x)`. Each coordinate has degree at most
three. The representation keeps the three factors; it never replaces their
product with the multilinear extension of the pointwise product table.

```text
claimed Boolean sum
    → typed loop: receive cubic message, check boundary, draw, update claim
    → returned scalar and ordered challenge point
    → receive three values and check their product
    → ordered obligations A(r)=a, B(r)=b, C(r)=c
    → separately supplied terminal verifier
```

The verifier source takes neither the private tables nor a private-polynomial
evaluation oracle. `Execution.run` executes the actual typed `Source.program`.
`Openings.run` sequences its result with the reported-value consumer using the
common complete-execution operation. Reporting is currently a supplied callback;
it is not yet another serialized source region or a cryptographic opening proof.

| Module | Concrete result |
|---|---|
| [Polynomial](Polynomial.lean) | Executable table restriction and four-coefficient round construction; exact evaluation and Boolean-sum laws; cubic collision bound |
| [Rounds](Rounds.lean) | Honest completeness and ordinary soundness `3n/|F|` for arbitrary adaptive strategies and independent uniform challenges |
| [Source](Source.lean) | Explicit sorts, operations and bounded loop; independent recursive denotation; at most `2n` interface calls including early rejection; actual generic lowering preserves complete execution |
| [Execution](Execution.lean) | Arbitrary stateful send/react callbacks; returned source claim corresponds to the mathematical residual test |
| [Openings](Openings.lean) | The actual prefix result determines three ordered claims; arity and product checks; truth of every returned claim implies the residual equation |
| [Acceptance](Acceptance.lean) | Common arbitrary-witness realization binds the actual source residual, arity, product check and complete output bundle; a following consumer checks those same obligations |
| [Security](Security.lean) | Actual composed execution has false-acceptance probability at most `3n/|F| + ε`, provided its terminal false-opening event has mass at most `ε` |
| [MultiplePoints](MultiplePoints.lean), [Batching](Batching.lean) | Equality-weighted two-point identity and a fixed-input batching proof using the same engine; conservative bound `(1+3n)/|F|` with a true-residual terminal |
| [Controls](Controls.lean) | Exact two-round outputs, states and events; failure, forged-value, identity, coordinate and polynomial-flattening controls |

The algebraic laws hold over commutative rings. Root counts and probability
theorems require finite fields. The coefficient construction uses no division
by interpolation constants. The bounds remain valid but can exceed one for
small fields. These are ordinary interactive statements, not FS, extraction,
zero knowledge or a polynomial-time analysis.

The terminal theorem splits acceptance into “the returned obligations are true”
and “the terminal accepted a false bundle.” Both events refer to the same reached
execution; independence between them is unnecessary. Its current terminal is
`Bundle → Bool`. Integrating a real PCS still requires actual proof messages,
verification/public state, object-binding assumptions, and an adversary/experiment
map establishing that error bound. A PCS theorem for unrelated fixed queries
does not discharge it. The example does not yet implement that larger terminal.

## Concrete execution and negative controls

Over `F₁₇`, take all three factors to be `x+y`, while retaining three distinct
object identifiers. Their Boolean sum is 10. With challenges `[2,3]`, the first
message has coefficients `[1,3,3,2]` and the second `[8,12,6,1]`. The source returns
scalar 6 and point `[2,3]`; the reporter supplies `[5,5,5]`, whose product is 6.
The exact output retains all three object/point/value occurrences.

The controls establish more than honest evaluation:

- A wrong first boundary stops before drawing or reporting.
- Exhaustion in round two retains the second message and first challenge.
- A wrong reported product stops after both draws and preserves unused coins.
- Reports `[1,1,6]` pass the product check but produce false obligations. The
  reference truth checker rejects them; an always-accepting terminal triggers
  the false-opening event used by `Security.soundness`.
  They also satisfy the output-realization constraints, while no satisfying
  witness for this run can close with all openings true. Realizing an output
  faithfully and proving its obligations are different claims.
- Wrong point arity is refused; swapping coordinates or object identities can
  change validity; deleting an obligation can hide failure.
- Materializing only the Boolean product values preserves the initial sum but
  changes the residual polynomial. It cannot justify this protocol rewrite.

## Comparison with the parallel quadratic composition

The [composition consumer](../../consumers/composition/README.md)
reduces claims about two potentially different tables and points through the
existing quadratic representation, with bound `(1+2n)/|F|` and a perfectly sound
logical terminal. Its machine-encoding results are separate from this example.

Both approaches are useful references. The specialized quadratic engine gives
the tighter bound for the equality-weighted workload. The cubic engine is needed
for the genuine three-factor product. Its two-point instantiation deliberately
tests reuse with a looser bound; it does not supersede the quadratic proof or
implement the other package's two-object terminal. Shared degree/table/claim
APIs should follow these distinctions, not erase them.

## Compiler and external-library consequences

| Retain until the relevant decision | Reason and current evidence |
|---|---|
| Factor identity, multiplicity and virtual-expression provenance | `flattening_changes_residual` rejects an apparently plausible Boolean-table replacement |
| Per-phase degree and message representation | Four coefficients admit genuine cubic rounds; a constant third factor admits quadratic specialization |
| Ordered axes and challenge prefix | Restriction laws and source outcomes agree on first-coordinate-first evaluation |
| Residual claims as values, separate from acceptance | `close_sound` needs every obligation; the forged-value control disproves product-check-only acceptance |
| Message/check/draw order and failure state | Early rejection and exhaustion have different retained executions |
| Public derived objects versus committed/private tables | Equality weights are computed from public points; they do not need an invented commitment |

These are requirements on the forthcoming MLIR design. The table tree is an
executable reference, not a buffer layout; the common `Proc` denotation is not
a mandate to flatten protocol or algebraic source. No native operation, pass,
artifact format or Rust implementation is added by this example.

The theoretical basis is multilinear interpolation, polynomial root bounds,
induction over adaptive rounds, conditional bad-event composition and typed
source interpretation. Thaler's notes, §§2.3–2.4, give the interpolation and
Sumcheck construction; Jolt's opening description supplies a real composition
workload. Neither is a theorem provider imported here.
[Thaler](https://people.cs.georgetown.edu/jthaler/extensionsandsumcheck.pdf),
[JoltBook](https://jolt.a16zcrypto.com/how/architecture/opening-proof.html).

ArkLib's pinned `General.lean` describes degree-indexed polynomial-oracle rounds,
sequential reductions and a residual statement. Reuse is plausible, but needs a
table-to-polynomial evaluation/degree law, coefficient/oracle correspondence,
matching adversaries and the selected terminal. Its documented check occurs
after the challenge; our early rejection can consume fewer draws. Verdict
correspondence therefore cannot silently become complete-execution equality.
Source inspected: [ArkLib at the package pin](https://github.com/Verified-zkEVM/ArkLib/blob/3f3f045dd295834c262bd6f0d9dfdfee07cc8e76/ArkLib/ProofSystem/Sumcheck/Spec/General.lean).

Existing [scalar adapters](../../integrations/arklib/ZkcArkLib/Sumcheck/Scalar.lean)
and [PolyFun execution adapters](../../integrations/arklib/ZkcArkLib/PolyFun/Blocks.lean)
remain useful distinct reuse routes. They do not already prove correspondence
for this example. No new ArkLib/VCVio theorem or dependency is imported here.

## Run and next boundary

From `formal/`:

```sh
lake build Examples.OpeningReduction.Controls ZkcTests
```

Main audit imports include every example module. All new theorem proofs are
kernel checked; the declared axiom policy remains `propext`, `Classical.choice`,
`Quot.sound`.

The next shared design should consume this example and the quadratic/machine
follow-up together: select a memory-log encoding, keep its same-machine adequacy
obligation, and expose the actual opening-proof/provider boundary. Review the
retained MLIR structures alongside those clients. Full field arithmetization,
PCS security, heterogeneous layouts, compact certificates and native differential
execution keep their separate concrete deliverables. No extra universal semantic
framework is required by the present results.
