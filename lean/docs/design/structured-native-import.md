# Structured native import

## Purpose and subjects

The shared `Source.Region` carrier needs a checked connection to actual native
structured programs. Its generic formation laws do not establish that a native
helper, capture map, domain, or result list was imported faithfully. The former
`zkc.common-source/0` bridge expanded pure helpers and lacked declaration
identity and structured callbacks. It is retired; its maintained scalar clients
now derive views from the Structured reader.

Import the original protocol-profile module after native formation and before
preparation. Keep its declarations and contracts. Preparation can select finite
algorithms without scalar simplification, expands Local helpers, and eventually
realizes total mathematics. A snapshot taken there is a different subject; it
cannot establish the source side of a transformation it has already applied.

The Structured format is the sole retained-source format for formal admission. Native parsing and
verification precede export. Lean independently checks the supported vocabulary,
binding interfaces, declaration references and static profile restrictions before
constructing canonical regions. It supplies the operation meanings; input files
cannot supply a semantic oracle.

## Protocol verification targets

### Schnorr

The Schnorr target is the library's Interactive original-stage unit, together
with the maintained Helpers and Reordered forms. Its open verifier process
receives a commitment, queries the actual challenge service, sends the
challenge, receives an independent response, and returns the Schnorr equation's
Boolean result. This equation must hold for arbitrary replies and stopping
prefixes, with the public inputs and service binding explicit.

Each form exercises a different part of the import. Interactive tests
participant binding and retained metadata, including a dormant formula. The
Helpers form exercises named calls, while split-scope `first` controls
distinguish faithful component calls from an all-input approximation. Reordered
rearranges the verification equation. The admitted EarlyChallenge unit queries
before receiving the commitment and serves as a counterexample to the shared
verifier contract. [Support](../support.md#interactive-schnorr) states what is
proved about each form.

The Interactive prover's honest strategy is decoded from its actual checked
process instead of being written by hand or produced by a separate executor,
replay oracle or generic `ProverContract`. The decoder is deliberately partial
and reads only complete successful traces, so a stopped or partial run yields
no messages. Taking the commitment from one reference run is sound only because
the source sends it before receiving the challenge, its prefix does not depend
on the reply, and every challenge completes. The shared strategy constructor
therefore asserts no causality itself; each use rests on its source's process
equation. The
[verification specification](../spec/verification.md#prover-strategies-from-checked-sends)
defines the construction, and [support](../support.md#interactive-schnorr)
states what is proved about it. The separate
[native participant probe](../../bridges/structured/participant.md) compares
selected source-bound executions and stopping observations as bounded evidence.

### Sumcheck

The library target is the multilinear protocol in
`libraries/protocols/polynomial/sumcheck/lib.zkc`. Each round sends a pair `(a0, a1)`, checks the
current claim against `a0 + a1`, obtains a fresh challenge `r`, and updates the
claim to `(1-r) * a0 + r * a1`.
[Retained protocol repeats](../spec/structured-source.md#retained-protocol-repeats)
admit its runtime round count and repeated interactions.

`Reduce` returns an evaluation obligation. A separate public-table or opening
consumer must discharge that obligation before it yields an acceptance claim.
The full public-table protocol additionally needs vector operations and the
imported `has_shape` and `fix_prefix` helpers. Source records flatten into
ports; each pair message becomes two ordered scalar exchanges, so no tuple-valued
action or separate carrier is required. Count agreement
and valid native dimensions are explicit premises.

The two-round quadratic scalar verifier and its `4 / |F|` theorem serve as
regression clients. They are a different protocol from the
multilinear pair-message library. The independent
[multilinear foundation](../spec/multilinear-sumcheck.md) and
[optional security adapter](../spec/multilinear-sumcheck-security.md) prove
the table laws and complete/residual interactive bounds.
[Uniform queries](../spec/uniform-query-service.md#actual-imported-roots) supply
the source-specific causal experiment equation for the admitted library roots.

## Structural and semantic requirements

The maintained whole-unit profile has per-root participants/scopes, immutable
Booleans, unsigned indices, nominal BLS12-381 scalar/vector/group values, and
root-owned random-service handles. The nominal profile is exactly BLS12-381 Fr
and G1; a configurable profile is deferred until a consumer needs a second
domain. Closed Math/Local helpers remain separate from open roots. Math uses
optional named closures; Local calls sequence all arguments and run only at
their owner. Finite/control work remains available in closed Local bodies.
Multi-role roots refuse transitive Math folds and checked reads; the profile
admits no affine resources.

Both dialects instantiate `Source.Region`. One evaluator uses explicit
F/G and lawful module operations; SiteObservations abstracts only internal source
marks. Generic operation/Region/table naturality gives site erasure and closed
lifting. The checked closed view has a semantic correspondence at the same value
assignment, with complete one-role port scopes certified by the closed view.

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
  appropriate totality and bound provenance; Local callbacks can stop. The
  supported types exclude affine resources rather than invent ownership laws
  for them.
- Interpret indexed reads as checked reads. A static bound discharges a failure
  case; it does not redefine an invalid read to return an arbitrary value.
- Retain source identity, relation annotations, roles, sites, helper origins and
  preconditions separately from dynamic process equality. Equal processes can
  have different static contracts.

The actual `finite/total-state.mlir` and `finite/unit-state.mlir` fixtures gate
the import. They exercise a two-result accumulator and a zero-result stopping
fold, respectively. Result swaps and changed helper bodies
can be well-formed programs with different meanings; the checker must not
misclassify every semantic difference as malformed input.

## Proof interface and remaining obligations

The fixture proofs compute admission of transparent constructor data, which the
bridge checks against fresh native exports, and use the common region and finite
semantics rather than assuming a source correspondence equation.
[Support](../support.md#finite-fold-subjects) states their equations. Two
further results are needed before Math totality can justify eliminating or
moving calls: semantic soundness of exact return-identity and bound propagation,
and general read safety under an explicit valid-input relation. They should
precede a generic native realization theorem, for which finite Runner
comparisons are regression evidence. A general availability-soundness and
presence theorem and a native demand-projection relation are further
obligations.

The checked operation tree is the authority for helper references and instruction
counts. Deriving that inventory after formation avoids a second mutable list
that can drift when a new operation or region is added. The inventory includes
the full helper signature and is proved equal to the typed body's erasure.
The independent linking check supplies unique declaration names and exact
signature membership in each strict prefix. Lookup laws expose the corresponding
body; table-frame laws isolate the helper meanings each region actually uses.

Two authored scalar Entries exercise this interface on actual prepared exports:
the retained native original and the output of
`zkc-opt --zkc-prepare-protocol="simplify=false optimize-finite=false"`.
Each pair's equation is specific to that pair and its checked named body
contracts; the reusable part is the inlining law, which needs a process equation
rather than a Math-totality assumption. [Support](../support.md#helper-inlining-pairs)
states the equations, and the
[bridge](../../bridges/structured/README.md#scalar-inlining-pairs) regenerates
the subjects.

The linker independently validates exact links in the proposed order. It does
not prove that sorting preserved every input declaration or body; preservation
and candidate-generation completeness remain separate properties. Proving the
whole Kahn implementation would couple each lookup client to incidental sorting
and lowering details. A small decidable predicate instead checks exact helper
signatures in the preceding declarations and supplies its proof to `Payload`.
The cost is another bounded traversal of at most 128 declarations and the formed
helper inventory. Name lookup remains simple; typed declaration indices would
be worth revisiting if substitution or linking proofs demonstrate a concrete
benefit.

Keep identity analysis separate from typed formation. Its proof needs an explicit
environment invariant: positions with the same known origin denote the same
value, and each retained index/container fact holds for those values. Calls
transfer that invariant through return summaries; folds discharge bounds using
domain items and invariant arguments/captures. A totality theorem must quantify
over valid inputs satisfying the function's declared preconditions. Merely
moving this analysis after formation would not prove these semantic properties.

## Evidence boundaries

Formation proves typed interfaces. Static admission checks the selected profile's
additional contracts. A source-to-reference equation concerns the elaborated
Lean process. Native export tests check that the writer emits the intended
subject. These obligations have different owners and cannot replace each other.

The byte digest identifies a subject; it does not establish its meaning. The
export writer and native formation are reviewed executable components.
Unbounded semantic equations require a separate realization relation before they
can justify claims about a bounded native execution.

MLIR's [language reference](https://mlir.llvm.org/docs/LangRef/) explains region
dominance and `IsolatedFromAbove`; zkc's native regions require explicit
captures. Its [dialect conversion framework](https://mlir.llvm.org/docs/DialectConversion/)
checks configured legality. Neither mechanism supplies a denotational correctness
theorem by itself.

## Primitive declaration and evaluation ownership

Primitive bindings are retained separately from callable declarations. The
closed fifteen-operation vocabulary exposes ordered ports independently of its
evaluator, avoiding an import cycle through helper meanings. One Local exec
operation uses `PIR.Outcome` and `Process` stops; pure index expressions
remain distinct calculations. Full-table framing and effect translation add one
family case. Binding names and helper origin names supply no semantic authority.

Conditional source contracts use the library's own helpers selected through
ordinary authored wrappers and the complete original-stage dependency closure.
An indexed finite-fold invariant belongs to `Source.Finite`; it applies callback
equations only at reached states/indices, which is necessary for bounded doubling
in the shape helper. The source import boundary retains original bytes, digest,
constructor subject and kernel admission separately from the resulting equations.
The full Sumcheck source additionally uses retained maps, protocol applications
and repeats, specified in [structured source](../spec/structured-source.md).
