# Lean toolchain

Both Lake packages pin **Lean 4.36.0**, the final release at commit
`611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9`. The compiler package has no external Lake
dependency; the formal package requires `../compiler`, Mathlib and VCVio. Install the pins through elan and
use the [development commands](development.md). Keep package pins identical and rebuild
artifacts for the selected compiler; build caches from different Lean versions are incompatible.

The active default targets are the core, vocabulary, subject library, core and vocabulary tests, and audit.
The separate `just test-interactive` target uses the same pins for selected source entries
and their proofs. The full CLI and historical formal suite still await migration.

## Audit and executable trust

Lean 4.36 [generates native constructor-index implementations](https://github.com/leanprover/lean4/pull/15407).
For an ordinary datatype with zero or multiple constructors, `T.ctorIdx` is a logical case analysis and
`T.ctorIdx._impl` reads the runtime constructor tag. Their `implemented_by` attribute is normal
compiler output, but allowing every such attribute would also allow arbitrary project code.

The audit's [recognizer](../lean/compiler/Zkc/Tools/Audit/CompilerHelpers.lean) reconstructs
both expected definitions from the datatype. It checks the parent, constructor count, target
name, universes, safety, types and complete bodies. Runtime builtin datatypes, additional native
attributes and any mismatch or Meta error are refused. Matching the generated form is a
compiler compatibility rule, not a proof of the compiler or runtime.

Logical declarations still undergo kernel replay, and their actual dependency closure must
use only `propext` and `Quot.sound`. The existing exception for Lean's recursive implementation
code remains. The audit reports partial definitions, recursive implementations and recognized
constructor indices separately so a new native dependency is visible. Unsafe code is outside
the kernel's logical check. No project native override or native-decision axiom is newly
admitted by this upgrade.

The audit accepts generated public, private, empty, indexed, mutual, nested and polymorphic fixtures and
rejects counterfeit logical bodies, native bodies and replacement targets. Private `extern`
and `implemented_by` controls verify that the imported private metadata remains visible.
Ten isolated mutations additionally check the recognizer during its build. The complete
suite has 16 negative controls; every control must fail by its intended rule.

Lean 4.36 also removed a redundant natural-number equality instance. Default instance search
now finds `LawfulBEq Nat` through the order of naturals, and a proof that uses it (for example
`eq_of_beq` on naturals, or a `simp` lemma about `==`) then depends on `Classical.choice`. The
core declares one scoped instance, in `Zkc/Core/Program/Identity.lean`, that takes the fact from
the decision of equality instead. It applies inside `Zkc.Core` and its namespaces, which is
where the core and its tests are, and to nobody who only imports the core; it changes no
statement. A successful build alone does not establish that no proof reaches the axiom; the
audit does.

## Using the release's new facilities

The final [4.36 release](https://github.com/leanprover/lean4/releases/tag/v4.36.0) includes changes
beyond the release-candidate notes. In particular, safe `withPtrEq` was restored with a compiler
check, and the proposed suppression of proof-only realized constants was reverted. Base feature
choices on the final compiler, not an intermediate release description.

- **Pointer equality:** the checked `withPtrEq` can accelerate equality on concrete data such
  as `List Nat`, while remaining definitionally equal to its structural fallback. It cannot
  generally accept polymorphic types containing erased type data. Never use pointer identity
  as a program identity, fact identity or receipt key. A native benchmark of the value table's
  operand-comparison pattern showed gains for shared lists but no gain for equal fresh lists;
  the latter path constructs the operands used by the current analysis. Consequently the
  value table keeps its structural comparison. Introduce this fast path only with an actual
  consumer that preserves sharing and evidence for its complete workload.
- **Arithmetic automation:** `Sym.Arith` and the new opt-in `grind` normalizer can produce
  ordinary checked laws in mathematical adapters. They do not belong in the minimal core's
  imports. A field identity does not by itself preserve an operation's domain, failure behavior,
  effects or protocol observations. Inspect the resulting proof's dependencies before placing
  it in a library; stronger automation does not waive that library's axiom policy.
- **Program logic:** `Std.WP` interprets any program type as a predicate transformer with a
  postcondition for exceptions, and `vcgen` walks a program with the specifications it is given.
  The core's "on every path" of a process is such a transformer and a claim about a definition
  is its Hoare triple, so proofs about concrete definitions are to be discharged through an
  adapter to `Std.WP` rather than through an engine of our own. The adapter is outside the
  core: the assertion lattice of `Std.WP` depends on `Classical.choice`, and `vcgen` is still
  marked experimental. It states that a triple is a claim of the core, so the core's theorems
  do not depend on it. WP is not a replacement for protocol processes, adversarial interaction
  or probabilistic security statements.
- **Evaluation in proofs:** tests decide with `decide +kernel`, which depends on no axiom. The
  `cbv` tactic is an alternative where kernel evaluation of a decision is too slow; its proofs
  depend on `propext` only, which the policy allows.
- **Deriving:** `deriving DecidableEq` still does not apply to mutual nested types, so the
  decision of equality of stored programs stays written by hand.
- **Bit-vector automation:** `bv_decide +uf` can help discover identities, but this release's
  native certificate path introduces native-decision axioms. It is not accepted under the
  core's existing axiom policy; an option named `+kernel` does not remove that dependency.
- **Build and elaboration:** the release's typeclass-cache and compiler improvements apply
  automatically. Lake splits elaboration and code-generation jobs; job counts across versions
  are not performance measurements. Use `LEAN_NUM_THREADS` to respect the worker budget.
  Semantic fact caches still need their own scope/model/observation dependencies; Lean's
  environment generation is not a version of a zkc program.

There is no new dependency on a mathematics or security library. Future adapters must pin a
coherent 4.36-compatible dependency graph and preserve the core's import boundary. A package
that remains pinned to 4.35 cannot supply `.olean` proofs to this compiler unchanged.

## Checking an upgrade

Start with changed modules and adversarial audit controls, then run `just test` and `just check`
on the final candidate. Confirm both the positive generated-helper control and all refusals,
not merely the command's absence of compiler errors. Review the reported axioms and native
implementation counts. If an additional supported package is attached, build, test and audit
it with the same toolchain and its own stated policy. CI currently runs only `just check`;
its success is not evidence that Lean builds or proofs passed.
