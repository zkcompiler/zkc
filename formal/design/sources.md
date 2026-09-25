# References

Primary research, official documentation and selected source implementations
behind the formal design chapters. Papers establish their published scope;
repository documentation does not establish a tested dependency combination.
Design recommendations and countermodels elsewhere in these chapters are zkc
analysis, not reported external capability.

External tools are described from primary sources and selected source APIs. No
compatible upstream lockfile is established here: before adoption, record exact
revisions and build the actual zkc client. The broad theory already applied to
PIR is documented in the [theory reference](../../docs/theory.md).

## S1

CompCert project. [CompCert C: a trustworthy compiler](https://compcert.org/man/manual001.html).
Official manual, especially semantic preservation and compiler trust boundaries.
Used as a methodology reference, not a claim that CompCert compiles zkc's Rust
or proves MLIR semantics.

## S2

Xavier Leroy. [Formal Verification of a Realistic Compiler](https://xavierleroy.org/publi/compcert-CACM.pdf).
*Communications of the ACM* 52(7), 2009, pp. 107–115. Pass decomposition,
semantic preservation and realistic compiler verification.

## S3

Yong Kiam Tan, Magnus O. Myreen, Ramana Kumar, Anthony Fox, Scott Owens and
Michael Norrish. [The Verified CakeML Compiler Backend](https://cakeml.org/jfp19.pdf).
*Journal of Functional Programming*, 2019; linked author manuscript, 59 pages.
Also the official [CakeML project](https://cakeml.org/). Used for the alternative
of a verified executable compilation/runtime stack and explicit intermediate
semantics. No cross-prover zkc integration is established.

## S4

Carmine Abate, Roberto Blanco, Deepak Garg, Cătălin Hriţcu, Marco Patrignani and
Jérémy Thibault. [Journey Beyond Full Abstraction: Exploring Robust Property
Preservation for Secure Compilation](https://arxiv.org/abs/1807.04603).
*CSF*, 2019, pp. 256–271. Basis for distinguishing common-context execution
relations from robust trace/hyperproperty preservation against target contexts.

## S5

Lean project. [Axioms](https://lean-lang.org/doc/reference/latest/Axioms/), official
reference; latest documentation is version-sensitive. The exact locally inspected
implementation is Lean **v4.33.1**:
[Native.lean](https://github.com/leanprover/lean4/blob/v4.33.1/src/Lean/Meta/Native.lean)
and [Decide.lean](https://github.com/leanprover/lean4/blob/v4.33.1/src/Lean/Elab/Tactic/Decide.lean).
The local `BVDecide/Prover/Bitblast.lean` also calls `nativeEqTrue`. This source
inspection and the local benign experiment support the native-evaluation trust
distinction. They do not themselves constitute a package rebuild.

## S6

MLIR project. [Interfaces](https://mlir.llvm.org/docs/Interfaces/), official
documentation. Extensible operation semantics and interfaces are engineering
facilities; PIR-specific effect laws need their own interpretations.

## S7

MLIR project. [Dialect Conversion](https://mlir.llvm.org/docs/DialectConversion/),
official documentation. Conversion targets, legality and type conversion do not
by themselves prove preservation of a protocol's semantic experiment.

## S8

Silvain Rideau and Xavier Leroy. [Validating Register Allocation and Spilling](https://xavierleroy.org/publi/validation-regalloc.pdf).
*CC 2010: Compiler Construction*, LNCS 6011, pp. 224–243, 2010;
[author bibliography](https://xavierleroy.org/bibrefs/Rideau-Leroy-regalloc.html).
A dataflow-based validator with
a mechanized soundness proof is the concrete precedent for combining verified
components and validation of an untrusted producer's result.

## S9

Patrick Cousot and Radhia Cousot. [Abstract Interpretation: A Unified Lattice
Model for Static Analysis of Programs by Construction or Approximation of
Fixpoints](https://www.di.ens.fr/~cousot/COUSOTpapers/POPL77.shtml).
*POPL*, 1977, pp. 238–252. Basis for sound approximation, semantic interpretation
of facts and invariant/post-fixpoint checking.

## S10

C. A. R. Hoare. [An Axiomatic Basis for Computer Programming](https://www.cs.ox.ac.uk/publications/publication8205-abstract.html).
*Communications of the ACM* 12(10), 1969, pp. 576–580, 583. Contract and
composition foundation; the linked institutional record confirms bibliography.

## S11

John C. Reynolds. [Separation Logic: A Logic for Shared Mutable Data Structures](https://www.cs.cmu.edu/~jcr/seplogic.pdf).
*LICS*, 2002, pp. 55–74. Local reasoning and separation/frame obligations for
mutable resources. The dossier does not claim the whole current library is an
embedding of separation logic.

## S12

Nick Benton. [Simple Relational Correctness Proofs for Static Analyses and
Program Transformations](https://nickbenton.name/correctnesspopl2004.pdf).
*POPL*, 2004, pp. 14–25; linked revised author version. Foundation for relations
between executions and transformation correctness beyond literal state equality.

## S13

Siddharth Bhat, Alex Keizer, Chris Hughes, Andrés Goens and Tobias Grosser.
[Verifying Peephole Rewriting In SSA Compiler IRs](https://arxiv.org/abs/2407.03685).
*ITP*, 2024. Also the [Lean-MLIR repository](https://github.com/opencompl/lean-mlir).
SSA/region and rewriting infrastructure; current effectful zkc adequacy and
dependency compatibility require the proposed implementation experiment.

## S14

CSLib contributors. [Transition-system simulation implementation](https://github.com/leanprover/cslib/blob/main/Cslib/Foundations/Semantics/LTS/Simulation.lean).
Inspected API includes composition and trace lifting. No terminal-state/PIR
adequacy theorem or installed zkc dependency is inferred from this API.

## S15

Mathieu Fehr, Yuyou Fan, Hugo Pompougnac, John Regehr and Tobias Grosser.
[First-Class Verification Dialects for MLIR](https://users.cs.utah.edu/~regehr/papers/pldi25.pdf).
*Proceedings of the ACM on Programming Languages* 9, PLDI, Article 206,
June 2025, 25 pages. DOI: 10.1145/3729309. Modular semantic dialects, verification
tools and analysis-transfer checks; the dated comparison with Lean-MLIR is not
an audit of current upstream support.

## S16

Opencompl contributors. [xDSL-SMT](https://github.com/opencompl/xdsl-smt).
Official implementation documentation for supported partial lowerings,
translation validation and PDL checking. Used as a complementary candidate;
no Lean proof bridge or complete dialect coverage is claimed.

## S17

Son Ho and Jonathan Protzenko. [Aeneas: Rust Verification by Functional
Translation](https://arxiv.org/abs/2206.07185).
*Proceedings of the ACM on Programming Languages* 6, ICFP, Article 116,
2022, pp. 711–741. LLBC, ownership-based functional translation and verification
methodology; a paper-level semantics is distinct from the entire current tool's
implementation trust boundary.

## S18

Aeneas contributors. [Aeneas repository](https://github.com/AeneasVerif/aeneas),
especially “Targeted Subset And Current Limitations,” “Backend Support,” and
external-definition models. Documents the supported subset, nested-loop and
mutable-reference/generic limitations, and current unsafe/concurrency work.
Those limitations may change; pin and test the actual implementation slice.

## S19

Cryspen. [hax](https://hax.cryspen.com/) and
[Lean quick start](https://hax.cryspen.com/manual/lean/quick_start/).
Official documentation confirms a Lean backend. The existence of a backend
does not establish its equivalence with other backends, soundness for arbitrary
Rust, or compatibility with zkc's dependency set.

## S20

Natalia Klaus, Juan Conejero and Palina Tolmach. [A Rust-to-Lean Verification
Pipeline with AI Provers: An Experience Report](https://arxiv.org/html/2605.30106v2).
arXiv:2605.30106v2, 2 July 2026. Reports cryptographic Rust targets, extraction,
mathematical specification and proof engineering, including rewritten models
and toolchain friction. Used as feasibility evidence and a model/implementation
boundary warning; its artifacts were not independently reproduced here.

## S21

Verus contributors. [Verus](https://github.com/verus-lang/verus), official project
description. Solver-based verification of a supported Rust subset, with some
low-level pointer reasoning. No automatic Lean proof import is asserted.

## S22

Creusot contributors. [Creusot](https://github.com/creusot-rs/creusot), official
project description. The inspected route uses **Coma** and **Why3**. Claims about
supported code must refer to the actual version and verification conditions.

## S23

Galois and SAW contributors. [Software Analysis Workbench](https://github.com/GaloisInc/saw-script),
including “Notes on Rust.” LLVM and MIR analysis are relevant alternatives;
the Rust route requires matching `mir-json`/rustc/schema versions. Overrides,
encodings and solver trust remain part of each proof claim.

## S24

Nuno P. Lopes, Juneyoung Lee, Chung-Kil Hur, Zhengyang Liu and John Regehr.
[Alive2: Bounded Translation Validation for LLVM](https://web.ist.utl.pt/nuno.lopes/pubs/alive2-pldi21.pdf).
*PLDI*, 2021, 15 pages, DOI: 10.1145/3453483.3454030. Also the
[official repository](https://github.com/AliveToolkit/alive2).
The paper explicitly discusses missed bugs under bounded loop unrolling;
the repository documents further support limitations. No all-loop or PIR
correctness result follows from a bounded LLVM check.

## S25

Fiat-Crypto contributors. [Fiat-Crypto](https://github.com/mit-plv/fiat-crypto),
official repository and architecture description. Verified arithmetic generation
and output-language infrastructure, including C/Rust. Evaluate the actual
generation pipeline and its remaining compilation boundaries for any reuse.

## S26

HACL* contributors. [HACL*](https://github.com/hacl-star/hacl-star), official
project description. Verified cryptographic implementations in the F* ecosystem;
an exact primitive's assurance is distinct from an idealized protocol assumption.

## S27

Jasmin contributors. [Jasmin](https://github.com/jasmin-lang/jasmin), official
project description. A high-assurance cryptographic language/compiler candidate
for selected native kernels. No zkc integration or performance result is claimed.

## S28

Ralf Jung, Jacques-Henri Jourdan, Robbert Krebbers and Derek Dreyer.
[RustBelt: Securing the Foundations of the Rust Programming Language](https://plv.mpi-sws.org/rustbelt/popl18/paper.pdf).
*POPL*, 2018; linked paper, 34 pages. Semantic justification of Rust abstractions
and unsafe implementations; theoretical input for an ownership boundary, not a
proof of arbitrary compiled Rust.

## S29

Lennard Gäher, Michael Sammler, Ralf Jung, Robbert Krebbers and Derek Dreyer.
[RefinedRust: A Type System for High-Assurance Verification of Rust Programs](https://plv.mpi-sws.org/refinedrust/paper-refinedrust.pdf).
*Proceedings of the ACM on Programming Languages* 8, PLDI, Article 192,
June 2024, 25 pages. Refinement typing and separation-logic automation
for foundational proofs of supported safe/unsafe Rust. A heavier candidate when
such ownership reasoning becomes essential.

## S30

Gilles Barthe, Benjamin Grégoire, Justin Hsu and Pierre-Yves Strub.
[Coupling Proofs Are Probabilistic Product Programs](https://arxiv.org/abs/1607.03455).
*POPL*, 2017, pp. 161–174. Probabilistic relational reasoning; application to zkc
requires the actual joint initialization and observer relation.

## S31

Gordon D. Plotkin and Matija Pretnar. [Handling Algebraic Effects](https://lmcs.episciences.org/705/pdf).
*Logical Methods in Computer Science* 9(4:23), 2013, pp. 1–36. Operations,
handlers and compositional interpretation; not a generic proof that arbitrary
protocol effects commute.

## S32

Thorsten Altenkirch, Conor McBride and James McKinna.
[Why Dependent Types Matter](https://people.cs.nott.ac.uk/psztxa/publ/ydtm.pdf).
Draft, April 2005, 21 pages. Basis for intrinsically well-formed data and typed
program representations. Semantic admission remains an additional obligation.

## S33

Umut A. Acar, Guy E. Blelloch and Robert Harper.
[Selective Memoization](https://www.cs.cmu.edu/~rwh/papers/memoization/popl.pdf).
*POPL*, 2003, pp. 14–25. Dependency-sensitive reuse is the relevant theory;
zkc's actual capture, stage and failed-state laws still need their own proofs.

## S34

Elaine Li, Felix Stutz, Thomas Wies and Damien Zufferey.
[Complete Multiparty Session Type Projection with Automata](https://cs.nyu.edu/wies/publ/cav23_mst.pdf).
*CAV*, 2023, LNCS 13966, pp. 350–373; linked author manuscript includes a
corrected complexity discussion. Input for the boundary between supplied finite
endpoints and a stronger asynchronous projection/progress promise.

## S35

Li-yao Xia, Yannick Zakowski, Paul He, Chung-Kil Hur, Gregory Malecha,
Benjamin C. Pierce and Steve Zdancewic. [Interaction Trees: Representing
Recursive and Impure Programs in Coq](https://arxiv.org/abs/1906.00046).
*POPL*, 2020. Coinductive effectful semantics, interpreter composition and
termination-sensitive equivalence. An extension candidate, not a reason to
replace the selected finite `Proc` semantics immediately.

## S36

Lean project. [Lake](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/).
Mathlib community. [Library Style Guidelines](https://leanprover-community.github.io/contribute/style.html).
Package/module distinction, controlled dependencies and proof-library engineering.
Exact build syntax and dependency compatibility must match selected toolchains.

## S37

Verified zkEVM contributors. [ArkLib](https://github.com/Verified-zkEVM/ArkLib)
and [CompPoly](https://github.com/Verified-zkEVM/CompPoly), official repositories.
Mathematical protocol/polynomial reuse candidates. zkc's currently declared
ArkLib pin is in the [optional package](../integrations/arklib/lakefile.toml);
its shared dependency pins and owned proof cones are checked separately.
