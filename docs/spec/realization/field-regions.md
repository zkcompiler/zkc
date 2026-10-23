# Structured field implementation regions

A field implementation region uses upstream Func, Tensor and Linalg containers
with zkc's nominal `!algebra.field` scalar operations. It represents pure
pointwise arithmetic beneath the [Kernel realization](../ir/kernel.md)
boundary. It does not change the source language or the executable program
carrier.

## Admitted profile

The private builtin module contains one `func.func @compute`. Its first
argument is an abstract `index` extent. Each remaining argument is a tensor of
one nominal field: rank zero for a scalar broadcast, or rank one with a dynamic
extent for a column. There is one rank-one result of that same field. Tensor
encodings, argument/result annotations and external callees are absent.

The function contains `tensor.empty` with the extent argument, one
`linalg.generic`, and `func.return` of its result. The generic operation has one
parallel iterator. Column and destination indexing maps are `(i) -> (i)`;
scalar indexing maps are `(i) -> ()`. Its destination block argument is unused:
no value is read from uninitialized storage. Every scalar-body operation is an
admitted field constant, addition, subtraction or multiplication. The body has
no outer captures, effects, integer observations or nested control flow.

The extent is a symbolic dimension of the implementation subject. It is not a
machine representation conversion from source `u64` values. Reached native
calls retain their checked lengths and resource admission. The enclosing
realization preserves eager arguments and length guards for every input,
including unused inputs. An empty domain retains the enclosing map or reduction
contract, including its identity and seed rules.

Field types remain nominal through all these steps, including extension and
binary fields. Replacing them with machine integers or HEIR ModArith requires
a separate representation contract; equal storage widths are insufficient.

## Transformation and independent comparison

Source admission inspects the complete scalar computation before constructing
an isolated candidate. Upstream common-subexpression elimination operates on
that candidate's pure SSA. The retained candidate is not permission to accept
its output: an independent reader checks its actual function signature,
operands, indexing maps, iterator, destination use, scalar operations and
returned value. It also checks unused literals and preserves the complete input
inventory.

The reader derives a bounded Ring expression from candidate SSA. Structural
correspondence compares the source and candidate expressions without requiring
identical node numbering or sharing. It preserves field labels, literals,
ordered operands and input slots. It does not use cancellation, probabilistic
sampling, or an assumption that a backend schedule is correct.

Both native pointwise expression emission and vector recipe emission read the
checked candidate. The final
source/native correspondence check remains required after emission and physical
selection. A region check alone does not establish native execution or a Lean
theorem. The managed invocation, output-publication and capacity contracts stay
with [numerical execution](../runtime/numerical.md).

The representation is private to implementation selection. It is neither a new
serialized expression format nor an executable target with a separate planner.
Bufferization, Vector/LLVM lowering and generated-code deployment are outside
this profile.
