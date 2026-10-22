# External quotient arithmetic profile

The optional [HEIR arithmetic package](../../../compiler/external/heir/README.md)
defines a compiler-internal comparison for arithmetic over
`R(q,n) = (Z/qZ)[X]/(X^n+1)`. It does not replace the
[checked coefficient operations](../domains/quotient-rings.md). The profile is
conditional on canonical input coefficients; native entry validation and
execution admission remain separate obligations.

## Subject and coordinates

An admitted module contains exactly one defined, single-block `func.func`, with
fixed, one-dimensional `tensor<nxi32>` arguments and results. The common degree
is a power of two between 2 and 65536. The coefficient modulus is an odd prime
less than `2^31`, and `2n` divides `q-1`. Integer storage carries values in `[0,q)`.
No tensor encoding, function argument/result attributes, control flow, external
callee or unknown operation attribute is admitted. Function identity, visibility,
signature, operand positions and result order belong to the compared subject.

The admitted operations are `mod_arith.encapsulate`, standard `mod_arith.lift`,
`polynomial.from_tensor`, `polynomial.to_tensor`, `polynomial.add`,
`polynomial.sub`, `polynomial.mul`, `polynomial.ntt`, `polynomial.intt` and
`func.return`. Tensor inputs enter through encapsulation; ring values are formed
with the exact `X^n+1` quotient. All arithmetic uses one ring per function.
Outputs observe standard lifts of coefficient tensors. Constants, RNS values,
centered lifts, norm observations and arbitrary upstream operations require
additional reader coverage before admission.

For a primitive `2n`-th root `r`, evaluation coordinates mean

```text
E[k] = sum_j a[j] * r^((2k+1)*j) mod q,  0 <= k < n.
```

Coordinates use natural `k` order. Forward transforms carry `r`; inverse
transforms carry `r^-1` and normalize by `n^-1`. The reader validates the root's
coefficient type, canonical value and degree, and checks `r^n = -1 mod q`.
Under the admitted prime and power-of-two conditions, this gives the required
exact order. Evaluation arithmetic requires the same root on both operands.
An inverse transform must match the incoming evaluation basis. A label saying
only `form=eval` does not establish this condition.

`mod_arith.encapsulate` does not validate or normalize an integer buffer in the
selected lowering. Callers must establish canonical input values before entering
this subject. Reading a well-typed arithmetic module does not establish that
precondition for an external buffer.

## Independent comparison and publication

The reader walks actual SSA definitions separately in the source and candidate.
It assigns an indeterminate to each ordered input ring element, normalizes sums,
differences and products as commutative ring expressions modulo `q`, and tracks
coefficient/evaluation forms and roots independently of that normalization.
Equal normalized output expressions with equal interfaces are sufficient for
acceptance under the stated input interpretation. Quotient elements are never
treated as field elements: inversion and cancellation are not used.

The finite reader admits at most 1024 inputs and results, monomials of at most
64 factors, and a budget of one million operation/operand/result and expression
inspection units across a standalone comparison. Compiler callers provide a
shared allowance that decreases across entries and retries. Unsupported expressions and capacity exhaustion
refuse. A refusal does not establish mathematical inequivalence.

`placeTransforms` first admits the source, clones it, runs the selected HEIR
placement, root attachment, canonicalization and common-subexpression passes,
and compares the actual candidate with the retained source. Failure returns no
candidate. Placement minimizes the upstream transform cost subject to its
solver limits; this is not a latency or memory optimum.

The comparison covers the structured arithmetic edge. It does not prove that
Polynomial-to-ModArith lowering, bufferization, LLVM generation, compiled code,
or runtime execution realizes that edge. Qualification tests exercise those
later stages on bounded inputs. The main compiler instead connects the admitted
arithmetic to managed native operations through the separate boundary below.

## Managed quotient calculations

An enabled compiler selects complete normalized Kernel entries containing only
formal quotient projection, coefficient observation, addition, subtraction and
multiplication. Each selected entry has one admitted `q,n`, at most 512 source
operations and at most 128 native coefficient inputs and outputs. At least one
multiplication is required for optional placement. Unsupported entries retain
the coefficient realization; arbitrary-modulus quotient semantics do not depend
on the external transform profile.

The importer uses actual HEIR Polynomial and ModArith SSA. Native projection
first reduces every captured coefficient sequence to the exact canonical
`q,n` representation, establishing the precondition for encapsulation. A reader
independent of the importer interprets the retained source operations and
compares their ordered outputs with the actual HEIR function. Qualified HEIR
placement then retains that module and checks its actual result.

The managed emitter constructs another private candidate using `index.constant`
and native quotient projection, add/subtract, coefficient multiplication,
NTT/INTT and pointwise multiplication. It emits no foreign pointer, uncharged
buffer, machine-code blob or new executable dialect. The existing runtime owns
argument checks, destination admission, charged work and resource failure.

A separate native reader resolves each actual binding and reads constants,
operands, canonical coefficient meanings and evaluation bases. It compares the
actual outputs with the retained source, without calling the importer,
placement pass or emitter. Source and candidate input positions are distinct
indeterminates except where the actual caller supplies the same value to more
than one port. Such aliases use the same mathematical assignment.

Generated occurrence labels locate native values proposed for output positions.
The reader checks every located value's expression and coefficient form; a
label alone gives no equality. One producer can supply several equal outputs,
without a copy introduced solely for matching. The enclosing reader checks
ordered returned values or their actual inlined uses. Global executable
admission additionally checks closed attributes, unique occurrences, binding
signatures and the complete candidate. The standard numerical schedule and
its consumed Local body are both checked under the existing
[candidate discipline](../../compiler/verification.md).

Optional planning has cumulative allowances of 16 solver invocations, one
million interpretation units, 100,000 scratch construction units and 16 MiB
of generated occurrence bytes. Source selection bounds are checked before
planning; a conservative scratch envelope is reserved before cloning and
emission. Optional exhaustion or an unavailable solver result selects the
coefficient fallback. Actual semantic mismatches are terminal, including when
the final successful budget debit leaves zero. Required final checking retains
its own cumulative limits and can refuse when those are exhausted. None of
these compiler allowances replaces runtime resource accounting.

## Relation to other profiles

Falcon and ML-DSA arithmetic fit the full scalar NTT condition at their usual
ring parameters. ML-KEM's `q=3329,n=256` does not; it uses quadratic components
and needs a separately interpreted product representation. Composite moduli
and arbitrary positive degrees remain supported by the coefficient fallback,
not by this transform profile.

RNS basis conversion, centered integer reconstruction, signed decomposition,
encoding and norm checks are separate mathematical observations. They cannot be
admitted by extending this operation list without interpreting their meaning
and capacity conditions. No Lean correspondence or protocol-security claim is
made by this native comparison.

Root selection in checked placement tries at most 256 field elements. For each
candidate `a`, it tests `r=a^((q-1)/(2n))` and `r^n=-1`, charging the shared
inspection allowance before exponentiation. In the admitted prime, power-of-two
profile this condition establishes exact order `2n`; finding a full field
generator or factoring `q-1` is unnecessary. Failure to find or afford a root
makes placement unavailable. The independently checked candidate still carries
its exact forward and inverse roots.

The selected native recipe has its own resource profile. It can allocate more
intermediate coefficient vectors than the coefficient recipe, and does not
promise the same exhaustion point under a fixed execution allowance. Compile-time
optional fallback preserves required compilation capacity; it is not a claim
that runtime capacity is interchangeable between recipes.
