# Native numerical calls

This contract connects checked Kernel realization and physical bindings to
synchronous native numerical handlers. It uses the existing `plan.apply` and
`zkc.program/0` operation path; there is no separate numerical executable format.

## Types and storage

The compiler owns exact nominal and structural port types, representation
selection and explicit conversions. Physical validation checks the actual ports
and retained Kernel/Local correspondence. The VM independently admits the
physical program and links independently advertised backend signatures.

A representation identity does not specify a foreign memory ABI. A numerical
adapter must interpret the exact selected representation and actual operands.
Typed field elements preserve their nominal field, including extension and
binary-field arithmetic. Equal size does not permit reinterpretation between
fields, or between a field element and its encoded coordinates.

Native dense inputs are borrowed immutable slices. A row-major view admits
`rows * columns == elements.len()` with checked arithmetic; zero dimensions
remain distinct from unknown dimensions. Transposition changes indexing without
copying storage. Multilinear tables retain their owning library's storage order:
first-coordinate folding pairs adjacent LSB elements and corresponding MSB
half-table elements. Storage constructors preserve that order.

Repeated aliases are allowed. Input borrows end when the synchronous call
returns; published results own their backing references. A physical release,
last use or reference count grants no permission to overwrite published inputs.
Sparse matrices, diagonal views, keys and capabilities do not acquire dense
access through this contract. Their existing adapters and explicit conversions
retain their own obligations.

## Invocation and completion

Installation resolves immutable bindings and signatures. Operand shapes,
attributes and capacity are checked at the reached call, after the existing VM
and native admission. Numerical construction receives policy and the fresh-result
allowance, without resource stores, randomness, transcript state or interpreter
environments. It does not create an additional frame or instruction charge.

Results are built in initialized private destinations. The adapter fixes their
lengths before allocation and exposes only mutable slices. Freezing consumes
the destination through its owning representation constructor. Native output
validation and the VM still check the complete returned tuple and its retention.
Results become observable only after successful completion; a failed operation
returns no partial result tuple. Failure does not roll back prior effects or
refund spent work. All internal work must finish before returning.

## Managed construction

`zkc-backends`' internal numerical scope reserves:

- The aggregate conservative charge of fresh results against the invocation's
  output allowance, in addition to each result's existing policy ceiling.
- Simultaneously live scratch and destination staging storage, plus reserved
  final representation storage, against `Policy::max_numerical_bytes`.
- A conservative operation/loop bound against `Policy::max_numerical_work`.

Reservations precede allocation and use checked arithmetic. Staging and final
storage are both counted while freezing can overlap them. Finished results
remain charged until the scope ends. Scratch and abandoned destinations release
their reservations when dropped. Scratch exposes only borrowed slices and cannot
be frozen through the result API. Accepted work charges are not refunded.

The defaults are 256 MiB of managed memory and 2^26 numerical work units per
call. These native policy fields are included in preparation compatibility;
reusing a cached computation cannot bypass a changed policy. They are distinct
from the CLI capacity record and existing VM instruction, iteration, logical-byte
and retained-value ledgers. Existing shape and output refusal precedence is
preserved before the new numerical exhaustion checks.

Managed memory bounds requested typed payload storage and conservative final
representation storage. They do not bound allocator overhead, total process
memory or allocations hidden inside provider libraries. Freezing and native
arithmetic remain trusted adapter code; an infallible provider allocation can
still encounter process allocation failure. Work units are not elapsed time,
bit-operation complexity or a constant-time guarantee.

## Implemented consumers

The scoped path currently covers dense `vector.matvec` and `vector.split` over
all eight installed field families, `poly.fold` for BLS LSB/MSB tables, and
`poly.opening_quotient` for KoalaBear and its degree-four/eight extensions.
The quotient uses scoped denominator scratch and its unpublished output for
batch-inversion prefixes. Other operations keep their existing provider checks;
DFT preparation and hidden provider scratch are not certified by this scope.

Kernel schedules still lower to Local control and installed operations. This
contract does not establish a native implementation of arbitrary scheduled
functions or native/source mathematical correspondence. Future native lowering
must connect the actual schedule, representation access, work bounds and
completion behavior. MLIR memory and bufferization interfaces apply when that
lowering provides concrete storage and alias semantics.
