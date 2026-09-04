# Natural Modular Arithmetic Semantic Module

> **Document kind:** Target semantic specification
> **Document state:** Active non-normative target
> **Provisional owner:** `foundation`
> **Authority:** None during transition. Current normative rules remain under
> [`docs/`](../../docs/README.md).

## 1. Scope

This page defines one ordinary, content-addressed semantic module for natural
modular arithmetic. It is an extension module under the executable Foundation
mechanism, not a declaration in the Foundation root profile and not an
expansion of `FoundationMetaProfileV0`.

The module's selected symbol is:

```text
zkc.foundation.natural-modular-arithmetic
```

Its current admitted consumer is the checked finite-cover Analysis lane. The
arithmetic meanings are independent of Schnorr, Analysis, PIR, Relations, or
any cryptographic family. Consumer-specific algorithms and propositions remain
with those consumers and enter neither this module's declaration bodies nor
its identity.

## 2. Declaration catalog

The module contains the following exact primitive declarations:

| Primitive | Inputs | Success result | Completed failures |
|---|---|---|---|
| `natural.equal` | two bounded naturals | exact Boolean equality | none |
| `natural.less-than` | two bounded naturals | exact strict natural order | none |
| `natural.modulo-positive` | natural, exact literal modulus | Euclidean remainder | `zero-modulus` |
| `natural.subtract-modulo-positive` | two naturals, exact literal modulus | Euclidean difference modulo the modulus | `zero-modulus` |
| `natural.multiply-modulo-positive` | two naturals, exact literal modulus | product modulo the modulus | `zero-modulus` |
| `natural.power-modulo-positive` | base, exponent, exact literal modulus | modular natural power | `zero-modulus` |
| `natural.inverse-modulo-coprime` | natural, exact literal modulus | unique multiplicative inverse | `zero-modulus`, `non-invertible` |
| `natural.widen-u64` | natural statically bounded by `2^64-1` | the same mathematical natural in `Nat64` | none |

The modulus is part of each algorithm term as an exact positive literal. A
provider cannot select a modulus out of band. Output natural bounds are derived
from that literal. Inversion succeeds exactly when the residue and modulus are
coprime; it is not a field-only operation and does not assert primality.

`zero-modulus`, `non-invertible`, and `stream-index-out-of-range` are distinct
typed semantic failures. The last is declared in the same module for portable
finite streams that index an authenticated literal sequence. It does not turn
partial host indexing into an unchecked exception.

## 3. Identity and execution

The module ID authenticates the module symbol, declaration order, type-rule
bytes, operation-law bytes, and completed-failure references. A primitive
reference authenticates the module ID and local declaration ordinal. A
portable algorithm that uses one of these primitives includes that reference
in its own preimage and therefore depends on the exact module preimage.

Execution requires all of the following:

1. authenticate the portable algorithm identity and term structure;
2. derive its exact direct module closure;
3. authenticate this module preimage and every declaration reference;
4. resolve an exact provider interpretation for each declaration and ABI;
5. admit every input under its declared value type; and
6. enforce deterministic step, primitive-work, and result-size limits.

A provider implementation is operational support, not semantic authority. A
matching module ID without its preimage is `MissingDependency`; another ABI or
term is `Unsupported` or `KindMismatch`; malformed values remain `Malformed`;
typed arithmetic failures remain semantic domain failures; provider/type
disagreement is `CheckerFailure`; and exhausted deterministic controls remain
`DeterministicLimitExceeded`.

## 4. Current use and nonclaims

The finite-cover Analysis instrument uses this module to express pair
normalization, representative embedding, response-difference extraction, and
an authenticated finite representative stream. That use demonstrates an
ordinary extension-module path and exact provider binding. It does not promote
the module into the root profile, prove a generic algebra library, establish
constant-time behavior, or supply a production cryptographic implementation.

Future consumers may import the module only by its exact content identity and
must state their own algorithm ABIs, resource policies, and semantic
obligations. A second use does not retroactively broaden the conclusion of the
finite Analysis judgment.
