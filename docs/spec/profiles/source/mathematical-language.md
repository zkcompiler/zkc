# Mathematical source language

This profile defines the initial `.zkc` source fragment that emits
[mathematical protocol MLIR](../compiler/mathematical-protocols.md).
It uses concrete installed fields, Boolean values, total mathematical helpers,
explicit participants, messages and selected Entries. The `.pir` source profile
has a separate parser and checking path; format selection is explicit.

## Capture and names

A capture is a nonempty map from logical module paths to exact UTF-8 bytes.
Each file starts with `module path;` matching its captured name. Module paths
use `::`; identifiers match `[A-Za-z_][A-Za-z0-9_]*`. Language keywords are
reserved. Comments start with `//`. Tokens retain trivia and byte spans.

Declarations are private unless prefixed with `pub`. A declaration can be named
through `use module::{Name, Other};` or by its qualified path when its module
is explicitly captured. Imports do not discover files. Imported names cannot
conflict with declarations or other imports. Local bindings cannot shadow visible
bindings or declarations. Import cycles, recursive helpers and duplicate names
refuse. Every declaration is checked, including unused bodies.

Capture identity is SHA-256 over a version marker, explicit format, and modules
sorted by logical path. Every name and byte string is prefixed by its unsigned
64-bit little-endian byte length. Diagnostic file paths do not enter identity.

## Declarations and expressions

```text
module example;
domain Fr = field("bls12-381.fr");
math fn double(x: Fr) -> Fr { return x + x; }
protocol Transfer roles(P, V)(x: Fr @P) -> (result: Fr @V) {
  let payload = double(x);
  let received = send P -> V(payload);
  return (result = received);
}
entry Demo = Transfer;
```

Types are `bool` or concrete domain aliases. A domain declaration names an
installed `Field`; string literals contain unescaped printable ASCII.
A helper has typed parameters and one typed result. A protocol has an ordered,
nonempty role roster and named, typed input/output ports with nonempty role sets.
`@P` and `@(P, V)` name components. Entries select a protocol declaration;
selection uses an exact qualified Entry name. Multiple Entries may select one
protocol. A cross-module reference requires a public target.

Bodies contain `let name [: type] [@roles] = expression;` and one final return.
Role annotations and `send Sender -> Receiver(expression)` are available only
in protocol bindings. Send must occupy the whole binding RHS. Protocol returns
use `(port = expression, ...)`; evaluate expressions in written order, then put
operands in declared port order. Missing, repeated and unknown results refuse.
Helpers return one expression. Lists accept trailing commas.

Expressions include bindings, helper calls, decimal field literals, Boolean
literals, parentheses, `*`, `+`, `-` and `==`. Multiplication binds most tightly,
then addition/subtraction, then equality. Arithmetic associates left; chained
equality requires parentheses. Arithmetic requires equal field types. Equality
requires equal field types or two Booleans. No implicit field conversion occurs.

A field literal needs a unique context from an annotation, another operand, a
call parameter or a return type. `let x = 1;` is ambiguous. The installed
`field.constant` contract checks canonical spelling and the characteristic bound;
there is no modular reduction or default field. Boolean literals need no domain.

## Participant meaning

A protocol value denotes one component per available role. Components of a
shared input need not be equal. Literal values are available at all roles;
arithmetic intersects operand availability. A strict subset annotation emits
`protocol.restrict_roles`; an equal annotation emits no operation. Result port
roles may narrow the operand's availability directly through `protocol.return`.

A helper result follows its body's actual input dependencies. Formation checks
also retain dependencies of every intermediate computation, including unused
ones. Thus `first(a,b) { return a; }` can accept `a @P` and `b @V`, but adding an
unused `a+b` inside the helper makes that call invalid.

Send requires distinct declared roles and a payload available at the sender.
Its result is available only at the receiver and denotes the actual received
value. The original payload keeps its existing roles. The lowering emits
`protocol.exchange` followed immediately by a receiver-only
`protocol.restrict_roles`, because the IR exchange itself has both sender and
receiver components. These operations imply no honest-delivery premise.

## Translation and retention

Modules are emitted in logical-path order; definitions retain declaration order.
Math helpers become private `func.func` definitions and `func.call` uses.
Protocols become `protocol.func`; field operations use `algebra`, and Boolean
constants/equality use admitted `arith` operations. Domain aliases are resolved;
Entry selection is retained in an interface rather than an executable operation.

Qualified components are encoded as `s` followed by each component's decimal byte
length, `_`, and spelling. `example::Transfer` becomes `s7_example8_Transfer`.
This encoding is injective and never truncated. Message sites are `s` followed by
the zero-based source statement index. Whitespace and comments do not alter sites.

Before any simplification, the compiler reparses the exact emitted bytes, verifies
the complete module, and independently compares its actual SSA against checked
source. The comparison consumes every definition and operation, including unused
work. It checks types, ordered operands, mathematical identities, helper targets,
role availability, message sites, receive restrictions and returns. An equivalent
but differently structured rewrite can refuse. The comparison never calls emission.

`CheckedOriginal` owns immutable source, original bytes, comparison counts,
interface, toolchain identity and a bound diagnostic location map. Its API does
not expose mutable original IR. Callers may parse separate copies. The existing
compiler receives those exact original bytes and the selected Entry's encoded
protocol symbol, then emits ordinary `zkc.run/1` and `zkc.program/1` artifacts.
All emitted protocols pass preparation and lowering, even if not selected.

`zkc.language-interface/1` is a JSON object with exactly these members:
`format`, `capture`, `original`, `toolchain`, `entry`, `protocol`, `roles`,
`inputs`, and `outputs`. Port rows contain exactly `name`, `type`, `roles`, and
`index`; indices refer to original input/output positions. Types are `bool` or
`field<installed.identity>`. Checking rejects duplicate/unknown keys, versions,
altered identities, selections and layouts. Object member order is immaterial; JSON escapes and numeric spellings compare
by their decoded values.
Version 1 has no relation or clause member.

The original identity hashes exact MLIR bytes without debug locations, using a
fixed printing policy independent of host command-line printer options. The
compiler toolchain identity binds the installed catalog fingerprint, compiler
source build identity and actual LLVM/MLIR release. It identifies the checked
environment; it is neither a cryptographic security claim nor an authenticity
signature. The location map is built from reparsed operations matched by the independent
comparison and binds capture and original identities separately;
paths remain diagnostic context.

## Bounds and scope

Requests can lower these ceilings, never raise them. Counters are shared across
captured modules. Checks refuse before recursive depth or charged-work bounds
are exceeded; no truncated result is returned.

| Quantity | Ceiling |
|---|---:|
| Files; bytes per file; total captured bytes | 256; 1 MiB; 8 MiB |
| Tokens, including trivia and file-end tokens | 1,000,000 |
| Nontrivia token; identifier; module path bytes | 4096; 128; 2048 |
| Parse, expression, import and call depth | 64 each |
| Declarations; source or emitted operations | 10,000; 100,000 |
| Charged checking work | 1,000,000 |
| Emitted MLIR; interface JSON | 16 MiB; 4 MiB |
| Encoded symbol; diagnostic path bytes | 4096 each |
| Location records, five 64-bit coordinates each | 16 MiB |

The comparator performs whole-module target admission once before comparing SSA.
Target admission, expansion and execution retain their own limits. A well-typed
source may fail target preparation or realization; this is a target compilation failure, with its phase identified.
Generics, local algorithms/control, resource and service operations, relation
predicates/attachments, proof construction and source-facing Host inputs are
outside this source fragment. Existing IR support for them remains independent.
The structural source check and runtime controls do not establish native Lean
correspondence or protocol security.

Reserved future syntax reports `source.unsupported`: `local`, `service`,
`predicate`, `relation`, `requires`, `construct`, `construction`, `where`,
`struct`, `enum`, `type`, `nat`, `if`, `else`, `for`, `while`, `opaque`, `stop`,
and generic/aggregate/effect punctuation (`<`, `>`, `[`, `]`, `!`). These words
cannot be declared as ordinary identifiers in this fragment.
