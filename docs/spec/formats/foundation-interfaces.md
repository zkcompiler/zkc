# Foundation interface cutover

This page defines the shared interface changes for the
[native MLIR foundation](../ir/native-foundation.md). These are specified target
contracts, not a claim that current tools emit or admit them. The
[contract register](../contracts.md) and [status](../../status.md) distinguish
the current producer profile from the cutover. The foundation lands one native
route; old readers and compatibility wrappers do not remain in that route.

## Versions and retained meanings

| Contract | Foundation form | Consumer-visible change |
|---|---|---|
| Structured original | `zkc.structured-source/1` | Structured logical types, typed binding arguments/signatures and invocation parameters |
| Constructed participant | `zkc.constructed-participant/1` | Structured types and attributes replace printed MLIR types and the generic text escape |
| Constructed pair | `zkc.constructed-pair/1` | Both children use the new participant form |
| Oracle realization | `zkc.oracle-realization/1` | Interned types become structured data; source-relative roots and actual-body checking remain |
| Application correspondence | `zkc.application-map/1` | New explicit auxiliary association, bound to the actual original and candidate |
| Shared declarations | `zkc.contract-declarations/1` | Complete structured declaration data and parameter schemas; no retired interpreter-profile bit |
| Logical type vocabulary | `zkc.logical-types/1` | Shared typed trees, including complete nominal identities and ordered alternatives |
| Executable bytes | `zkc.program/0` | Unchanged grammar, layout, canonical spellings and execution meaning |

Source AST, checked-source associations, native-origin framing, message codecs,
proof framing and transcript hash constructions keep their owning contracts.
An internal spelling change can change the original MLIR bytes and their exact
hash; it does not change the hash algorithm or authorize reusing an old subject.
Regenerate affected subjects from actual artifacts. No version bump implies a
formal reader or theorem for that version is available.

## Structured source

The envelope retains the eleven required slots and their order:

```text
["zkc.structured-source/1", "original", source-sha256, entry-name,
 domains, relations, bindings, definitions, contracts, catalogue,
 source-declarations]
```

The [structured-source contract](structured-source.md) continues to define
definitions, regions, operands, roles, contracts, sites, declaration ordering,
refusal limits and the exact original-byte hash. The changes are:

1. Every logical type position contains a complete `Type` from
   [logical type data](logical-types.md), rather than the former type-specific
   arrays or a product identity encoded as JSON text. There is no additional
   type table in this envelope. A general type vocabulary does not enlarge the
   exporter's admitted operation or aggregate profile.
2. A binding row is
   `["binding", name, contract, arguments, implementation, inputs, outputs]`.
   Arguments use the catalog's kinded static-value encoding; inputs and outputs
   are ordered logical `Type` arrays. These are the declaration's logical
   ports, excluding execution scope/outcome. Readers rederive the signature
   from the catalog and actual arguments. A printed or producer-supplied
   signature is not authority. The admitted source profile continues to refuse
   selected implementations where it requires an unselected logical binding.
3. A primitive descriptor is still
   `["exec", "exec.apply", binding-name, parameters]`; `parameters` now uses
   the catalog's structured parameter encoding. Scope/outcome extraction still
   requires admission of the actual CFG. It cannot use the declaration alone.
4. Source declarations retain their frontend-owned structured meaning. Their
   internal MLIR carrier is structured inherent data, not a string containing a
   serialized declaration document. Diagnostic locations remain separate.

The retired assertion that bindings are non-callable metadata is replaced by
the typed callable declaration contract. Callable here describes the installed
invocation ABI; it adds no source body and no inlining permission.

## Constructed participants

The participant envelope retains its ten slots, hashes, policy and service-port
rules. Its tag becomes `zkc.constructed-participant/1`. The pair is exactly
`["zkc.constructed-pair/1", producer-record, validator-record]`, with matching
source, candidate and policy. The [construction contract](constructed-participant.md)
continues to require checking the supplied actual candidate first.

Input, output, instruction-result and region-argument type positions contain
complete logical `Type` trees. A binding is `[]` when absent, otherwise
`[contract, arguments, implementation, inputs, outputs]` as above. The instruction
row and the service-query origin/coordinate field retain their existing arities.
Attributes remain sorted `[name, value]` pairs with these exact value cases:

```text
Value = ["string", text] | ["symbol", [symbol-component...]]
      | ["bool", boolean] | ["integer", signedness, width, decimal]
      | ["type", Type] | ["array", [Value...]]
      | ["dictionary", [[name, Value]...]]
      | ["parameter", Parameter]
```

Symbol components are nonempty and resolve under MLIR's actual symbol scope.
Signedness is `signless`, `signed` or `unsigned`; width is a positive canonical
decimal string at most 4,096. Signed values use their signed decimal value;
signless and unsigned values use the nonnegative bit-pattern value. Values must
fit that width and interpretation. Decimal spelling has no leading plus or
zeroes, and zero is `0`, never `-0`. This serialization convention grants no
signedness to a signless arithmetic operation.
Dictionary keys are unique and sorted; attribute positions admit only the
cases their operation owns. The `text` fallback is removed. An unrepresented
semantic attribute refuses export; an exporter must not omit it. Parameter
objects use the [catalog schema](contract-declarations.md#invocation-parameters).

## Realization and application records

`zkc.oracle-realization/1` keeps exactly `{format, selection, types, entries,
declarations}`. Its `types` entries are complete logical `Type` trees in
first-use order. Existing unsigned JSON type references remain unsigned JSON
references here; they do not change to printed MLIR spellings or decimal
strings. All occurrence paths, policy normalization, queries, signatures,
ordering checks, bounds and actual-body comparisons retain their
[realization meaning](oracle-realization.md). Logical handles do not become
ordinary data types by entering this table.

The [application map](application-map.md) is a separate auxiliary artifact.
It has no transcript authority, installs no operation and cannot replace the
realization record's complete original/candidate comparison. Candidate-specific
maps must be regenerated after transformations that change their subject.

## Executable byte language

The [program-byte grammar](program-bytes.md) remains `zkc.program/0`. Compiler
and Rust readers retain independent structural admission. MLIR Type/Attribute
objects are encoded to the existing neutral physical spelling only at this
boundary; the native VM neither links MLIR nor reads MLIR bytecode.

Preserve complete nominal domains, representations, ordered children, variant
alternatives and extension bases. Setup authority, resource successors,
reached refusal precedence and metering remain defined by the existing native
execution contracts. The foundation is not permission to change byte meaning
while retaining its version. Any such change must first revise this decision
and its consumers explicitly.
