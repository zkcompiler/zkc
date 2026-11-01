# Structured logical source decoding

This note specifies the independent reader's adaptation to the current
[foundation source schema](../../../docs/spec/formats/foundation-interfaces.md).
The existing structured calculus and its process interpretation are unchanged.
Wire decoding supplies data, not a source connection or security theorem.

`Zkc.Source.LogicalFormat.type` validates a complete logical Type tree, retaining
the exact JSON data. Constructor argument kinds, domain sorts, nominal identity
trees, ordered variant alternatives, duplicate labels and oracle arguments are
checked. Traversal has bounded depth, expanded work and metadata. This data
vocabulary grants no interpreter support. `Structured.Format.type` separately
lowers only the existing Boolean, index, field, vector, group, group-vector,
indices, sequence, single-alternative product, service and logical-oracle types.
Existing semantic admission continues to refuse logical oracle execution and
unsupported aggregate/service profiles. Fixed arrays and multiple alternatives
remain outside the structured interpreter profile.

Product identities first pass structured `atom`/`tuple` validation. The reader
then maps atoms to JSON strings and tuples to ordered JSON arrays and writes
compact JSON with unescaped Unicode and standard JSON string escapes. This
encoding is exact and preserves the existing internal nominal identity and its
512-byte profile bound. It retains phantom actuals and distinguishes an atom
from a singleton tuple. No Unicode normalization is performed. The source text
parser rejects lone surrogate escapes before Lean's JSON parser can replace
them. Retired type arrays, printed types, hex descriptors and identity strings
in wire Type positions are refused.

The Lean inspection and execution tools emit this same logical type vocabulary
through `StructuredSource.wireType`. Product printing inverts the canonical
internal identity encoding and checks that decoding it yields the original
identity. An invalid internal encoding produces a refused type tree, never a
new atom with the malformed text as its name. Value payload encodings remain
separate from the logical types embedded in them.

A binding has seven fields, including kinded static arguments and complete
ordered logical input/output lists. `Binding.schema` retains those decoded
claims; `Binding.arguments` retains the existing interpreter's root projection.
Admission checks their agreement, unselected implementation policy and the
signature independently fixed by the formal primitive interpretation. All
bindings are checked, including unused declarations. `Format.binding` decodes
the row and checks signatures that do not need a nominal association;
`Format.bindingIn` additionally resolves capabilities and associated members
against the caller's catalogue. `Format.snapshot` performs that complete check
for every binding against its retained rows, before ordinary unit admission
checks those rows against the independently selected environment.

The existing internal constructor can omit wire metadata; it still selects the
same fixed formal primitive and derives its ports from that meaning. The wire
reader always requires and retains both signature lists and kinded arguments.
There is no reader for a five-field binding or unkinded static argument.

Primitive invocation parameters use structured `natural` rows for the current
Natural validator, with canonical u64 decimals. They lower exactly to the
existing internal decimal parameters. Actual primitive admission checks the
operation-specific parameter count, including the empty None schema. Other
parameter families remain unsupported by this interpretation. Catalog presence
cannot enroll an operation or supply a meaning. The existing field embedding
uses its existing operation and model APIs; its signature is rederived using
the extension's declared BaseField and existing capability/characteristic
checks. No embedding function is synthesized from catalog membership.

The eleven-slot source envelope, exact digest, source declarations, typed
origins, role scopes, operands, results, regions and sites keep their existing
association. Checked arithmetic still refuses overflow, underflow, zero
divisors and out-of-range ingress when reached, including discarded results;
optional inputs retain their incomplete-stop behavior.
