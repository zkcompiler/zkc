# Trusted common input bindings

This is an explicit Host admission context for independently executing roles.
It supplies no signature, agreement theorem or source certificate. Every process
must obtain the same SHA-256 pin from an externally trusted application context.
Computing a pin from incoming context bytes establishes no such trust.
Generic Program admission and independent execution do not implicitly use it.

The consumer first authenticates the Program and its actual source/interface
association, obtains the complete common-input requirements through independent
derivation or an authenticated owner association, and maps each requirement to
exact flat participant inputs. Availability, public markings,
types and names cannot derive requirements or discharge agreement. Logical child
mapping remains the source/interface owner's responsibility.

The context uses the bounded canonical [logical encoding](../ir/construction.md#native-occurrence-encoding)
of arrays and strings, at most 4 MiB, with this exact shape:

```text
["zkc.input-bindings/0", program_sha256, entry, list(Binding)]
Binding = [list(Component), physical_type, facet, Expected]
Component = [role, native_input, list(path_index)]
facet = "value" | "tag" | ["extent", axis]
Expected = ["active", canonical_hex] | ["inactive"]
```

The Program digest names exact admitted bytes. All digests and byte strings use
lowercase hex. Native input and path indices are canonical unsigned decimal
strings. Requirement/component order and complete physical types must exactly
match that complete trusted inventory; extra, omitted or changed groups
refuse. There are at most 1,024 groups and 32,768 total components. A component's
path has at most eight pairs `(variant alternative, payload ordinal)`, checked
against the declared alternatives and complete physical payload types.
Components in a group include at least two different participant roles.

`value` binds the selected component's existing canonical wire bytes, using the
same installed codec as public proof input binding. It requires a complete
Copy data type with an admitted native wire profile. `tag` binds only a
variant's canonical decimal declaration ordinal, encoded as ASCII then hex;
it establishes no payload equality. An inactive path uses the exact inactive
marker. It neither unpacks nor serializes dormant payloads. Distinct active and
inactive expectations cannot be identified by empty bytes.

The typed runtime observation is `Observation::Value`, `Observation::Tag` or
`Observation::Extent { axis }`; these alternatives cannot be combined. An extent
axis is a canonical unsigned decimal string. Bytes, sequences, field vectors,
group vectors, indices, fixed arrays and fixed vectors have axis 0; matrices
have axes 0 (rows) and 1 (columns). Other types and axes refuse. The complete
physical type in the binding remains the selected collection type. Extent
expectations contain canonical ASCII unsigned decimal, encoded as lowercase
hex, just like tag ordinals. Leading zeroes, signs and overflow refuse.

Extent observations require Copy data, but do not require a wire codec and do
not encode or compare contents. A trusted value adapter exposes pure stable
metadata inspection without executing a length operation. Unsupported adapters
refuse. Context and actual extents are capped at 67,108,864; backend collection
and retained-value limits independently narrow this conservative inspection
ceiling. Zero is an active extent. An inactive expectation requires a conditional
variant path on every component, never an unconditional root.

Before constructing a participant runner, `InputBindings::check_role` checks all
that role's required components against the pinned expectations. It bounds each
value, descriptor path and canonical encoding, and charges inspection and
encoding to the caller's [invocation ledger](../runtime/capacity.md#invocation-ledgers):
each inspected value's retained bytes as logical work, and each canonical
encoding bound as fresh allocation held live until its comparison ends. All
roles of one invocation share that ledger. Failure creates no runtime frame or
semantic action. Ordinary runner loading still independently admits complete inputs,
backend authority, services, custody and budgets.

## Production

`InputBindings::producer(program, entry, inventory)` starts the producer that
sits beside this reader. It checks the inventory exactly as `admit_pinned`
does. `ContextProducer::observe_role(role, backend, inputs, ledger)` observes
one role's actual inputs in the entry's port order, with holes allowed only
outside required components, and computes each of its components' observation
exactly as the reader does, charging inspection and encoding to the caller's
ledger in the same way. Every observed component of one group must agree: equal
canonical bytes, or the inactive marker on every one, or the producer refuses
with `input-binding-Value`. `ContextProducer::encode(ledger)` requires an
observed component for every group (`input-binding-Input` otherwise), emits the
canonical bytes `admit_pinned` accepts, and charges them as fresh allocation.
A producer may observe one role or all of them; observing all of them also
checks the participants' agreement before distribution.

Producing a context confers no trust. Hashing the produced bytes yields the pin
that the application distributes through its externally trusted context; a
process that hashes bytes it receives still establishes nothing. The SDK exposes
the producer as `RunEntry::common_input_context(request)`, which prepares the
named request without issuing resources and charges its invocation ledger, and as
`BackendRun::common_input_context(inputs, value_budget, work_budget)` for
caller-owned backend values. The CLI command `zkc common-inputs` writes the
context of one Run deployment of a Function package and reports its SHA-256.

## Consumers and trust boundary

The Runtime utility checks pins, exact inventories and actual values. It cannot
establish that other processes used the same externally supplied pin. Current
joint execution establishes scoped selector/count agreement at actual reached
headers without requiring this independent-execution context. The native
LanguageInterface exports complete source-associated requirements for each
concrete Protocol. Its independent reader compares the actual original through
the existing schema/component map; source comparison separately derives every
closed helper inventory. This context does not replace the existing canonical
public proof invocation root.

The SDK's `BackendRun::bind_common_inputs(context, externally_trusted_pin)`
consumes a Run and derives its complete inventory from the authenticated selected
original's required [Protocol member](entry.md#retained-interface). It returns
`InputBoundBackendRun`, whose `start_role` checks actual role inputs before
constructing a Runner with that Run's exact Program and entry. Refusal preserves
backend custody and zero execution usage. The former caller-inventory method is
replaced; the generic Runtime utility retains its explicit application trust seam.
Context class and component order follows the canonical source inventory after
mapping, including when participant positions differ across roles.

`RunEntry::bind_common_inputs` uses the same inventory adapter and returns
`InputBoundRunEntry`. Its named `prepare` resolves source supply, setup and service
allowances through existing Host preparation, then checks every supplied joint
role's ordinary data before any capability/service issuance, frame or execution.
Prepared capability holes are allowed only outside required components; they
confer no custody and do not bypass ordinary Runner admission. The returned plan
uses existing joint execution. There is no new independent-role named transport.
Generic unbound Run execution and reached-header joint agreement remain distinct.

The authenticated compiler owns the actual source/native association and complete
inventory. The SDK authenticates that owner-associated inventory and checks its
local schema, roles, conditional paths, participant positions and complete Program
types. It cannot independently certify source coverage from package hashes.
Fresh compiled source-to-Entry pairing checks the producer/consumer association;
hand-authored SDK fixtures alone do not establish it. An external context pin is still required in each process, and
no pin proves that peers selected it. Common-input admission replaces neither a
public proof root nor a formal correspondence argument.
