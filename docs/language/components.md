# Checked interfaces and components

A library interface states what a component supplies. Static linking checks the
selected implementation before emitting common PIR. This chapter also covers
local alternatives and traversal within those components. Start with
[projects](projects.md) for library loading and public exports.

## Checked interfaces and static components

The [checked-library profile](../spec/profiles/source/checked-libraries.md)
separates checking a client from choosing its private representation. The runnable
[checked-components example](../../examples/protocols/checked-components.pir)
uses one client with an empty affine state and a stored Boolean state:

```text
interface Cell {
  type State drop;
  local start(ok: bool) -> State effects (local);
  local step(state: State) -> State;
  local finish(state: State, ok: bool) -> bool;
}
fn Client<C: Cell>(ok: bool) -> bool effects (local) {
  let state = C::start(ok);
  let next = C::step(state);
  return C::finish(next, ok);
}
link Empty = Client<EmptyCell>;
link Stored = Client<StoredCell>;
```

An importable root supplies `library(namespace=..., name=..., version=...,
resolution=...);`. An application may use a local anonymous owner. These captured
identities qualify declarations; [source projects](projects.md) explains
multi-file imports, visibility, exact dependencies and source selectors.
`component EmptyCell: Cell { ... }` supplies type representations and local
member bodies. A component can take domain, natural, association and component
parameters; nested selections remain static. `link` names a closed callable for
ordinary participant-local code. It does not introduce runtime dispatch.
Every component template is checked against its declared interface under its
parameter bounds, including templates that are never selected and parameters
that no member body uses. Selection cannot repair an invalid template.

`type State drop` permits disposal but does not promise copying. The client
therefore must thread it through `step`, even if a selected implementation uses
copyable storage. A guard requires the conservative `effects (local)` allowance;
all installed primitive calls in this source profile carry that allowance.
An empty effect set permits pure aggregate manipulation and calls with an empty
effect contract. The finer operation effects and security properties remain
owned by PIR and their property checkers.

Interfaces can expose `nat Width;`, `association Subject;` and sorted domain
members. `Array<C::View, C::Width>` retains its element type and associated
dimension until selection. Ordinary values never become static actuals.
`select Shared = Provider<...>;` gives a pure selection an alias;
`seal Separate = Provider<...>;` gives it a distinct declaration-based identity.
Repeated use of the same seal shares that sealed selection.

Explicit sealing is an advanced, optional feature. Its long-term source syntax
and necessity remain under review against nominal wrappers and explicit identity
parameters. Current behavior remains supported; this is not a deprecation.

An interface can request `facet required "zkc.frontend.library" "resources";`
or `"effects"`. Those facets report the finite body/conformance checks.
Unknown required facets refuse linking; `facet optional "owner" "name";`
retains an unavailable result without inventing evidence. These are not
cryptographic-security claims.

Checked component bodies support typed calls, products, fixed arrays, static
projections, finite nominal variants, exhaustive local matching, isolated Boolean
conditionals, bounded array traversal and terminal stops. Existing concrete local functions also retain their
bounded conditional and numeric-loop constructs. Unsupported control flow refuses;
interface checking does not bypass common PIR admission.
The core API also supports ordinary type parameters with permission bounds and
component-level static requirements; the current authoring syntax exposes
component parameters and member-signature requirements, not those additional
declaration forms.

After linking, typed representation plans produce ordinary closed local
functions. An empty noncopyable state becomes a `resource_unit` logical port
until disposal, although it has no physical payload. Both selected examples then
follow normal PIR admission, projection, physical compilation and execution.
Their implementations are alternatives with a shared interface, not an asserted
proof of behavioral equivalence.

## Local alternatives and finite traversal

The runnable [checked-variants example](../../examples/protocols/checked-variants.pir)
uses both empty and stored private states:

```text
enum Outcome<C: Cell> { Ready(C::State), Invalid(bool) }
fn Use<C: Cell>(ok: bool) -> bool {
  let result: Outcome<C> = Outcome::Ready(C::start(ok));
  match result capture(ok) -> (answer) {
    Ready(state) => {
      let next = C::step(state);
      let accepted = C::finish(next, ok);
      yield (accepted);
    },
    Invalid(error) => { yield (error); }
  }
  return answer;
}
```

A checked client or component can choose an alternative at runtime:

```rust
if ok capture(state, ok) -> (result) {
  let ready: Outcome<C> = Outcome::Ready(state);
  yield (ready);
} else {
  let invalid: Outcome<C> = Outcome::Invalid(ok);
  yield (invalid);
}
```

Each arm has its own scope. Captures cross the conditional once, even for an
affine state; an arm cannot reach uncaptured outer values. Continuing arms agree
on result types. A stopped arm yields nothing, and an all-stopping join must not
declare results in authored source. If a selected component makes an otherwise
continuing join always stop, linking removes the unreachable result and
continuation while preserving the reached calls. This syntax lowers to existing
local PIR control.

`enum` defines an ordinary local value. `Ready` is its constructor, not a
compiler-certified validation claim. Its payload is checked against the declared
alternative. Only the chosen payload exists at runtime; an unused alternative
never fabricates a resource. The variant's copy/drop permissions conservatively
include *all* alternatives. Component, domain, natural and association parameters
are retained in its identity, including parameters absent from the payload.

A match explicitly captures the outer values needed by its arms. Each arm sees
only its payload bindings and those captures. Every alternative must appear once;
continuing arms yield the same output types. The current `yield` form takes names,
so compute a call result in a `let` before yielding it. A local `stop reject;`
(or `abort`, `exhausted`, `incomplete`, `refused`) terminates execution without a
yield. A match whose every arm stops declares `-> ()` and needs no following
return. Such stops cannot be recovered by matching an error value. Local functions
name no participant; the protocol's `local P:` places their execution.

```text
let elements = [C::start(ok), C::start(ok)];
let initial = C::start(ok);
for element in elements carry(state = initial) capture(ok) -> (output) {
  let accepted = C::finish(state, ok);
  let next = C::step(element);
  yield (next);
}
return C::finish(output, ok);
```

Traversal consumes each element once and threads the carried state. Invariant
captures must be copyable. A zero-length array preserves the initial state and
never enters the body; the body is nevertheless checked. Selection expands this
finite traversal within a 4,096-instruction budget. It is not an unrestricted
iterator or dynamic loop. An empty array needs an expected type, for example
`let empty: Array<C::State, 0> = [];`.

Variants can cross local call boundaries. This executable profile excludes them
from protocol inputs/outputs, messages, primitive signatures and family selectors.
Their tag cannot choose another participant's schedule. The
[local-variant profile](../spec/profiles/compiler/local-variants.md) owns the
portable descriptor, resource accounting and realization restrictions.

## Captured relations and checked preparation

An explicitly loaded `relation Circuit = r1cs("circuit.r1cs");` can be passed as
an association actual, such as `ForRelation<Circuit>`. Its normalized descriptor,
including the public/private partition, becomes the captured subject. A frozen
resolved artifact retains that descriptor and does not reopen the source path.
An association alone establishes no validation fact.

The native [`zkc_tools::ingress`](../../crates/zkc-tools/src/ingress/mod.rs) API
checks external material against caller-selected expected configuration. Its
private-constructor results retain actual key, assignment, setup or index data.
Groth16's checked invocation verifies those subjects and required premises before
calling the compiled protocol. The reusable PCS path checks one setup against
multiple independently recomputed relation indices. These are concrete native
adapter APIs; there is no generic runtime external-package constructor in PIR.
