# Entry declarations

This native contract defines closed Entry jobs and their source-level associations.

## Entry functions

A protocol without static parameters provides a default run Entry selected by
its qualified protocol name, or an unambiguous short name. It reuses the generated
`Protocol::run` signature and has the Host body `return Protocol::run(inputs)`.
Its Entry kind is `function`; compilation, preparation, bindings, execution and
source correspondence follow the ordinary Entry function contracts. The internal
generated function name is not a second selectable Entry name.

The inventory includes these default Entries alongside authored Entry functions
and proofs, including imported concrete protocols. Omitted selectors require one
eligible candidate; defaults never shadow authored Entries. An explicit protocol
selector may apply static arguments, as in `Schnorr<G>`. It uses the source path
and static-argument grammar, consumes the entire selector, and checks all sorts,
requirements and closedness through the ordinary argument checker. Selectors are
bounded to 4096 UTF-8 bytes, including the reported qualified spelling, and the
existing token/type/work limits. Protocol
ambiguity is checked before argument or execution-kind validation. Non-protocol
Entries cannot receive static arguments through this interface.

Static names use the frozen checked namespaces of captured modules, including
resolved imports. An unqualified binding must have one declaration identity
across those namespaces; repeated imports of one declaration are not ambiguous.
Qualified paths and associated projections use the source resolver; an absolute
path such as `::example::G` explicitly starts at a captured module root. No module's
lexical context or enclosing static arguments are selected implicitly. All
required protocol parameters, including inherited module parameters, must be
supplied. No runtime-value inference, proof configuration or Host authority is
inferred.

The public selected name is the qualified protocol path followed by the supplied
argument tokens with whitespace/comments removed; string tokens are unchanged.
Its spelling is replayable, independent of caller scope. Equivalent argument
spellings may name different external selections, while the closed computation
retains the existing normalized type-argument identity. Only a requested generic
specialization joins that check response's finite Entry inventory. Definition
discovery, omitted selection and selector-free preparation enumerate no generic
instances. The captured project and checked source declarations remain unchanged.

`entry fn Name(parameters) -> Result { body }` declares an externally callable
Host function. Visibility, named arguments, ordinary generic helpers and Local
body inference follow the existing callable rules. Result annotations may be
omitted when uniquely inferable. The body has Host stage, independently of its
Local computational mode. Ordinary Local and Math helpers cannot invoke Host
functions or deployments. Calls resolve statically; cycles and ambiguous targets
refuse. No runtime function-name dispatch is introduced.

Entry functions may perform ordinary calculations, execute protocols or call
proof operations. Calls between entry functions use ordinary function-call syntax
and share the outer invocation's execution context and cumulative resource policy.

Host control uses the existing let/mut, products, variants, if, match, finite for,
require and final-return conventions. Numerical islands lower through the existing
Kernel and physical program pipeline. Only reached calls execute, in operand and
control order. No retry, memoization, parallel execution or effect reordering is
implicit. Invalid dormant branches and callable contracts are checked eagerly.

A closed protocol specialization `P<A>` generates nominal `Inputs`, `RunResult`
and `run(inputs)`. Ordinary Inputs/RunResult fields are indexed by participant;
shared ports retain distinct role components. A proof `D` generates `Public`,
`Witness`, candidate `Proof { bytes }`, projection-only `ProveResult`, and
`VerifyResult` with `Accepted { outputs }` and `Rejected` alternatives. The
operation signatures are `D::prove(public, witness)` and
`D::verify(public, proof)`. Exact specialization identity is part of each generated
type; structurally equal products do not make deployments interchangeable.
Service, setup and resource authority are not freely constructible data fields.
Only ordinary copyable native data crosses the Host numerical boundary;
affine managed custody remains with its native owner. Internal numerical
transport may preserve opaque or restricted nominal types, including existing
native results. It grants no source constructor authority: opaque factories
require their defining module's authority, and generated native results remain
projection-only. Compiler publication checks this source correspondence.
External input construction separately requires the schema's constructor
permission; numerical result reconstruction does not grant that permission.

Only successful explicit source return roots are published. Normal joint-run
false is ordinary data. Semantic verifier rejection produces Rejected without
success outputs; malformed framing, native stops and cleanup failures do not
produce a successful source return. Returning a candidate does not generate an
implicit verifier for the wrapping Entry. Its declarative proof remains callable
with an independently supplied public statement.

## Proof declarations

`proof` is contextual at declaration positions. A declaration closes a protocol's
static parameters and chooses proving/verification policy:

```text
proof-decl := "proof" name "=" path static-args? (";" | "{" clause* "}")
```

A protocol target requires a complete proof configuration block:

```text
proof Proof = Schnorr<G> {
  prover P;
  verifier V;
  public { base, point };
  accept accepted;
  target knowledge;
  construction fiat_shamir("merlin3.bls12-381.fr64be/0", challenges);
}
proof Release = Proof;
```

`prover`, `verifier`, `public`, `accept` and `construction` are required exactly
once, in any order. Proof jobs require two distinct protocol participants. Public
ports are named whole logical inputs and must cover exactly the data ports
available at the verifier, including empty logical ports. Their order is
canonicalized to declaration order. A mismatch diagnostic prints the expected
`public` list. This explicit list approves the whole logical public interface;
it includes setup-provided verifier keys even when the Host supplies their bytes.
Relation purposes do not authorize inputs.
`accept` names a Boolean output or product field available at the verifier;
its native result index follows the complete flattened output signature.

Optional `complete port.field;` selects a producer Boolean output or product
field, for example `complete result.ready;`. True permits completion; false
withholds that attempt's proof. This does not change the protocol body or add a
guard. Ordinary `prove` uses one attempt and refuses an incomplete result; the
application must call `prove_attempts` with a larger count to authorize retries. Completion belongs to proof production, not ordinary joint execution.

`construction authored;` selects the existing no-derived-transcript profile.
A `fiat_shamir` construction names an installed suite and exactly one verifier
random service with the corresponding field. Other verifier services remain
explicit private services in the verifier program.
The native compiler resolves the service's actual ordered query/delivery pairs,
including static applications and repeated occurrences. Both `draw()` and
`index<N>()` queries of that service are selected; each becomes a transition of
the same transcript at its occurrence. It checks exact delivered
values and order through the same admission as an explicit native policy. An
unused selected service, omitted delivery or transformed challenge refuses; source
authors do not supply generated site names. These checks establish supported
construction, not a security theorem. Native proof admission and its limits still
apply to the resulting program.

A named construction associates the protocol specialization with deployment
choices. It may have ordinary static parameters and requirements. Its contract
includes the target protocol's completed requirements and boundary obligations.
Omitting `where` infers usage, natural and capability requirements; a written
`where` clause must establish them. Invalid concrete targets fail even when the
construction is unused:

```zkc
construction ExternalWire<G: Group> for Schnorr<G> {
  base authored;
  format RawBytes;
}
```

An Entry selects it with `construction ExternalWire<G>;`. Its target and closed
static arguments must equal the Entry's target. `base authored` retains the
protocol's explicit transcript operations. An omitted format uses native
framing. `RawBytes` carries exactly one nonrepeated prover-to-verifier `Bytes`
message unchanged. The library must parse its record, check its acceptance
condition and reject unconsumed bytes. Format selection never depends on
candidate proof contents. These transport choices add no transcript binding.

`target` is optional. It names an existing target clause with the same acceptance
selector. Export requires entry-input operands, with witness ports unavailable at
the verifier and other purposes available there. The original gains one
`protocol.statement` at the selected protocol's start, retaining exact argument
components, participant selectors, relation and Boolean result index. Ordinary
clauses remain metadata; selecting no target emits no statement. Output-bound or
more general clauses remain valid attachments but cannot be selected for this
native statement ABI.

An Entry may name another complete Entry, including one declared later. An alias
uses the short form without a block, even an empty one. Aliases
must be proof aliases and inherit the protocol, closed arguments,
setup associations and every job choice. Cycles, partial
overrides and static re-specialization of an Entry refuse. Alias resolution uses
the source call-depth and work bounds.

### Construction bodies

A construction can select a module implementing an interface with `transcript Provider;` and a
finite set of verifier services with `replace {base, extension};`. The singleton
spelling is `replace challenges;`. Empty and duplicate selections refuse. The
compiler orders selected services by their original input positions. Every
selected service has the same owner; its actual query contract fixes the handler
result type independently of the provider's state or domain. The provider declares an associated
`State` and a zero-argument Local `initialize()` returning that state.
Both members must belong to the implemented interface; private helpers do not
satisfy provider selection. Source-created state requires `Copy` and `Drop`; private state need not permit
sharing or serialization.

An installed closed transcript domain can also be selected as the provider. Its
`State` is the affine `zkc::transcript::State<T>` supplied by the Host, with the
authorized invocation already absorbed. `zkc::transcript::observe`, `challenge`
and `challenge_index` advance that state using explicit byte labels. They do not
add generated site labels or loop coordinates. There is no source initializer
for a managed state. `base fiat_shamir("suite", challenges);` uses the same
managed root and supplies the native rules for selectors without an override.

Handlers are ordinary typed Local bodies:

- `on start(t, input, ...)` receives the state and named original protocol
  inputs, each available at both participants. It returns the next state.
- `on message label(t, value)` receives one complete logical message payload
  and returns the next state.
- `on query label(t)` returns `(state, value)`. An index query also supplies its
  request bound as the second handler parameter.

Selectors use [source site labels](protocols.md#site-labels). A dotted selector
descends through labelled protocol applications. A finite group, such as
`on message {commitment, response}(t, value)`, checks the body separately at
each selected payload type. Parameter annotations are optional and, when
written, must match the selected signature. Bodies cannot capture protocol
locals or undeclared inputs.

`base Other<...>;` inherits a construction for the same protocol specialization.
The provider and replacement authority remain fixed. A handler replaces the
whole inherited rule at that selector; other rules remain inherited. Without a
native base, the resolved construction must have a start handler and cover every
message and every query on the selected authority. Bases must be acyclic.

Retained verifier services remain explicit Host inputs with their own budgets.
Their replies may affect verifier-local guards, completion and acceptance. They
cannot affect outgoing messages, shared construction state, child-start inputs
or counts of loops containing shared construction events. Runtime admission
checks the actual Local bodies and repeated data flow conservatively; algebraic
cancellation of a private dependency is not inferred.

Each selected query and its delivery form one ordered construction event.
Retained queries belong before or after that pair. Both participants' loop
counts for shared events must be independent of unpublished private values.
Early completion remains explicit and may depend on private values; admission
does not claim termination independence.

### Child constructions

`apply Child<...> at call.path;` delegates one complete labelled protocol call.
The child's target and static arguments must match that call. Its closed
provider, state, initializer and root must match the parent, and its selected
services must be exactly the child ports mapped to the parent's selected
authorities, with the same verifier. All aliases of a selected parent authority
must be selected in the child; selected child ports cannot map to an unselected
parent authority. Parent services absent from the call require no child port. Selections must be disjoint and
acyclic. Inheritance can replace a whole child selection; parent mathematical
handlers cannot override individual leaves inside it.

The root initializes state once per participant. Each selected call invokes the
child's `on start` on the live state and that call's actual shared arguments,
before the child body. An event-free child still starts; a call inside a
zero-trip loop does not. Children must cover their messages and selected queries
without a native fallback. No implicit child domain tag is added.

Only the root selects a record format. A child with an explicit or inherited
format, or an inherited native root-binding requirement, refuses. A native-root
parent may delegate to an explicit child using the same managed provider.
Parent record-codec rules still cover delegated message leaves: child ownership
applies to mathematical handlers, while root transport covers the whole proof.

### Record codecs

`format Codec;` selects an ordinary module implementing an interface with an associated
`Record: Copy + Drop` and these Local methods:

```text
initialize(layout: Layout) -> Record
write(record: Record) -> Bytes
finish(record: Record, proof: Bytes) -> ()
```

The associated type and selected methods must be required by the implemented
interface. The compiler checks the complete signatures, including the absence
of callback and finite-domain arguments; the interface name is an ordinary
library choice. Bare `format Codec;` passes `()` to `initialize`.
`format Codec(rounds, size);` passes the named shared original inputs in order:
a single input keeps its type, and multiple inputs form a tuple. Layout inputs
must be available at both participants. An inherited format and its input
selection remain fixed; a different format needs its own construction.

The construction supplies rules for every prover-to-verifier message:

| Rule | Parameters | Result |
|---|---|---|
| `on encode site` | Record, actual logical payload | `(Record, Chunks)` |
| `on receive site` | Record, original proof Bytes | `(Record, Ranges)` |
| `on decode site` | Chunks | Logical payload |
| `on wire site` (optional) | Transcript state, Chunks | Transcript state |

Chunks defaults to `Bytes`. Annotating the decode parameter with a nonempty
product such as `(Bytes, Bytes)` selects multiple disjoint chunks. Ranges has
the same shape, replacing each `Bytes` with `(index, index)` for offset and
length. The compiler slices the actual immutable proof with bounds checks;
receive cannot substitute a different buffer. Decode sees only these chunks.
Codec rules do not cover erased challenge deliveries.

For example, `zkc::proof::Stream` accumulates sequential chunks and checks EOF:

```zkc
format Stream;
on encode response(r, value) { return Stream::append(r, encoding::field_be(value)); }
on receive response(r, proof) { return Stream::take(r, 32); }
on decode response(chunk) {
  let (valid, value) = encoding::field_from_be<F>(chunk);
  require valid;
  return value;
}
```

On the verifier, receive and slicing precede wire observation, decoding, then
mathematical observation. On the prover, encoding precedes wire and mathematical
observation. Omit `on wire` when the transcript observes only decoded values.
Codec functions use ordinary data computation; only wire and mathematical
handlers receive transcript authority. Record state is separate from transcript
state and cannot enter ordinary protocol operands or outputs. The exact exit
and failure rules are defined by [record construction](../ir/construction.md#record-transport).
A well-typed codec does not establish injectivity, byte coverage, round-trip
correctness or protocol security.

### Selection

The checked project exposes eligible concrete Entry declaration IDs sorted by
qualified name. `resolveEntry`, `selectEntry` and `closeEntry` share these rules:
an exact qualified name must
name an Entry; a short name must match exactly one Entry's terminal identifier;
an empty selector requires exactly one Entry across the capture. Complete
aliases remain distinct candidates. Selectors use exact NFC names under the
[Unicode source profile](lexical.md); no normalization or confusable-name matching
is performed. Missing or ambiguous selections refuse with
`source.entry` and list canonical candidate names and kinds. Adding candidates
cannot silently change a previously successful selection to another Entry.
An explicit generic protocol selector follows the static argument rules above.
`resolveEntry` returns the generated run declaration, checked arguments and public
selection name; `selectEntry` returns only that declaration ID. `closeEntry`
specializes through the same resolution, without changing the checked inventory.

Definition checking without selection does not close every Entry. The compiler's
`zkc.source-check/0` diagnostic report includes an `entries` array of objects with
`name` (qualified selection name) and `kind` (`function` or `proof`). A selected
generic instance joins only that response's inventory. A selected check reports
its qualified `entry` and `original` identity, with `scope: "entry"`;
an unselected check has `scope: "definitions"` and no selected Entry. Detailed
public callable inspection remains the optional `declarations` array.

### Setup associations

Proof declarations and protocol metadata may associate inputs with named setup slots:

```text
proof Proof = Opening<Kzg> {
  setup pcs { vk, pk, statement.commitment };
  prover P;
  verifier V;
  public { vk, statement, point };
  accept accepted;
  construction authored;
}
entry fn Session(inputs: Opening<Kzg>::Inputs) {
  return Opening<Kzg>::run(inputs);
}
```

A selector names an input or a visible product subtree. It retains logical port
and field indices; closure derives its native leaves. The selected subtree must
contain at least one setup-bearing leaf. Ordinary siblings are ignored. Native
collections remain one operand, including setup-bearing variant alternatives.
Paths cannot project through associated representations or variants.

Every setup-bearing input leaf must occur in exactly one slot. Selectors cannot
overlap, including within one slot. Names are unique identifiers, slots are
nonempty, and at most 64 slots are admitted. Association applies to every role
component of the logical input. The installed setup-bearing profile is
multilinear KZG, including keys and nested commitment/proof data. Merkle commitments
do not require a setup key. Slots do not introduce runtime operations or authorize
setup material.

A proof slot must include at least one whole public verifier-key input available
at the verifier. Every verifier-key input must satisfy that rule; at most 64
verifier-key ports are admitted in a proof Entry, independently of the slot count.
Prover-key inputs must remain at the prover. The Host pins
all keys in one slot to the same application-selected identity. Multiple slots
may select different identities. A joint invocation slot does not require a verifier-key input.
A protocol association supplies the joint invocation contract. A proof block
always requires its complete configuration, even if it also has setup slots.

Explicit setup association admits whole builtin `prover_key` and `verifier_key`
input ports through checked Host initialization. It does not grant external construction authority,
message transmission, nested/private key construction or opening-state ingress.
Other input constructors keep their existing permission requirements. Current
source slots require an input association; they do not express receive-only keys
or a separate expected key per receive site. The native Host's authorized setup
registry governs incoming PCS headers. An authorized value may decode and be
observed before `pcs.check` rejects a different explicit verifier key. Slots do
not name outputs: an unchecked returned commitment or proof is authorized but
not automatically tied to a specific output setup.
