# Entry declarations

This native contract defines closed Entry jobs and their source-level associations.

## Entry jobs

`run` selects joint execution; `proof` selects proving and verification. They
are contextual at declaration positions, so ordinary variables and fields may be
named `run` or `proof`. Both produce the same checked Entry abstraction, with an
explicit execution kind.

```text
entry-decl := ("run" | "proof") name "=" path static-args?
              (";" | "{" clause* "}")
```

`run Session = Protocol<Args>;` selects a joint run. Its optional block accepts
only setup associations; an empty block is equivalent to the short form.
A `proof` targeting a protocol requires a complete proof block:

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
application must call `prove_attempts` with a larger count to authorize retries. Run Entries cannot carry a completion selection.

`construction authored;` selects the existing no-derived-transcript profile.
A `fiat_shamir` construction names an installed suite and exactly one verifier
random service with the corresponding field. Other verifier services refuse.
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
choices. It may have ordinary static parameters and requirements:

```zkc
construction ExternalWire<G: Group + Share> for Schnorr<G> {
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
must have the same run/proof kind and inherit the protocol, closed arguments,
setup associations and every job choice. Cycles, partial
overrides and static re-specialization of an Entry refuse. Alias resolution uses
the source call-depth and work bounds.

### Construction bodies

A construction can select a component with `transcript Provider;` and a
verifier service with `replace challenges;`. The provider declares an associated
`State` and a zero-runtime-argument Local `initialize()` returning that state.
Source-created state requires `Copy` and `Drop`; private state need not permit
sharing or serialization.

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

### Selection

The checked project exposes all Entry declaration IDs sorted by qualified name.
`selectEntry` and `closeEntry` share these rules: an exact qualified name must
name an Entry; a short name must match exactly one Entry's terminal identifier;
an empty selector requires exactly one Entry across the capture. Complete
aliases remain distinct candidates. Selectors use exact NFC names under the
[Unicode source profile](lexical.md); no normalization or confusable-name matching
is performed. Missing or ambiguous selections refuse with
`source.entry` and list canonical candidate names and kinds. Adding candidates
cannot silently change a previously successful selection to another Entry.

Definition checking without selection does not close every Entry. The compiler's
`zkc.source-check/0` diagnostic report includes an `entries` array of objects with
`name` (canonical qualified name) and `kind` (`run` or `proof`). A selected check
reports its canonical `entry` and `original` identity, with `scope: "entry"`;
an unselected check has `scope: "definitions"` and no selected Entry. Detailed
public callable inspection remains the optional `declarations` array.

### Setup associations

Run and proof Entries may associate inputs with named setup slots:

```text
proof Proof = Opening<Kzg> {
  setup pcs { vk, pk, statement.commitment };
  prover P;
  verifier V;
  public { vk, statement, point };
  accept accepted;
  construction authored;
}
run Session = Opening<Kzg> { setup pcs { vk, pk, statement.commitment }; }
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
may select different identities. A run slot does not require a verifier-key input.
A run block accepts setup associations without proof choices. A proof block
always requires its complete configuration, even if it also has setup slots.

Explicit setup association admits whole builtin `prover_key` and `verifier_key`
input ports through checked Host initialization. It does not grant `Wire`,
message transmission, nested/private key construction or opening-state ingress.
Other input constructors keep their existing permission requirements. Current
source slots require an input association; they do not express receive-only keys
or a separate expected key per receive site. The native Host's authorized setup
registry governs incoming PCS headers. An authorized value may decode and be
observed before `pcs.check` rejects a different explicit verifier key. Slots do
not name outputs: an unchecked returned commitment or proof is authorized but
not automatically tied to a specific output setup.
