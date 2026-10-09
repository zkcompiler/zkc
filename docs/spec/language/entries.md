# Entry declarations

This native contract defines closed Entry jobs and their source-level associations.

## Entry jobs

The short form `entry Session = Protocol<Args>;` selects a joint run. A proof Entry
uses an explicit block:

```text
entry Proof = Schnorr<G> {
  prover P;
  verifier V;
  public { base, point };
  accept accepted;
  target knowledge;
  construction fiat_shamir("merlin3.bls12-381.fr64be/0") {
    derive challenges;
  }
}
entry Release = Proof;
```

`prover`, `verifier`, `public`, `accept` and `construction` are required exactly
once, in any order. Proof jobs require two distinct protocol participants. Public
ports are named whole logical inputs and must cover exactly the data ports
available at the verifier, including empty logical ports. Their order is
canonicalized to declaration order. Relation purposes do not authorize inputs.
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
including static applications and repeated occurrences. It checks exact delivered
values and order through the same admission as an explicit native policy. An
unused selected service, omitted delivery or transformed challenge refuses; source
authors do not supply generated site names. These checks establish supported
construction, not a security theorem. Native proof admission and its limits still
apply to the resulting program.

`target` is optional. It names an existing target clause with the same acceptance
selector. Export requires entry-input operands, with witness ports unavailable at
the verifier and other purposes available there. The original gains one
`protocol.statement` at the selected protocol's start, retaining exact argument
components, participant selectors, relation and Boolean result index. Ordinary
clauses remain metadata; selecting no target emits no statement. Output-bound or
more general clauses remain valid attachments but cannot be selected for this
native statement ABI.

An Entry may name another complete Entry, including one declared later. Aliases
inherit the protocol, closed arguments, setup associations and every job choice. Cycles, partial
overrides and static re-specialization of an Entry refuse. Alias resolution uses
the source call-depth and work bounds.

### Setup associations

Run and proof Entries may associate inputs with named setup slots:

```text
entry Proof = Opening<Kzg> {
  setup pcs { vk, pk, statement.commitment };
  prover P;
  verifier V;
  public { vk, statement, point };
  accept accepted;
  construction authored;
}
entry Session = Opening<Kzg> { setup pcs { vk, pk, statement.commitment }; }
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
A block with only setup choices selects a run; adding any proof choice requires
the complete proof block. Empty blocks refuse.

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
