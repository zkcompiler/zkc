# Shared mathematical protocols

The mathematical layer lets an author write algebra and post-message updates
once, while retaining a separate meaning for each role. Its
[profile](../spec/profiles/source/mathematical-protocols.md) defines the
contract. The compact examples below are explanatory. The existing frontend
accepts the closed scalar/group spelling shown in the
[authored Sigma fixture](../../tests/fixtures/mathematical/sigma.pir).

```text
mathematical source
  -> shared typed mathematical representation
  -> checked role placement with inline pure regions
  -> participant projection
  -> polynomial representation and kernel selection
  -> physical scheduling and execution
```

Each boundary has its own independently defined meaning. The mathematical
representation retains shared pure nodes, structured calls and indexed loops.
`Proc` expresses interaction and stopping behavior; it is the semantic target
for proofs rather than the storage format used by optimizers.

## Architectural capabilities

These are architectural commitments. See [status](../status.md) for current
support and the [roadmap](../roadmap.md) for implementation order.

| Capability | Application in zkc | Required evidence |
|---|---|---|
| Typed algebraic expressions and qualifiers | Mathematical source with nominal domains, static shapes and shared role-indexed names | Sigma and Sumcheck fit the same vocabulary; received components remain fresh |
| Shared graph operations | Typed interning and algebraic rewrites inside total pure regions | Actual sharing and useful checked rewrites; effects remain distinct |
| Data/transcript dependencies | Derived dependency views over ordered effects, calls, loops and capabilities | Message-before-challenge dependencies and dynamic occurrence paths survive |
| Verifier extraction | Availability and demand drive checked placement | Independent open-role source and placed meanings agree for all replies |
| Virtual polynomials | Shared factors, delayed evaluation/fixing and materialized alternatives | Representation and loop laws; identical canonical wire bytes |
| Algebraic completeness analysis | Useful ideal-membership certificates and group/field normalization | Certificate checking under explicit extraction and relation premises |
| Graph scheduling | Pure work and physical schedules checked separately | Data, alias, lifetime and budget conditions preserve complete outcomes |

The mathematical layer combines explicit role components, capabilities, complete
stopping semantics, checked transformation boundaries and connections to Lean
probability libraries.

The graph becomes useful when these consumers use its mathematical structure.
Authoring, analysis and placement share one admitted subject; projection retains
pure operations for later polynomial and kernel decisions. The implementation
sequence first connects an actual generated protocol, then structured polynomial
and component clients, while completing formal guarantees in the
[roadmap's stated order](../roadmap.md#1-the-remaining-sequence). The capabilities
above remain foundation requirements throughout that sequence.

## A closed Sigma fixture

```text
public generator : G, statement : G
private witness @ P : F
relation statement = witness * generator

nonce = query nonce_sampler @ P
a = send P -> V (nonce * generator)
c = send V -> P (query challenge_sampler @ V)
z = send P -> V (nonce + c * witness)
verify @ V z * generator == a + c * statement
return
```

The nonce sampler and challenge sampler are separate capabilities. The selected
challenge type is `F*`; its distribution must be supplied explicitly. A
full-field challenge or Fiat–Shamir replacement is a different experiment.
The verifier cannot query the prover's nonce capability: its action signature
requires a role-permission proof.

The maintained [Lean Sigma fixture](../../formal/Examples/Mathematical/Sigma.lean)
uses the canonical subject produced by `sigma.pir` and the actual installed BLS
carriers. `verifier_fresh_receive` exposes an arbitrary reply entering the
continuation's fresh binding. `prover_pure_commitment` connects the entry's
query, captured scale region and send, preserving the actual input environment.
These are prefix laws over every admission certificate of that exact subject.
Standalone honest algebra is proved separately; full trace honesty, native
provider agreement and protocol security remain open.

## Current authored profile

The frontend uses `mathematical protocol` to distinguish its body from located
role instructions. `inputs ((P, V) g: "bls12-381.g1"::Element, P x:
"bls12-381.fr"::Element);` declares the independent components available at each
role. This does not assert equality of shared inputs supplied by different roles.
A closed `bind` selects each total operation or entropy service. Flat `let` calls
and immutable aliases form pure regions; query, message and guard statements
remain ordered occurrences. A message result aliases the sender's operand at the
sender and denotes the actual received value at the receiver.

`roots (nonce = nonce_draw owners (P));` grants a service to its named owners;
`query [sample] P nonce -> (r);` creates a fresh reply occurrence.
`guard [verification] V(accepted);` rejects before either participant's suffix
executes. Repeated calls to a root consume that same root's state.

This first profile requires one closed protocol, instance and entry, a bijection
of roles, and scalar, group, nonzero scalar or Boolean values. It rejects helper
functions, extra executable declarations, generic bodies, structured expressions,
operators, products, loops and calls. Bind declarations may be unused; they do
not create executable bodies. All message schema labels, explicit effect sites,
root names and argument names are retained in the placed presentation. Each
schema has one payload type. Distinct labels remain distinct even with the same
payload. Name collisions refuse at common admission.

`protocol-inspect` returns a `mathematical_placement` object containing the
captured raw term, actual common target and untrusted witness. Its separate
`mathematical_correspondence: "unchecked"` status is deliberate: current native
execution and common-to-participant Lean checks do not establish this earlier
translation boundary. Authored text correspondence is also a distinct frontend
obligation.

## Structured Sumcheck

For a prover-held polynomial `p` of arity `n` and individual degree at most `d`,
carry a fixed-capacity point buffer and the scalar claim:

```text
state = (zero_vector(n), claimed_sum)
repeat i : Fin n carrying state:
  g = send P -> V round_polynomial(p, state.prefix, i)
  verify @ V g(0) + g(1) == state.claim
  r = send V -> P (query uniform_field @ V)
  state = (set(state.prefix, i, r), g(r))
evaluation = query terminal(p).evaluate(state.prefix) @ V
verify @ V evaluation == state.claim
return
```

The two components of `g` and `r` may differ in open-role execution. Updating
`state` once therefore still gives the verifier its received-message meaning.
Even when `p` is public and its honest round can be computed at V, the guard
must use the **received** `g`. An availability check alone cannot catch that
wrong-expression substitution.

The [Lean Sumcheck fixture](../../formal/Examples/Mathematical/Sumcheck.lean)
is one source family for arbitrary `n`. It uses the existing formal polynomial
with individual degree at most two and three-coefficient messages. `roundAt`
fixes the preceding coordinates using the actual bounded index. Finite controls
execute `(X₀+X₁)²` over `F₅`, reject a hostile first message before drawing,
and execute the zero-round terminal without fabricating an index.
They do not transfer the existing separate Sumcheck security theorem to this
new source family; that transfer still needs a correspondence proof.

The full polynomial profile preserves `d`, formal coefficient meaning and
virtual/materialized representations. It uses an explicit fixed-width
coefficient schema; normalized variable-length polynomial tags are not reused
for zero-padded messages. A private polynomial instead needs an appropriate
terminal service and its own binding/security premises.

## Repeated components and one shared service

The [component fixture](../../formal/Examples/Mathematical/Components.lean)
stores a helper once and invokes it twice. Both invocations resolve to one root
counter capability. Its final state is 2, and its query/message sites carry
different invocation paths. A terminal rejection retains both updates.
Calling a helper does not allocate a service. Two local capability ports may
alias one root identity; distinctness must be checked on resolved identities.

The same file separates sender aliases from arbitrary receiver replies and
executes a loop whose result depends on the bounded index. These controls
exercise meaning, without requiring a native optimizer or transport.

## FV connections

The [VCVio bridge](../../formal/integrations/arklib/ZkcArkLib/Mathematical/Execution.lean)
maps `Proc I A` to `OracleComp spec (Outcome A)`. Its structural inverse and
bind law preserve typed replies. `simulate_encode` uses VCVio's actual
`simulateQ` with a stopping state/event handler and equates its complete result
to `Proc.run`. An `Empty` reply for a terminal action is handled by stopping;
it cannot be provided by an ordinary total answer function.

The [ArkLib query bridge](../../formal/integrations/arklib/ZkcArkLib/Mathematical/PolynomialQueries.lean)
connects coefficient evaluation to ArkLib's actual polynomial `OracleInterface`
and retains service identity alongside a multivariate point query. This is a
query-answer law. Whole protocol views additionally need matching schedules,
statement/relation bindings, adversary information, challenge distributions,
stopping observations and terminal consumers. ArkLib views that defer a guard
can consume a challenge where this source stops; verdict equality cannot
establish unchanged resource state.
