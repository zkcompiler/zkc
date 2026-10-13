# Two-round full-prefix random-oracle simulation

The optional `ZkcSecurity.ArkLib.FiatShamir.Prefix` modules define and prove a
simulation from a typed full-transcript classical random oracle to the pinned
ArkLib salted state-restoration experiment. This specification concerns the
independent formal model. It supplies no native provider interpretation.

## Supported experiment

Fix one `StateRestoration.Round` and repeat its message and challenge alphabets
for exactly two rounds. A full-prefix query is one of:

- `first(input, message₀)`;
- `second(input, message₀, claimedChallenge₀, message₁)`.

Both return a challenge from the round's finite, nonempty, uniform sampler.
Every typed query is permitted, including inconsistent claimed challenges,
queries made before their ancestors, and repeated queries. One initially empty
lazy random-oracle cache spans the adversary and final verification. Each fresh
key draws an independent uniform answer; an existing key returns its cached
answer. The public input and both messages may be chosen adaptively.

The adversary is an `OracleComp` over that full-prefix interface, returning the
input, two messages, and a terminal witness. Verification queries the first key,
uses the resulting challenge in the second key, and returns the complete
ArkLib execution path with the input and witness. Its observation includes both
challenges, not only acceptance. The all-branch query bound counts accesses,
including cache hits, rather than native work or only fresh draws.

## Fixed key injection and retained cache

The target is exactly ArkLib's
`oracleSpec Input (Option round.Challenge) [round, round]`. Its encoding is:

```text
first(z, m₀)           ↦ here(z, m₀, none)
second(z, m₀, c₀, m₁) ↦ later(m₀, none, here(z, m₁, some c₀))
```

The encoding is fixed independently of the oracle table. The claimed earlier
challenge is explicit source-key data. `decode_encode` and `encode_injective`
prove a left inverse and collision freedom, including inconsistent prefixes.
`view_cacheQuery` proves cache updates commute with projection through this
injection. `view_outside` proves that adding any outside-image target entry
leaves the projected cache unchanged. Such entries remain in the target cache;
they are not discarded or used to resample an existing full-prefix key.

`adaptive_projection` proves response and projected final-cache equality for
all adaptive full-prefix clients and arbitrary initial target caches.
`adaptive_output` exposes its output-only form. There is no assumed key-image
invariant or assumed correspondence field. The source experiment has no raw
byte queries outside its typed domain. Extending it to arbitrary byte strings
requires a separately proved routing and cache simulation.

## Completion and security transport

`adversaryMap` translates each adversarial access and, after the adversary
selects its output, queries `here(z, m₀, none)` once. It emits the restoration
message/salt pairs `(m₀, none)` and `(m₁, some actualChallenge₀)`. This extra
query is necessary even when the original adversary made no first-round query.
The salts are reduction data; they are not fields in the source proof.

Pinned ArkLib completion then queries both target keys. Its first query repeats
the preparation query in the same cache. `repeat_query` proves that this repeat
returns the same answer and leaves the cache unchanged. `prepare_complete` and
`restoration_simulation` prove equality to translated full-prefix completion,
including the final target cache. `experiment_eq` connects the resulting
output to the independently defined full-prefix cached experiment for arbitrary
initial target caches. It therefore gives exact distributional equality, with
no statistical loss, for the initially empty experiments.

`adversaryMap_queryBound` proves `Q′ = Q + 1`. Applying ArkLib's
`restored_extraction_bound` charges another two accesses for completion.
`extraction_bound` consequently proves the conservative bound
`(Q + 3) * error` on permitted-input executions whose terminal knowledge witness
holds but whose named backward-extracted witness fails the initial knowledge
predicate. This is a direct application to the proved experiment, not an
assumption that the two constructions correspond. A protocol consumer must
supply its actual all-prefix extractor, prover preservation, local bad-challenge
bound, and terminal witness map. Any acceptance claim additionally needs the
protocol's terminal acceptance law.

The repeated first access is charged despite being a cache hit. No tighter
`Q + 2` bound is claimed here. The model does not expose query-log equality:
preparation adds an access. Nor does it establish a concrete extraction runtime.

## Boundary and validation

The result is for two repetitions of one round alphabet, unsalted source keys,
a single shared classical RO, and the stated full-prefix observation. It does
not prove a general variable-round, heterogeneous-challenge, source-salted,
child-session, private-oracle, QROM, or reset experiment. Extending to more rounds
requires an encoded salt-prefix construction, injectivity and cache laws, an
adaptive preparation program, completion equality, and a proved query charge;
none is supplied by assuming a fixed table-dependent encoding.

Native participant normalization, typed grouping of actual absorbs, statement
and domain binding, byte encoding, challenge decoding and sampler/provider
conformance remain separate obligations. In particular this theorem is not a
Merlin/STROBE or duplex reduction, and it does not imply the installed native
policy implements this ideal oracle.

The optional package's standalone `TestsSecurity.PrefixSimulation` controls
check statement/message/challenge binding, invalid salt shapes, out-of-order
and inconsistent queries, salt selection from the shared answer, and failure
when the completion access is omitted. `TestsSecurity.PrefixAudit` checks all
owned declarations' transitive axioms against the existing three-axiom allowlist.
See the [integration guide](../../integrations/arklib/README.md) for commands.
