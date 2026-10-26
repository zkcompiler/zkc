# Retained Sumcheck model transition

This document records a semantic API change, not a universal equality between
the historical uniform interpreter and Domain. The authoritative constructed
instruction meaning is `Domain.participant` over the admitted program's
`ringModel`. `SumcheckDomainConnection.retained` interprets that Process through
an explicit scalar ABI adapter.

## Selected artifacts and arbitrary values

`SumcheckDomainConnection.artifact_identity` checks the entire generated
`SmallSumcheckValidator.artifact` against the older `SumcheckProof.participant`.
`source_identity` checks the entire admitted source program. Reuse does not
depend on entry names or matching digest strings.

The checked root equation covers every `values : List F`, `claim : F`, and
`rounds : Nat`, with every field reply in every lawful monad. It does not
assume a relation, a valid table shape, a successful helper, or an honest size
bound. Excess rounds refuse. The terminal preserves its actual ordered tests:
point representability, point length below 64, and table representability.
Failure and the unread malformed proof head remain observable.

`round_projection`, `loop_projection`, and `root_projection` are equations of
the actual generated instruction Process. They discharge the reached operand,
result-sort, suite, request, template and coordinate checks. `helper_table`
and `Domain.Binding.helperTable_ringModel` fix the actual helper bodies and
their admitted dependency prefixes. The finite protocol normal forms do not
interpret instruction constructors.

## Exact theorem dispositions

The old `SumcheckProof.compiled_transform` quantified arbitrary typed public
values, history, proof, service handle and lawful monadic challenge. Its left
side was the acceptance projection of:

```lean
ideal context challenge table participant.returned participant.instructions
  (inputs values claim rounds ++ [.transcript initial]) proof
```

The maintained theorem has the same quantifiers and original-transform right
side. Its left side now uses:

```lean
SumcheckDomainConnection.retained challenge values claim rounds initial proof
```

`legacy_compiled_transform` retains the exact previous typed proposition.
`retained_legacy` proves equality of the complete return outcome and unread
proof before acceptance. The maintained theorem is proved directly through
`SumcheckSourceVerifier.verifier_optional`, the actual source rounds and
`SumcheckVerifierTerminal.terminal_decision`; it does not use the old generic
uniform construction/projection soundness proof.

`SumcheckProof.compiled_transform_rounds` makes the same left-side transition;
`legacy_compiled_transform_rounds` retains its exact previous proposition.
Its existing decoded-table and resource premises belong to its mathematical
terminal interpretation. They are not premises of `retained_legacy`,
`compiled_transform`, or the byte transport.

The former `SumcheckProof.spec_transform` is retired. It quantified
`data : List (Value F G)` with only `data.length = 3`, including incorrectly
sorted or unsupported raw values. It equated the old `ideal` acceptance with
the transform of the old `spec` instruction reading. That statement described
those two historical models; it supplied no Domain sort or metadata check.
There is no claim that the maintained typed theorem is equivalent to this raw
statement. The replacement for the selected actual artifact is the maintained
`compiled_transform` above. The original raw statement and its proof remain in
Git history at base `20e9a277a`.

`raw_model_disagreement` checks this boundary on the unmodified selected
Sumcheck artifact: with a Boolean in the claim slot and one round, the old
model consumes both field messages before refusing. Domain refuses at input
sort checking and leaves both messages unread. The two full results differ
for every tail, low value and high value. This is an actual raw-input failure
of the proposed universal transport, in addition to the malformed-guard
mutation below.

The generic `Uniform.check_sound`, `Uniform.compiled_transform`, and
`Uniform.compiled_selected` have **not** been reinterpreted or silently given a
sorted-input premise. They remain historical model statements required by
other current consumers. This lane does not claim their deletion or generic
Domain replacement.

`SumcheckDomainControls.legacy_malformed_guard` and `nominal_malformed_guard`
give an actual counterexample to unconditional transport: a true guard with
one declared Boolean result continues in the historical model and refuses in
Domain. The checked selected artifact has no such reached instruction. This
counterexample precludes obtaining retirement by merely renaming the old
interpreter or replacing its definition by Domain.

## Histories, queries and original sends

Legacy initialization is an arbitrary opaque prefix. Only the execution suffix
is projected to old events. Scalar payload, proof, data, transcript and return
adapters are explicit and partial. Unrepresentable values refuse.

`legacyOrigin` removes the delimited dynamic-coordinate suffix. The four
selected origin equations hold at every iteration index, not only honest
ones. `message_identities` and `query_identity` check actual source sites,
senders, receivers and draw request. The direct source proof keeps delivery as
an actual send; it is absorbed as a message. `query_not_delivery` distinguishes
that event from the challenge occurrence. Outcome/proof projection does not
assert identity of physical observation lists or runtime frames.

The adapter maps the complete suffix and key **before** invoking the existing
legacy challenge function. `query_state` preserves its entire arbitrary
`StateT` state, so cache updates, random state and query counters follow that
same function. `nominal_queries_distinct` and `legacy_query_collision` show why
this is not an equivalence with an independently sampled nominal random
oracle. No injectivity, sampling, adversary or query-cost equivalence between
those enlarged games is asserted.

## Bytes and the remaining deletion boundary

`executable_metered` retains its exact proposition about the actual executable
and costed lowered Code. `metered_domain_prunes` connects that Code result to
the complete adapted Domain return and unread proof at every budget.
`executable_prunes` now targets Domain; `executable_legacy_prunes` retains the
exact old byte proposition. `executable_transform_prunes` retains its exact
original-transform byte proposition through the maintained Domain theorem.

The decoder, actual native codec scope, 40-byte frame treatment, binding
header, whole-proof acceptance, helper/instruction charges and cleanup are
unchanged. Existing executable resource and cleanup controls still apply.

The historical `specK/specStep` and `idealK/idealStep` definitions have **not**
been deleted. In particular, generic Code metering/pruning proofs and the
finite historical comparison still depend on them; `meteredStep` still calls
the historical scalar step. Removing those cases now would leave the protected
byte proof without its checked VM connection. The migrated source proofs use
Domain alone; the old duplicate execution path remains in the Code dependency
chain. Its retirement remains an open integration obligation. This document
must not be cited as final semantic closure or as native cryptographic
security evidence.
