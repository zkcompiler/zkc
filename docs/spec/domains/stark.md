# Parameterized single-table STARK reduction

This contract describes `stark::single_table::ScalarTableArgument` and
`BlockTableArgument`, their logical
assignment interface and the DEEP word supplied to the common FRI library.
It does not establish a soundness theorem for the complete compiled argument.
The [library guide](../../../libraries/arguments/stark/README.md) describes
configurations and execution coverage. The octic and whole-Bundle callers have
separate aggregate-degree contracts.

## Shared phases and explicit sampling

Both public entrypoints use the same private preparation and completion
protocols. Preparation finishes the DEEP reduction and common FRI commitment
phase, including terminal coefficients. It returns an opaque FRI commitment
state together with separate prover and verifier opening records. Native
commitment state stays at the prover; it is not embedded in a shared logical
record or in the public statement.

`ScalarTableArgument` then samples one index per request.
`BlockTableArgument` samples the complete index sequence in one request. Each
requires the corresponding service capability. Neither entrypoint changes the
sampling law implicitly. The authored `fri_queries.positions` path identifies
the block request for construction selection. A gate, when explicitly selected,
applies there, after commitments and before openings.

Both bind the exact resulting sequence through common FRI `BindQueries` and
call the same completion protocol. Completion obtains positions from that
state, authenticates the outer rows, reconstructs the adjusted DEEP values and
calls common `QueryAssociated`. Query values cannot be substituted between
these phases by a separately supplied index list.

The quartic KoalaBear `Keccak256` configuration uses direct quartic challenges
and Keccak row commitments for both base and extension rows. It does not
project octic draws. The existing Poseidon2 configuration retains its explicit
octic-to-quartic conversion; the two configurations share the reduction.

## Assignment and opening inventory

The captured relation Bundle supplies the table identity, witness/configuration/
public column groups, public scalar slots, assertion scopes and expression arena.
Matrices are row-major in group declaration order at the interface; column
polynomials use explicit transposition. The verifier's complete statement and
selected configuration determine the field, basis, shift and public data.
Native commitment layout does not redefine these logical positions.

Let `n = 2^(LogFinal+Rounds)` and `N = n*2^LogBlowup`. Rounds, LogBlowup and
Queries are positive; the installed two-adic domain must contain N distinct
points. Trace columns and quotient chunks have intended strict degree `< n`.
The nonzero evaluation coset must be disjoint from the trace subgroup.

The opening inventory preserves every expression-arena input in its original
order, including its authority, column and rotation modulo n. Append one
witness input at rotation zero for each committed witness column absent from
that prefix, in ascending column order. This suffix supplies degree coverage;
it does not add AIR assertions or change public/witness assignment meaning.
Known configuration/public columns and public scalars are evaluated from the
statement. Every quotient chunk is opened at the OOD point itself.

The prover sends exactly the extended input-claim vector and the quotient-claim
vector. The verifier checks the full input-claim count and uses only its original
arena prefix in the AIR identity. Added claims still participate in DEEP and
are checked against authenticated witness rows. No unread committed column is
silently treated as already degree-checked.

## Challenges and degree adjustment

The ordered protocol prefix is trace commitment, composition challenge alpha,
quotient commitment, OOD challenge zeta, then input/chunk claims and the checked
AIR identity. Both roles stop unless zeta avoids the trace subgroup and the
evaluation coset; the rotated opening points must also avoid the coset.

After these claims, sample and deliver gamma, followed by a fresh independent
adjustment delta. In inventory order, every witness input contributes
`(T(X)-v)/(X-zeta*g^rotation)`; append every quotient chunk contribution
`(Q_j(X)-q_j)/(X-zeta)`. Weight these terms by consecutive powers of gamma,
starting at one, to obtain D. The actual first FRI word is
`W(X) = (1 + delta*X) D(X)` on the evaluation coset. The common FRI contract
remains strict degree `< n`; an honest D has degree `< n-1`.

At each query, authenticate the trace and chunk rows under the actual committed
roots and recompute the same adjusted value. The common FRI checker must compare
that value to its authenticated initial handle at the same query position,
before checking the fold chain and terminal polynomial. Acceptance cannot ignore
this equality or an authentication result.

The adjustment changes the transcript. Zero challenges and coefficient
cancellation remain possible under the declared law; they are not implementation
exceptions. Neither syntactic dependence nor an execution test proves uniformity.
The configuration's challenge conversion needs its own joint-distribution law.

## Scope of the degree argument

For a fixed word's degree-<N interpolant R and coset vanishing polynomial
`X^N-s^N`, an honest `deg R < n-1` yields adjusted degree `< n` for every delta.
Otherwise at most one delta makes `(1+delta X)R mod (X^N-s^N)` have degree `< n`:
the high coefficients are affine in delta; for degree n-1 its degree-n
coefficient is a nonzero multiple of delta, and for larger degree the high
coefficient vector has a nonzero constant part. Multiplication by X alone is
insufficient: `X^(N-1)` wraps to the constant `s^N`.

This exact-membership argument does not replace proximity, DEEP batching,
commitment extraction or Fiat–Shamir composition hypotheses. Quotienting and
its degree/proximity relation are studied in
[DEEP-FRI, §4.2.1](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITCS.2020.5).
The implementation supplies the stated reduction and rejection controls; a
formal security claim must separately instantiate the relevant theorems.
