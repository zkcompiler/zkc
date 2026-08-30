# Source and Current-Model Reconstruction

> **Kind:** Temporary source and architecture research record
> **State:** Complete for the selected source revision and current checkout
> **Authority:** None. This page records reconstruction and comparison; it
> neither defines PIR semantics nor establishes source-theorem applicability.

## 1. Result

The reviewed construction is not a parameter choice inside the active
canonical-framed transcript. It is a different transcript state machine and a
different Fiat--Shamir construction contract.

The source can be represented over the unchanged `InteractiveCore`, but only
if PIR adds all of the following outside that Core:

1. a separately identified duplex-sponge transcript construction;
2. a total correspondence from the Core's public runtime instance to the
   paper's binary instance `x`;
3. one construction-public, proof-carried salt with separate generation and
   replay authority;
4. the exact overwrite state and cursor transitions;
5. a protocol-derived fixed alternating schedule and fixed codecs; and
6. distinct verifier-complete and prover-required execution prefixes.

Ideal random-function and ideal-permutation behavior, inverse-permutation
adversary access, decoder bias, salt distribution, source theorem premises,
and quantitative losses do not become construction-admission facts. They
remain Analysis obligations.

## 2. Pinned source

The source of record is Chiesa and Orrù,
[*A Fiat--Shamir Transformation From Duplex Sponges*](https://eprint.iacr.org/2025/536),
revision 27 March 2026. The reviewed PDF has SHA-256
`fca7ba09ebe59141c3c041ac660b4e3e161fdab8a709aee67e236db8d8da3a35`.

The exact source ownership used here is:

| Source location | Reconstructed authority |
|---|---|
| Construction 3.3, pp. 18--20 | State, initialization, overwrite absorption, squeezing, and cursor behavior |
| Definition 4.1, pp. 27--28 | Per-round prover encoders, verifier decoders, exact lengths, and codec bias |
| Definition 4.2, p. 28 | Random-function and permutation experiment shape |
| Construction 4.3, pp. 28--29 | Salt, proof tuple, round schedule, and prover/verifier algorithms |
| Sections 5--7 | Theorem premises, adversary access, reductions, and quantitative losses |
| Section 8.2, pp. 69--70 | A session-identifier implementation variant, not literal Construction 4.3 |

Operational pseudocode owns transitions when later cost prose disagrees with
it. A theorem proof may reveal an applicability requirement, but it does not
silently enlarge the construction definition.

## 3. Exact operational construction

### 3.1 State and initialization

Let `Sigma` be a nonempty finite alphabet with distinguished symbol `0`, let
`r > 0` be the rate, and let `c` be the capacity. The source state is:

```text
DuplexState = (s, i_A, i_S)
s            in Sigma^(r+c)
i_A, i_S     in [0,r]
```

For a binary runtime instance `x`:

```text
Start_h(x):
  s := (0^r, h(x))
  return (s, 0, r)
```

`Start_h` makes one `h(x)` query and no permutation call. The paper already
receives `x` as a binary string. It does not define a codec from a typed zkc
invocation to `x`; that mapping is a zkc correspondence obligation.

### 3.2 Overwrite absorption

```text
Absorb_p((s,i_A,i_S), chi):
  i_S := r

  if chi is empty:
    return (s,i_A,r)

  if i_A < r:
    overwrite s_R[i_A] with first(chi)
    return Absorb_p((s,i_A+1,r), rest(chi))

  // i_A = r and input remains
  s := p(s)
  return Absorb_p((s,0,r), chi)
```

The exact consequences are:

- absorption overwrites rate cells; it does not XOR;
- there is no padding, delimiter, length frame, namespace, or eager final
  permutation;
- empty absorption can change behavior because it sets `i_S = r`;
- merely filling the final rate cell does not call `p`;
- the next waiting input symbol calls `p` before it is written; and
- consecutive absorbs without a positive squeeze equal one concatenated
  absorb.

For positive length `L` beginning at absorb index `a`, the pseudocode makes
`floor((a + L - 1) / r)` permutation calls during that absorb. The following
positive squeeze may make the boundary call.

### 3.3 Squeezing

```text
Squeeze_p(st, 0):
  return (empty, st)

Squeeze_p((s,i_A,i_S), ell > 0):
  i_A := 0

  if i_S < r:
    emit s_R[i_S]
    continue with i_S + 1 and ell - 1

  // i_S = r
  s := p(s)
  continue with i_S = 0 and unchanged ell
```

Therefore:

- zero-length squeeze is an exact no-op, including both cursors;
- every positive squeeze resets `i_A = 0`;
- consecutive squeezes continue one stream and equal a combined squeeze;
- an absorb after a partial squeeze discards the unread stream by setting
  `i_S = r` and overwrites again from rate position zero; and
- a decoded verifier value is not reabsorbed.

These laws distinguish this construction from prefix-XOF adapters, Keccak XOR
duplexing, Keccak's separate `OVERWRITE` mode, STROBE, and Merlin.

## 4. Codec and transform

For round `i`, the paper's codec contains:

```text
phi_i : M_P,i -> Sigma^ell_P(i)      injective
psi_i : Sigma^ell_V(i) -> M_V,i      total
```

The distribution of `psi_i` on a uniform alphabet string has a declared bias
from the intended uniform verifier-message distribution. The construction
performs one decode and has no retry or rejection sampler.

For an interaction with `k` prover rounds, the transform is:

```text
state := Start_h(x)
tau   <- Uniform(Sigma^delta)
state := Absorb_p(state, tau)

for i = 1 .. k:
  state := Absorb_p(state, phi_i(alpha_i))
  (raw_i,state) := Squeeze_p(state, ell_V(i))
  rho_i := psi_i(raw_i)
```

The abstract proof is exactly:

```text
pi = (tau, alpha_1, ..., alpha_k)
```

It carries neither verifier messages nor transcript frames. The paper does
not specify a byte serialization, canonical parse, malformed-input policy, or
trailing-byte rule for this abstract tuple. Fixed transcript-codec lengths do
not decide proof serialization; Interface and OIR must own it.

### 4.1 Prover/verifier asymmetry

The paper's argument prover needs transcript derivation only for `i < k`.
After producing `alpha_k`, it does not encode, absorb, squeeze, or decode the
final round. The verifier performs every transition through `i = k` before
evaluating acceptance.

Consequently the target must distinguish:

- the verifier-complete Fiat--Shamir interpretation; and
- the transcript prefix required by an honest proof-generation Plan.

Making a verifier compute the final challenge is mandatory. Making a prover
compute it can be proof-equivalent, but is not exact source oracle-trace or
resource correspondence.

## 5. Source gaps and applicability obligations

The fresh audit found five matters that must remain explicit.

### 5.1 Decoder-preimage sampling

The security arguments sample uniformly from `psi_i^-1(rho_i)` and invoke a
lemma for surjective functions. Definition 4.1 states totality and a bias
condition, but does not explicitly require surjectivity or an efficient
uniform-preimage sampler.

Forward execution therefore needs only total `psi_i`. Exact knowledge or
zero-knowledge theorem applicability remains unresolved unless a selected
codec supplies the stronger inverse-sampling premise or the source is
clarified.

There is a stronger proof defect. Claim 5.22 treats sampling a uniform message
and then a uniform element of its decoder fiber as uniform on the encoded
domain. That is false when fibers have unequal sizes. The statistical distance
is the forward decoder bias, not zero. A repaired theorem must either require
balanced fibers or charge the additional bias; the current general biased-
decoder proof cannot be activated as written.

### 5.2 Non-power-of-two alphabets

The reduction uses `delta* = delta log_2 |Sigma|` and an injective fixed-length
binary encoding of `Sigma^delta`. For non-power-of-two alphabets, that displayed
bit length need not be integral. An exact theorem profile must expose this
source-resolution obligation rather than choose a ceiling or variable-length
repair silently.

### 5.3 Permutation-call prose

The page-28 efficiency prose counts `ceil(L/r)` calls for a positive absorb
phase, while Construction 3.3's lazy-boundary pseudocode gives
`floor((L-1)/r)` from index zero inside the absorb. Sections 4--5 then use the
incompatible count in exact backtracking offsets. Executable semantics follow
Construction 3.3, but the current proof requires repair or an erratum; this is
not merely a missing target premise or a conservative cost-bound choice.

### 5.4 Positive rate

The construction notation does not make `r > 0` explicit, although positive
absorb and squeeze fail to terminate at `r = 0` and later expressions divide
by `r`. The target construction must make positive rate a well-formedness
condition and record that this is an explicit source repair.

### 5.5 Session identifier

Section 8.2 describes `Start_h(sid || x)` as a composability-oriented
implementation variant and leaves universal-composability security open. It
is not literal Construction 4.3 and cannot silently inherit that
correspondence or theorem profile.

## 6. Comparator findings

The comparison set reinforces one rule: an `absorb`/`squeeze` host API is not
a semantic construction definition.

| Construction | Materially different choice | Consequence for zkc |
|---|---|---|
| CO25 Construction 3.3 | Literal overwrite with two persistent cursors | Exact cursor and boundary behavior is identity-bearing |
| CFRG FS draft 03 | XOF snapshot/reader behavior; empty absorb is a no-op | Similar API, different state machine and source theorem |
| Keccak duplex | XOR absorption, padding, then permutation | `Duplex` alone is not a complete construction name |
| STROBE | Operation flags, boundaries, streaming state, and role adjustment | Runtime operation boundaries can change meaning |
| Merlin | Fixed labels and encoded lengths over STROBE | Canonical framing is useful but not raw-source correspondence |
| SAFE | Declared I/O pattern and terminal closure | Schedule exhaustion is useful; normalization is not universally valid |
| Spongefish | Common interface over exact and heuristic constructions | Trait compatibility does not imply theorem compatibility |
| Halo2 | Wire encoding and transcript encoding may differ | Interface/OIR and transcript codecs need separate owners |

The strongest small discriminator is:

```text
partial squeeze -> empty absorb -> next squeeze
```

The CFRG adapter leaves the empty absorb inert; Construction 3.3 resets the
squeeze cursor and changes the next result. A generic API signature cannot
recover that semantic difference.

## 7. Entry-target reconstruction

At package entry, the active
[Fiat--Shamir page](../../../../pir/fiat-shamir.md) defined one closed
canonical-framed transcript construction. Its identity commits to a fixed
initial state, state and byte types, absorb/squeeze/advance algorithms,
application-domain declaration, sampling failure, and an ordered total map of
challenge rules.

Its owner-derived schedule absorbs:

- Core, construction, and application-domain headers;
- typed public bindings and scope events;
- active messages, Oracle effects, guards, and challenge conditions;
- per-challenge namespaces and per-draw material; and
- bounded retry outputs.

That design correctly enforces strong statement and prior-message influence
for its own construction. It deliberately has no authored message skip map.
It cannot literally represent the reviewed source because the source instead
requires:

| Source coordinate | Current obstruction |
|---|---|
| Runtime `Start_h(x)` | Construction has one fixed identity-bearing initial state |
| Proof-carried salt | Core invocation has no construction-public material lane |
| Raw `phi_i(alpha_i)` | Every current occurrence receives typed canonical framing |
| One-shot `psi_i` | Current challenge law includes namespace, acceptance, retry, and separate state advance |
| Source fixed alternating schedule | Current construction covers a more general Core and effect algebra |
| Prover derivation prefix | Current PIR records verifier-complete execution only |

Treating `tau` as a Core message would change the Fresh source interaction.
Treating it as SessionContext would misclassify proof-carried transform
material. Reusing the current frames would identify a different transcript.

### 7.1 Pre-selection runtime and record gap

Before this package, `CoreInvocation` carried public and verifier-private Core
inputs. Initial Oracle material had a separate runtime capability lane, but no
corresponding Fiat--Shamir construction-public lane existed. `RunRecord`
retained Core occurrences, challenges, Oracles, and terminal output, but no
family-specific resolver-initialization result.

The duplex construction therefore needs public construction material bound to
the exact FS Protocol and Core invocation. Successful execution retains the
closed initialization result in the first duplex challenge receipt; missing or
invalid material and operational evaluation failure produce no completed
Protocol record, because this family defines no semantic interpretation-
failure variant. The actual salt must not enter `CoreId`, `CoreInvocationId`,
or construction identity.

### 7.2 Pre-selection Analysis-view gap

The entry-target static views assumed canonical-framed fields such as a fixed initial
state, frame law, challenge namespaces, retries, and sampling exhaustion.
Analysis needs a common construction surface plus family-specific views. A
consumer must not pretend that a field absent from the duplex construction is
present with an empty value.

### 7.3 Retained Interface and OIR gap

The target has no proof-field owner for construction-public material. OIR must
eventually specify where `tau` appears, how it is parsed, and how parsed
message objects project to the PIR semantic values whose distinct transcript
codecs are used. This package does not select those bytes.

## 8. Current implementation map

The production C++ tree does not currently expose the target transcript-
construction subject and resolver lifecycle as a complete implementation.
The most direct executable pressure is in research instruments:

| Surface | Current evidence |
|---|---|
| Canonical-framed Core/FS lifecycle | `evaluation/k2-protocol-fiat-shamir/` |
| Exact Schnorr statement/influence behavior | `evaluation/r2-p01-schnorr/` |
| Native FRI logical-Oracle and FS paths | `evaluation/native-fri-ior/` |
| OIR projection pressure | `evaluation/k3-oir-projection/` |
| Analysis source closure | `evaluation/k3-analysis-closure/` |
| State-restoration theorem carrier | `include/zkc/Soundness/` and `lib/Soundness/` |

The new executable package is therefore a target-model falsifier, not a patch
to a production transcript implementation. Migration starts only after the
semantic target and retained finite evidence close.

## 9. Owner map

| Fact | Exact owner |
|---|---|
| Core messages, challenges, checks, claims, and causal execution | PIR `InteractiveCore` |
| Common Fresh/FS same-Core relation | PIR common FS owner |
| Exact duplex state, codecs, schedule, and construction-public schema | PIR duplex construction owner |
| Runtime salt value and resolver initialization receipt | PIR execution data |
| Honest salt-generation algorithm and private randomness | Plan/Realization |
| Proof tuple placement and canonical parsing | Interface/OIR |
| Ideal models, inverse access, bias, entropy, and source theorem premises | Analysis |
| Concrete provider correspondence and observed executions | Realization/Evidence |

This routing preserves the core result of the redesign: verifier-observable
interaction remains the shared protocol subject, while each Fiat--Shamir
construction is separately identified and separately analyzed.
