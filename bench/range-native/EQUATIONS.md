# Equations, wire decisions and terminal obligations

All arithmetic below uses the scalar field of Ristretto and actual Dalek points. Let the scalar order be `ℓ = 2^252 + 27742317777372353535851937790883648493`. For admitted `n ≤ 64`, integer embedding of `[0,2^n)` is injective. `B` denotes the value base and `B̃` the blinding base; `Q` denotes the IPA coefficient point.

## 1. Source authority and exact pins

The algorithm reading is the **released local Bulletproofs 5.0.0 source**, VCS `86eadbeeb4a96d8da41427137b45ead810d03b41`. [Release provenance](https://docs.rs/crate/bulletproofs/5.0.0/source/.cargo_vcs_info.json). Line numbers below refer to that release. No Dalek 2.0 `main` source was used.

| Obligation | Released source and lines | Native body |
|---|---|---|
| Pedersen bases | `src/generators.rs:44–53` | `generators.rs::new` |
| Generator stream/order | `src/generators.rs:64–100,179–207` | `generators.rs::new` |
| Bits and masks | `src/range_proof/party.rs:86–148` | `prover.rs::prove_core` |
| `l,r,t1,t2` | `src/range_proof/party.rs:183–243` | `prover.rs::prove_core` |
| Responses and `x=0` guard | `src/range_proof/party.rs:280` onward | `prover.rs::prove_core` |
| Aggregation and range-to-IPA handoff | `src/range_proof/dealer.rs:226–282` | `prover.rs::prove_core`, `verifier.rs::evaluate_core` |
| Exact transcript framing/challenges | `src/transcript.rs:44–54,65–95` | `transcript.rs::Flight` |
| Recursion and terminal weights | `src/inner_product_proof.rs:38–253` | `prover.rs::ipa_prove`, `verifier.rs::ipa_folding/ipa_flat` |
| Upstream combined verifier | `src/range_proof/mod.rs:344–452` | `baseline.rs` only |
| Executable delta | `src/range_proof/mod.rs:588–594` | `verifier.rs::evaluate_core` |
| Raw codec | `src/range_proof/mod.rs:488–544`; `src/inner_product_proof.rs:341–416` | `codec.rs` |

The source comment preceding upstream `delta` writes powers of two of length `nm`, while its executable body uses length `n`. This experiment follows the body and the derivation below. The earlier research report flags an IPA prose typo in the `b` fold; this implementation follows the released executable `b_R` fold. No semantic defect is hidden by changing a source pin.

## 2. Generators and integer statement

For party `j`, construct separate SHAKE256 XOFs with bytes:

```text
"GeneratorsChain" || "G" || u32LE(j)
"GeneratorsChain" || "H" || u32LE(j)
```

Read consecutive 64-byte blocks and map each with `RistrettoPoint::from_uniform_bytes`. Take the first `n` points per party and concatenate in party-major order `i=jn+b`. This is a stream per party/family, not a separate hash per index. `B` is `RISTRETTO_BASEPOINT_POINT`. Independently derive `B̃` by SHA3-512 of the 32-byte compressed basepoint followed by `from_uniform_bytes`.

The tests compare all 1024 directly exposed upstream `G` points for `(64,16)` and both Pedersen bases. Upstream's `H` accessor is private: exact `H` correspondence is exercised through cross-verification, not asserted as a direct private-array comparison. Smaller per-party prefixes are compared against the independently derived `(64,16)` arrays.

The public statement is `(context,n,m,V[0..m])`. The producer checks the actual openings `V_j=v_j B+γ_j B̃`, the integer bound and all counts before sampling proof masks. The validator obtains its statement independently of the proof. Generator fields are private; this entry fixes the default suite rather than taking an unbound arbitrary generator vector.

## 3. Range reduction

For `i=jn+b`:

```text
aL_i = bit_b(v_j)                 aR_i = aL_i - 1
A = <aL,G> + <aR,H> + α B̃
S = <sL,G> + <sR,H> + ρ B̃
Y_i = y^i                         d_i = z^(j+2) 2^b
l0_i = aL_i - z                   l1_i = sL_i
r0_i = Y_i (aR_i + z) + d_i      r1_i = Y_i sR_i
l(X) = l0 + X l1                 r(X) = r0 + X r1
t1 = <l1,r0> + <l0,r1>           t2 = <l1,r1>
T_1 = t1 B + τ1 B̃                T_2 = t2 B + τ2 B̃
tx = <l(x),r(x)>
τx = x τ1 + x² τ2 + Σ_j z^(j+2) γ_j
μ = α + x ρ
δ = (z-z²) Σ_(i=0)^(N-1) y^i - (Σ_(j=0)^(m-1) z^(j+3)) (Σ_(b=0)^(n-1) 2^b)
```

The native draw order is `α,ρ,sL[0..N],sR[0..N],τ1,τ2`; each draw calls `Scalar::random` with the caller's advancing RNG. The reduction uses actual bit vectors, not an assumed honest algebraic relation. The polynomial identity tested with a nonbit control is:

```text
t0 - δ - Σ_j z^(j+2) v_j
  = Σ_i y^i aL_i(aL_i-1)
    + Σ_j z^(j+2) (Σ_b 2^b aL_(jn+b) - v_j).
```

Equation **R**, checked as its own group identity:

```text
E_R = Σ_j z^(j+2) V_j + δ B + x T_1 + x² T_2 - tx B - τx B̃ = 0.
```

Finite power sums never divide by `y-1`; forced `y=1` is a valid native arithmetic control.

## 4. Actual parent and recursive IPA

After binding the three response scalars, derive `w`, set `Q=wB`, and define `H'_i=y^(-i) H_i`. The range validator constructs:

```text
P = A + x S - z Σ_i G_i + Σ_i (zY_i+d_i) H'_i - μ B̃ + tx Q.
```

The honest relation is `P=<l(x),G>+<r(x),H'>+<l(x),r(x)>Q`. The native child does not get to supply a replacement `P`, `Q`, generator set, or factors to the public range validator.

For each current `(a,b,G,H,P)` split into left and right halves:

```text
L = <aL,GR> + <bR,HL> + <aL,bR> Q
R = <aR,GL> + <bL,HR> + <aR,bL> Q
a' = u aL + u^-1 aR              b' = u^-1 bL + u bR
G' = u^-1 GL + u GR              H' = u HL + u^-1 HR
P' = P + u² L + u^-2 R
```

After exactly `k=log2(N)` rounds, the full terminal check is:

```text
E_I = P_final - a G_final - b H_final - ab Q = 0.
```

It is **not** `tx=ab`. The recursive cross terms change the inner product. The direct verifier recomputes all generator folds with point arithmetic and checks this exact terminal equation.

## 5. Flattening and linear pullback

For original index `i`, examine its bits from most significant to least significant in challenge production order:

```text
s_i = Π_r (u_r if bit_(k-1-r)(i)=1 else u_r^-1)
G_final = Σ_i s_i G_i
H_final = Σ_i s_i^-1 H'_i
E_I = P + Σ_r(u_r² L_r + u_r^-2 R_r)
      - a Σ_i s_i G_i - b Σ_i s_i^-1 H'_i - ab Q.
```

The code computes `s_i` and its inverse product explicitly, independently of upstream's inductive recurrence. The two flattened variants retain this **same equation**:

- Materialized: construct the `N` scaled points `H'_i`, use them in both parent and terminal contractions.
- Pulled back: use original `H_i` and move `y^(-i)` into the scalar weights for both contractions. No dense map is allocated.

The prover's pulled-back first round likewise moves `H` factors into the `L/R` and first folded-`H` coefficients; subsequent rounds use the actual folded bases. Same-tape byte equality covers all `L/R` messages and terminal values, rather than just the final decision.

This instantiates `contract(w,view(D,X)) = contract(Dᵀw,X)` for a diagonal view; the half-fold test also checks the nonsymmetric concatenated weights. It does not justify randomized batching, changing both operands of a bilinear expression without cross terms, moving guards/stops, or removing required resource charges.

## 6. Wire and transcript schedule

After the explicit application prefix, the exact schedule is:

| Action | Label | Bytes/value |
|---|---|---|
| Append | `dom-sep` | `rangeproof v1` |
| Append u64 | `n`, `m` | little-endian 8-byte values |
| Append each commitment | `V` | ordered raw 32-byte compressed points |
| Append | `A`, `S` | raw compressed points |
| Challenge | `y`, `z` | separate 64-byte squeezes, wide scalar reduction |
| Append | `T_1`, `T_2` | raw compressed points |
| Challenge | `x` | same reduction |
| Append | `t_x`, `t_x_blinding`, `e_blinding` | canonical raw 32-byte scalars |
| Challenge | `w` | same reduction |
| Append | `dom-sep` | `ipp v1` |
| Append u64 | `n` | total dimension `N`, not per-party `n` |
| Each round | `L`, `R`, then challenge `u` | two compressed points, then reduced challenge |

The native wrapper's u64 append uses `append_message(label,u64LE)`; the independent raw-Merlin test uses `append_u64` and compares every challenge's 64 bytes. Both upstream producer and verifier transcript end states also agree. The research fingerprint is squeezed from a cloned native transcript, after the protocol, and is not a protocol action.

Raw proof slots, each 32 bytes:

```text
A | S | T_1 | T_2 | tx | τx | μ | L0 | R0 | ... | L(k-1) | R(k-1) | a | b
```

Exact length and admitted count precede parser indexing. Points are decompressed and re-encoded for canonicality; proof points must be nonidentity. Scalars use `from_canonical_bytes`, never modular reduction of incoming scalars. Dropped/extra rounds, trailing bytes, wrong point encodings and noncanonical scalars fail closed.

Upstream **does not absorb terminal `a,b`**. Mutating them changes IPA acceptance but leaves the final transcript fingerprint unchanged; this is an explicit test. A parent continuation requiring complete-child binding must append canonical child evidence (or a specified commitment to it) before deriving subsequent challenges. That is an enclosing-protocol decision, not an implicit modification of this wire format.

## 7. Degenerate challenges and acceptance policy

Reject all `y,z,x,w,u=0` after one squeeze. `y,u` need inverses; `z=0` destroys the value coefficients; `w=0` removes the inner-product coefficient; `x=0` removes proof-mask response contributions and is already refused by upstream's party. Forced-zero hooks exist only under `cfg(test)`; they exercise both producer and validator. The policy helper is explicit and contains no retry loop. No forced-zero result is claimed to be an ordinary Merlin transcript.

The deterministic validator checks `(E_R=0) AND (E_I=0)`. Upstream samples a separate verifier scalar `c` and checks `E_I+cE_R=0` with variable-time MSM. These are different adversarial acceptance policies. The benchmark never labels their timing difference an exact compiler optimization or a proof of security.
