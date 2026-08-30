# Algebraic Interaction and Reduction: Candidate and Validation Record

> **Kind:** Temporary equal-resolution candidate comparison and constructive
> encoding record
> **State:** Complete at the assigned typed-encoding depth
> **Authority:** None. The objects below pressure the target and record the
> selected model. They are not admitted repository artifacts, theorem proofs,
> or implementation-support claims.
> **Basis:** [Source and Model Synthesis](source-and-model-synthesis.md)

## 1. Candidate comparison

Five candidates were compared against all four cases.

| Candidate | Sumcheck/GKR | Literal duplex transform | Packed Boolean GKR | Decision |
|---|---|---|---|---|
| A. Preserve the current Core and the current single FS construction unchanged | Direct flat encoding succeeds. | Fails runtime initialization, salt, codec, and squeeze semantics. | Succeeds with profile-local algebra/cost. | Rejected as the complete answer; preserves too narrow an FS support claim. |
| B. Add runtime child-protocol calls and a universal transition algebra | Can encode nesting, but duplicates flat execution authority and makes observationally equal elaborations semantically different. | Does not solve the FS envelope. | Adds no value. | Rejected. |
| C. Replace mandatory framing with an authored per-event absorb/skip map | Can emulate the paper. | Lets a construction omit protected statements or messages and author its own affirmative boundary. | Irrelevant. | Rejected. |
| D. Treat every transcript as the current canonical frames and seek theorem transport afterward | Retains strong framing. | Represents a different construction; the paper theorem cannot be attached directly. | Irrelevant. | Retained only as a distinct zkc profile, not as literal duplex correspondence. |
| E. Preserve the flat Core, retain strong framing as one closed profile, and add one closed ideal-overwrite-duplex profile with FS-local public material | Direct encoding remains unchanged. | Source-exact construction becomes representable without weakening the default. | Remains native; specialized algebra and cost stay in their existing owners. | Selected model request. |

The selected architecture is:

```text
                         one finite InteractiveCore
                         /                       \
                        /                         \
              Fresh challenge                 Fiat--Shamir
                interpretation                 interpretation
                                                    |
                                      one exact construction profile
                                      /                          \
                         StrongFramedV0          IdealOverwriteDuplexV0
                         no extra material       proof-carried public salt
```

The new arm is a conservative extension of the challenge interpretation. It
does not add an Interactive Core effect, a third party, nested execution, or a
general escape callback.

## 2. Decisions on the cross-cutting questions

### 2.1 A Core claim remains structural

A claim records a typed residual obligation and its lifecycle. `ApplyReduction`
records a structural transition; neither operation proves that the obligation
is true. A terminal disposition records that the protocol stops carrying the
claim. It does not mean “proved by this check.”

Therefore the Core must continue to admit unsound protocols. It would be a
category error for admission to require a theorem-level check-to-claim proof.
Relations binds the claim and reduction to exact mathematical instances and
transforms. An Analysis family selects the terminal check and proves, assumes,
or fails to establish that it grounds the final claim.

### 2.2 GKR execution remains flat

A fixed-depth GKR protocol has a complete finite occurrence and claim graph.
Its runtime meaning is that graph, not a stack of child interpreters. A source
template may be instantiated repeatedly during authoring, but all local
references are resolved before Core authentication.

If reusable authoring later proves important, the narrow addition is a checked
elaboration satellite:

```text
template instance + local bindings
  -> candidate flat fragment
  -> exact occurrence/value/claim/reduction map
  -> equality with the corresponding admitted Core slice
```

That result would retain provenance for authoring or theorem application. It
would not enter `CoreId`, execute a child, or make two identical flat bodies
different Protocols. The present cases do not require this satellite for
constructive expressibility, so its exact schema remains deferred.

### 2.3 Challenge reuse is occurrence reuse, not value equality

A Sumcheck challenge used by later local computations remains one challenge
occurrence. It needs `Shared` only when it is explicitly a required challenge
of multiple reductions. Two independent scalars sampled for one reduction are
two challenges, not one vector merely because an implementation samples them
together. Equal sampled values never merge coordinates.

### 2.4 Algebra and cost stay outside the common Core vocabulary

Field arithmetic, multilinear extension, Lagrange interpolation, Boolean gate
identities, and degree checks are exact portable algorithms or owner modules.
Packing, tables, cache layout, and vector instructions are Plan or realization
choices. Quantified field-size error and word-RAM cost are Analysis
propositions. No generic `RAMConsistency` or `Polynomial` Core effect was
justified.

## 3. Complete two-round Sumcheck inhabitant

This finite inhabitant is a typed abstract trace, not an executable fixture.
Use `F_17`, `B={0,1}`, and

```text
P(X_1,X_2) = 3 X_1 X_2 + 2 X_1 + 5 X_2 + 7.
```

The Boolean-hypercube sum is `H=11` in `F_17`.

### 3.1 Static objects

```text
Statement binding S:
  polynomial coefficients of P,
  dimension 2,
  individual degree bounds (1,1),
  summation domain (0,1),
  claimed sum H=11

Claims:
  C0 = R0(P,11)
  C1 = R1(P,[r1],t1), source ReductionOutput(R1,0)
  C2 = R2(P,[r1,r2],t2), source ReductionOutput(R2,0)

Reductions:
  R1: C0 + p1 + r1 -> C1
  R2: C1 + p2 + r2 -> C2
```

Each claim has its own exact relation-instance recipe. Each reduction meaning
names the previous claim, the polynomial publication, the challenge, and the
transform deriving the next prefix and target.

There is no setup, Oracle, PCS, or private verifier state. The finite Core has
two prover messages, two scalar challenges, three checks, two reductions,
three guarded Reject paths, and one Accept terminal. Ill-typed or absent
messages are strategy failures; unavailable Fresh coins are operational
noncompletion; strong-framed sampling exhaustion is an interpretation failure.

### 3.2 Occurrence trace

| Ordinal | Effect | Exact value or law | Claim consequence |
|---:|---|---|---|
| 0 | `ProverMessage(p1)` | `p1(X)=7X+2`, coefficients `(2,7)` | none |
| 1 | `InvokeCheck(k1)` | degree at most 1 and `p1(0)+p1(1)=2+9=11` | false selects Reject before any challenge |
| 2 | guarded `ReachTerminal(Reject)` | active iff `not k1` | discharges `C0` on the rejected path |
| 3 | `Challenge(r1)` | fresh value `4` after `p1` | none |
| 4 | `ApplyReduction(R1)` | `t1=p1(4)=13` | consumes `C0`, creates `C1` |
| 5 | `ProverMessage(p2)` | `p2(X)=15`, coefficients `(15,0)` | none |
| 6 | `InvokeCheck(k2)` | degree at most 1 and `p2(0)+p2(1)=15+15=13` | false selects Reject before `r2` |
| 7 | guarded `ReachTerminal(Reject)` | active iff `not k2` | discharges `C1` on the rejected path |
| 8 | `Challenge(r2)` | fresh value `6` after `p2` | none |
| 9 | `ApplyReduction(R2)` | `t2=p2(6)=15` | consumes `C1`, creates `C2` |
| 10 | `InvokeCheck(k_final)` | `P(4,6)=15=t2` | exact standalone grounding check |
| 11 | guarded `ReachTerminal(Reject)` | active iff `not k_final` | discharges `C2` on the rejected path |
| 12 | `ReachTerminal(Accept)` | requires `k1,k2,k_final`; consumes or discharges `C2` as declared | accepting completion |

`R1.required_publications=[(0,Some(r1))]` and
`R2.required_publications=[(5,Some(r2))]`. Each reduction has exactly its one
required challenge. A causal prover strategy producing `p2` sees `r1` but not
`r2`.

The Fresh Protocol samples the two values. The current strong-framed FS
Protocol absorbs `S`, then `p1` before `r1`, and cumulatively `p2` before `r2`.
That establishes structural correspondence only, not the classical theorem or
a Fresh-to-FS theorem.

### 3.3 Sumcheck mutations

| Mutation | First intended boundary |
|---|---|
| publish `p_i` after `r_i` | Core reduction ordering / exact prefix |
| omit `p_i` from required publications | reduction admission or FS required influence |
| use a degree-2 payload under a degree-1 representation | message/algorithm typing or local check |
| continue to `r_i` after a false local check | occurrence/guard correspondence with the source |
| derive `t_i` from another polynomial or point | Relations reduction grounding |
| expose a future challenge to the prover | causal strategy generation |
| replace the final check with an unrelated true predicate | source correspondence or Analysis applicability, not Core well-formedness |
| treat a replayed anticipatory trace as causal | causal-authority boundary |
| omit `P` or `H` from the Statement | claim recipe and FS source correspondence |
| use correlated/nonuniform coins while claiming the classical bound | Analysis applicability |

## 4. Complete flat GKR object graph

Choose a public finite layered arithmetic circuit with output layer `0`, input
layer `d`, fixed widths, exact wiring algorithms, public input `x`, and a
claimed output table `D`. The selected supplied-claim front-end binds `D` once
as a Statement value before execution; it is not also a prover publication.
The general object graph is parameterized by finite widths, and Section 4.4
closes one concrete finite instance.

### 4.1 Output compression

```text
Initial statement claim C_statement(C,x,D)
  -> shape/canonicality check of the bound D
  -> fresh output point a_0
  -> reduction R_output
  -> C_0(a_0, ~D(a_0)) : ~W_0(a_0)=~D(a_0)
```

The output table is fixed before `a_0`. `C_0` is a reduction output, never an
event-created initial claim.

### 4.2 Layer `i`

For every one of the finite Sumcheck variables in the layer identity:

```text
C_{i,j-1}
  -> publish h_{i,j}
  -> check exact degree and recurrence
  -> Reject on false
  -> challenge rho_{i,j}
  -> reduction S_{i,j}
  -> C_{i,j}
```

The final partial-sum claim and the two child evaluations then feed:

```text
publish q_i(t)
  -> check degree, q_i(0), q_i(1), and final GKR kernel
  -> Reject on false
  -> fresh tau_i
  -> line reduction L_i
  -> C_{i+1}(a_{i+1},v_{i+1})
```

After the last layer, an exact public-input MLE algorithm checks
`~W_d(a_d)=v_d`; the terminal selects that check and the final claim meaning.
All wiring evaluation comes from the declared public algorithm or admitted
preprocessing source.

This is a complete flat Core. The per-layer and per-round names above are
authoring notation. The authenticated semantic coordinates are the resulting
occurrence, value, claim, reduction, check, and algorithm references.

### 4.3 GKR mutations

| Mutation | First intended boundary |
|---|---|
| omit `D` from the Statement or sample before its binding is initialized | Statement formation, Core ordering, or FS influence |
| round challenge before `h_{i,j}` | Core ordering / causal strategy |
| line challenge before `q_i` | Core ordering / reduction publication law |
| incorrect recurrence, degree, endpoint, or final-kernel check | source verifier check |
| output claim uses a wrong layer, point, or value | Relations recipe/transform binding |
| implicit host wiring evaluator | missing exact dependency/capability |
| original grid-extension GKR labeled as the modern Boolean-MLE Core | source correspondence and Core identity |
| child template handle retained at runtime | Core formation/admission |
| local checks promoted to whole-protocol soundness | Analysis authority |

No mutation required a new Core constructor.

### 4.4 Closed finite GKR instance

The parameterized graph above is witnessed by this one-layer arithmetic
circuit over `F_17`:

```text
public input layer W_1 = (2,3)
output gate 0 = W_1(0) + W_1(1) = 5
output gate 1 = W_1(0) * W_1(1) = 6
Statement output table D = (5,6)
W~_1(z) = 2 + z
D~(z) = 5 + z
```

There is no setup. The Statement binds the field, circuit and wiring
algorithms, `x=(2,3)`, `D=(5,6)`, and all degree bounds. Three prover-message
types carry respectively two degree-at-most-two coefficient vectors and one
degree-at-most-one vector. Four challenge occurrences have type `F_17`.

For output point `a_0=4`, the initial reduction obtains
`C_0(4,9)`. With gate-label variables `b,c`, the exact layer kernel is

```text
G(b,c) = (1-b)c(4 + 5b + 5c + 4bc).
```

The complete honest interaction is:

| Phase | Message, check, challenge, and claim transition |
|---|---|
| output | check the bound table shape; sample `a_0=4`; reduce `C_statement` to `C_0(4,9)` |
| first Sumcheck round | publish `p_1(B)=9-9B^2`; check degree and `p_1(0)+p_1(1)=9`; sample `rho_1=2`; reduce to target `t_1=7` |
| second Sumcheck round | publish `p_2(C)=3C+4C^2`; check degree and `p_2(0)+p_2(1)=7`; sample `rho_2=3`; reduce to `G(2,3)=t_2=11` |
| line reduction | publish `q(T)=4+T`; check degree, `q(0)=4`, `q(1)=5`, and the final layer kernel; sample `tau=6`; reduce to `C_1(8,10)` |
| input | directly check `W~_1(8)=10`; reach Accept and discharge the final claim |

Every false check has its own guarded Reject terminal before the next
challenge. An ill-typed message is an illegal strategy move, missing Fresh
randomness is operational noncompletion, and exhausted strong-framed sampling
is an interpretation failure rather than Core rejection. The finite Core has
three prover messages, four challenges, five checks, four reductions, one
Accept terminal, and five guarded Reject paths. Its exact wiring evaluator is
a declared public algorithm, not ambient host computation.

## 5. Packed Boolean GKR encoding

The packed variant modifies the declared algebra used by the layer, not the
interaction category. It is `Native`: its hybrid interpolation and Boolean
gate computations use the existing typed algorithm/module dependency
mechanism, so no missing owner-local semantic construct justifies a separate
`ProfileOrModule` classification.

One closed finite object graph fixes `F_17`, `B=2`, interpolation points
`(0,1)`, depth two, and one Boolean gate-index bit at every layer. It binds a
public two-copy circuit, public input, claimed output table, exact hybrid
extension algorithms, wiring algorithms, Booleanity relation, and degree
bounds as Statement/PublicParameter values; it has no setup and no PCS. The
authenticated Core directly enumerates the following schedule rather than
retaining a GKR template handle:

```text
bound output table
  -> binary-output and shape check
  -> joint output-evaluation challenge (p^(0), b^(0))
  -> output-compression reduction to the first layer claim
  -> layer 0 optimized Sumcheck:
       f_0(b) message, degree <= 3
       domain-sum check, then challenge b^(1)
       h_0,x message/check, then challenge x^(1)
       h_0,y message/check, then challenge y^(1)
       two next-layer evaluation values, then exact kernel check
  -> joint challenge (alpha^(1), beta^(1)) after both values are fixed
  -> layer 1 optimized Sumcheck over their declared linear combination:
       f_1(b) message, degree <= 3
       domain-sum check, then challenge b^(2)
       h_1,x message/check, then challenge x^(2)
       h_1,y message/check, then challenge y^(2)
       two input-layer evaluation values, then exact kernel check
  -> two direct public-input-extension checks
  -> Accept
```

Every message and scalar pair has an exact finite `F_17` value type. Each
failed binaryity, degree, recurrence, kernel, or final-input check reaches a
guarded Reject before any dependent challenge or reduction. The honest prover
strategy reads only the preceding prefix. This finite object graph accounts
for the novel univariate round, the ordinary within-copy rounds, later-layer
linear combination, and the final input boundary without importing the
paper's separate commitment scheme.

Its claim graph is also finite: `R_output` produces the first layer claim;
the `b`, `x`, and `y` Sumcheck reductions refine it; the checked layer kernel
produces two next-layer evaluation claims; and a reduction parameterized by
the joint `(alpha,beta)` occurrence consumes those two claims into the next
layer's combined claim. The second layer repeats that explicit chain, and its
two residual input claims are discharged only by the two final checks.

Treating each evaluation pair as one product-typed message, the Core has eight
prover messages carrying twenty-four field elements: two four-coefficient `f_i`
polynomials, four three-coefficient within-copy polynomials, and four terminal
evaluation values. It has two joint `F_17^2` challenge occurrences, six scalar
challenge occurrences, eleven verifier checks, eleven guarded Reject paths,
and one Accept terminal. These are structural resource counts; the paper's
asymptotic word-RAM cost remains an Analysis proposition.

For each layer it adds one first Sumcheck round:

```text
publish f_i(b), degree exactly bounded by 3(B-1)
  -> check sum over the declared B-point interpolation domain
  -> fresh b_i
  -> continue the within-copy multilinear Sumcheck
```

After two next-layer evaluation values are fixed, the verifier samples the
source coefficients used to combine those values and the matching wiring
predicates. The same challenge occurrence may be read by several equations
within one reduction; that is ordinary dataflow, not multiple reduction-role
consumers.

The profile includes exact `B`, field, interpolation points, Boolean AND/XOR
identities, degree bounds, and input-Booleanity relation. A packed-word Plan
and a naïve scalar Plan intentionally share the Core and Protocol identities.

Required negatives include:

- the `b` challenge before `f_i`;
- a wrong interpolation domain or degree;
- combination challenges before both values are fixed;
- a circuit without the declared identical-subcircuit decomposition;
- the concrete counterexample `AND(a,0)=0` for non-binary `a`;
- a quantitative cost result from an unresolved asymptotic `omega(1)` factor;
- any RAM-consistency, zero-knowledge, strong-FS, or complete-SNARK claim from
  the paper alone.

The paper's separate binary-polynomial commitment stops at a typed downstream
dependency. It does not enter this GKR Core or receive security authority from
this encoding.

## 6. Ideal-overwrite-duplex construction request

The target extension is a closed construction arm, not a caller-authored
event map:

```text
TranscriptConstruction =
    StrongFramedV0(StrongFramedConstruction)
  | IdealOverwriteDuplexV0(IdealOverwriteDuplexConstruction)

IdealOverwriteDuplexConstruction = {
  core_id,
  exact source-profile declaration,
  alphabet and bounded symbol-string types,
  rate and capacity,
  runtime-instance codec,
  Start_h algorithm and contract,
  overwrite-mode Absorb_p algorithm and contract,
  Squeeze_p and state-advance algorithms and contracts,
  total map from prover-message occurrences to
    injective codecs and exact encoded lengths,
  total map from challenge occurrences to
    exact squeeze lengths and total decoders,
  one construction-public-input declaration for the salt,
  salt length delta,
  exact initialization and occurrence schedule,
  semantic transition and resource bounds
}
```

The construction-public input is semantically just proof-supplied public
material. Its value is not stored in construction identity, and verifier
semantics must not claim it was sampled uniformly. Honest generation obtains
it from a Plan/private-randomness capability; a zero-knowledge Analysis profile
separately requires and validates the distribution premise. Verification and
replay receive the same value from the proof/interface and retain it in the FS
interpretation record.

The exact initialization is:

```text
instance_bytes = instance_codec(ordered Statement values)
state_0 = Start_h(instance_bytes)
state_1 = Absorb_p(state_0, salt)
```

Each active prover-message occurrence has exactly one profile-owned codec and
absorb action. Each Challenge has a one-shot squeeze and total decoder. The
closed profile fixes the final-message behavior and proves total coverage of
the source round schedule. It has no optional skip bit. The paper profile has
no zkc namespace, retry, header, label, or length frame.

`StrongFramedV0` retains all current statement/message coverage, canonical
typed framing, namespaces, and retry laws. The two profiles necessarily have
different construction and Protocol IDs while they may refer to the same
Core. Neither theorem transfers between them without an explicit Analysis
applicability result.

### 6.1 Duplex transition falsifiers

The construction profile must distinguish at least:

1. partial squeeze followed by overwrite absorption;
2. empty absorption after a partial squeeze;
3. a zero-length squeeze;
4. two consecutive squeezes versus one concatenated squeeze;
5. lazy versus eager permutation at the filled rate boundary;
6. overwrite mode versus XOR mode;
7. missing, wrong-length, or late salt;
8. noninjective message codec or non-total challenge decoder;
9. namespace or typed-frame substitution under a literal-source claim;
10. omitted adversarial inverse-permutation access in theorem applicability;
11. unpriced codec bias or capacity loss; and
12. a classical theorem relabeled as QROM or UC.

These are source-correspondence and theorem-applicability distinctions. They do
not weaken the existing strong-framed admission rules.

## 7. Why no executable promotion was needed

The assigned evidence depth is a complete typed abstract encoding for the
three representable cases and a decisive typed obstruction for the duplex
case. The candidate comparison is already decisive:

- Sumcheck and GKR inhabit the current flat Core without an opaque operation;
- the packed GKR delta is visibly profile/Plan/Analysis-local;
- the duplex construction fails on explicit subject fields and lifecycle
  inputs, not on an uncertain runtime outcome; and
- the selected duplex extension has precise positive and negative boundaries.

An executable package would be useful only after the new duplex profile is
specified, or if a later checked-elaboration design leaves two competing map
laws indistinguishable. Promoting now would test a temporary host model and
could self-author the missing semantics. The cases therefore close at typed
constructive depth without claiming execution evidence.
