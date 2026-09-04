# Imported Verifiers and Recursive Proof Composition

> **Portfolio case:** Imported verifier and recursive proof verification
> **Target depth:** strict T2 constructive encoding
> **Achieved depth:** T1 source-grounded architecture mapping; strict T2 is
> blocked on the concrete circuit/model, setup-instance, codec, Fresh-OIR, and
> numeric resource profiles listed in Section 15
> **Result:** `ProfileOrModule`; recursive verification is a finite Relations
> predicate, while exact circuit semantics and Fresh endpoint projection need
> owner-local module/profile definitions
> **Authority:** Source-grounded temporary research, not an implementation,
> recursive-composition theorem, or security claim

## 1. Source lock and selection

The selected finite member comes from the cycle-based construction of
Ben-Sasson, Chiesa, Tromer, and Virza,
[Scalable Zero Knowledge via Cycles of Elliptic Curves](https://eprint.iacr.org/2014/595),
archive revision `20200618:063504`, PDF SHA-256
`e5e32ca3713b1747681f9f194359023a7c0ec842f293b84793fa924c0faad62e`.
The PDF identifies itself as the extended version dated `2016-09-18`. The
record uses the complete two-circuit PCD construction in Sections 4--5 and
Figure 2, not only the introductory recursion sketch.

The recursive-composition and depth obligations are checked against Bitansky,
Canetti, Chiesa, and Tromer,
[Recursive Composition and Bootstrapping for SNARKs and Proof-Carrying Data](https://eprint.iacr.org/2012/095),
archive revision `20121228:123450`, PDF SHA-256
`c29188804166b6f2d1ec2753b119e29e0b0af942e6bff8971b0e8d4c911e56ed`.
This source is necessary because the cycle paper explicitly routes the formal
recursive security argument to the earlier work. The constructive record below
does not reproduce that proof.

One non-cycle architecture falsifier is Chiesa, Ojha, and Spooner,
[Fractal: Post-Quantum and Transparent Recursive Proofs from Holography](https://eprint.iacr.org/2019/1076),
archive revision `20200715:141732`, PDF SHA-256
`d152c8d0d625a1ffb7cd3ad86ccc410b4dfa8f77aea82309dde1e8824236fb42`.
Fractal replaces the pairing-friendly curve cycle with a transparent
preprocessing SNARK and a finite verifier constraint system. Its Sections
2.1, 2.5, and 11 are used to test whether the target architecture accidentally
depends on curve-cycle details.

The adjacent folding records cover Nova, HyperNova, CycleFold, and ProtoStar.
They are not silently treated as alternate recursive-SNARK sources here.
Their accumulation-plus-decider organization is a contrast: a decider checks
an accumulated relation at a boundary; it is not evidence for a universal
runtime child-verifier operation.

## 2. Decision

The source-level recursive step has three different objects:

```text
inner proof value
  consumed as a private input of an outer relation

finite inner-verifier semantics
  embedded in that outer relation's canonical computation graph

outer proof value
  emitted by the outer proof system and checked by its ordinary verifier Core
```

They must not be merged. In particular, the recursive step is not:

```text
outer Core --runtime call--> child Core
```

It is:

```text
outer RelationDefinition
  = local compliance predicate
  + exact finite inner-verifier computation

outer ProverPlan
  consumes one witness occurrence containing the inner proof value
  and constructs an outer proof

outer Core
  observes only the outer Statement, outer proof, outer verifier check,
  and outer verdict
```

This distinction survives both the BCTV curve-cycle construction and Fractal's
transparent non-cycle construction. Their algebra, setup, proof system, and
security assumptions differ, but both put prior-proof verification inside the
new relation rather than granting a verifier circuit authority to execute a
child Protocol.

The selected primary classification is `ProfileOrModule`, for two bounded
reasons:

1. Relations needs one exact finite arithmetic-circuit definition-language
   module and evaluator profile that can carry the imported verifier graph
   without an opaque callback. The existing Relations extension boundary can
   host this; no new top-level subject is required.
2. The current bounded OIR endpoint profile rejects every Fresh Protocol.
   These zero-challenge preprocessing-SNARK verifiers therefore need the
   already anticipated owner-local Fresh endpoint sibling before exact OIR
   projection is available.

Neither point requires an accumulator root, recursive-proof root, runtime
child-Core authority, cyclic semantic identity, or general recursive
evaluator.

## 3. Source distinctions that the model must preserve

### 3.1 Proof recursion is not semantic recursion

A PCD prover repeatedly constructs proof *values*. The same finite proof
systems, verifier circuits, relation definitions, Protocols, and Plans are
reused at every step. No semantic subject contains the next proof value in its
own identity preimage.

The runtime value recurrence is:

```text
(z_(i-1), pi_(i-1))
  -> satisfy one fixed recursive relation for z_i
  -> construct pi_i
```

The semantic dependency graph remains a finite DAG formed before any `pi_i`
exists. Calling this use of a fixed relation "recursive" must not authorize a
recursive identity constructor.

### 3.2 A valid proof value need not be the same host occurrence

The source relation checks that semantic prior proof `pi_in`, lowered to the
exact `pi_in_c4` circuit representation, verifies for `z_in`. It does not demand
that the exact in-memory object be the output occurrence of the immediately
preceding host invocation. A copied, stored, or independently obtained proof
with the same semantic value is source-valid if it passes the exact verifier
for the exact prior statement.

The target still keeps occurrences distinct:

- the prior Protocol publication is one run occurrence;
- the outer relation's private `pi_in_c4` is a fresh witness occurrence; and
- the Plan private-material coordinate is another owner-local occurrence.

The checked relation is verifier validity and typed value agreement, not
physical-object identity. A concrete same-process construction may additionally
use the Plan-owned one-use causal handoff defined by this package, but that is
an optional construction proposition rather than a premise of source validity.
Serialized or persisted operational provenance remains a separate Realization
record and is not inserted into the recursive relation or a security theorem.

### 3.3 Proof values are not proof bytes

The BCTV recursive circuits consume algebraic proof tuples. In the
source-reported implementation a proof has the tuple roles

```text
(pi_A, pi_A_prime, pi_B, pi_B_prime,
 pi_C, pi_C_prime, pi_K, pi_H)
```

with seven elements in the applicable `G1` and one in the applicable `G2`.
The selected implementation reports `337` bytes for `Proof4` and `374` bytes
for `Proof6`. Those measurements do not by themselves define either byte
codec. Alpha-side and beta-side proof types remain distinct because their
groups differ, not merely because the reported lengths differ.

Interface/OIR owns the external encoding, canonical group decoding, curve and
subgroup checks, tuple order, and failure before semantic execution. The Plan
private-supplier path lowers the decoded canonical tuple through the exact
`EncodeProof6ForCircuit4` algorithm; the outer relation consumes that circuit
representation. A different relation that intends to prove correct parsing of
raw bytes must put the byte type and decoder computation in its own predicate;
parsing cannot be smuggled into a Plan supplier.

### 3.4 Accumulation, decision, and recursive verification differ

An accumulation or folding step may reduce several claims to one accumulator
claim without proving both source claims at that moment. A decider later
discharges the accumulated relation. BCTV-style recursive composition instead
places an exact verifier for a prior proof in a new NP relation and proves that
relation with another proof system.

Both patterns can appear in one complete system. That does not make
`Accumulator`, `ImportedVerifier`, `RecursiveProof`, and `Decider` aliases.
The target retains their owner-local relation and proof-system structures.

## 4. Selected finite member schema

### 4.1 Fixed source profile

The source instantiates a PCD-friendly two-cycle `(E4,E6)` of MNT curves. The
selected profile fixes:

```text
F4 = scalar field of E4 = base field used by the E6 verifier
F6 = scalar field of E6 = base field used by the E4 verifier

SNARK4 = required exact preprocessing-SNARK profile coordinate (G4,P4,V4)
SNARK6 = required exact preprocessing-SNARK profile coordinate (G6,P6,V6)

Proof4 = Record {
  A:G1_4, A_prime:G1_4, B:G2_4, B_prime:G1_4,
  C:G1_4, C_prime:G1_4, K:G1_4, H:G1_4
}

Proof6 = the corresponding record over the E6 proof groups

PCDVerificationKey = Record {
  vk4: VerificationKey4,
  vk6: VerificationKey6
}

H4       = the source subset-sum hash with output dimension d_H,4 = 1
X4       = FixedSeq<F4,1>
X6       = FixedSeq<F6,2>
X6BitsInF4 = FixedSeq<BitCarrier<F4>,2*ceil(log2(r6))>
X4BitsInF6 = FixedSeq<BitCarrier<F6>,ceil(log2(r4))>

S4_to_6_host = the source host conversion X4 -> X6
CS4_to_6     = the source F4-circuit conversion X4 -> X6BitsInF4
CS4_from_6   = the source F6-circuit reverse conversion X6 -> X4BitsInF6

Proof6Circuit4 = exact F4-circuit representation consumed by CV6
Proof4Circuit6 = exact F6-circuit representation consumed by CV4_online
EncodeProof6ForCircuit4 : Proof6 -> Proof6Circuit4
EncodeProof4ForCircuit6 : Proof4 -> Proof4Circuit6

AlphaCircuitAdvice4 = exact finite Cbits, conversion, CV6 division, and
                      verifier-circuit advice record type over F4
BetaCircuitAdvice6  = exact finite reverse-conversion, CV4_online division,
                      and verifier-circuit advice record type over F6

bits4_prover = the source's deterministic lexicographically first field
               representation used by the outer prover/verifier algorithm
Cbits4        = the source circuit relation accepting either permitted
                wraparound representation described in Section 4.2
```

The curve equations, field moduli, abstract verifier equations, proof tuple
roles, and representation directions are fixed by the source. Each concrete
relation body additionally binds one exact source-profile subset-sum matrix
`M4` before its identity is formed; the paper's matrix distribution is an
Analysis premise, not a caller-selected ambient hash. The PDF does not close
the complete circuit payload, advice carriers, portable `G/P/V` algorithms,
or byte codec needed by the target, so these names are required profile
coordinates rather than already admitted modules. This is the principal T2
blocker; no host library call may fill it implicitly.

For finite dimensions choose:

```text
message arity        s     = 1
message length       n_msg = 1 element of F4
local-data length    n_loc = 1 element of F4
predicate output     l     = 1 element of F4
```

and the two-gate compliance predicate under Appendix A.1's bilinear-gate
model:

```text
t0  = (1 - b_base) * z_in
out = (z - z_loc - t0) * 1

Pi_step(z,z_loc,z_in,b_base) = out
```

Thus a base node requires `z=z_loc`; a recursive node requires
`z=z_loc+z_in`. The PCD circuit separately checks that `b_base` is Boolean.
This is a finite source-level schema member of the source's arbitrary fixed
arithmetic-compliance-predicate interface. It is selected to isolate recursive
verification rather than to model the paper's RAM application.

The source fixes `n4=1` and `n6=2` for this hash/output representation. Applying
its Lemma 5.1 to `s=1`, `n_msg=1`, and `|Pi_step|=2` gives:

```text
|C_pcd,4| = 2 + 89,412 + 2*298 + 11,925 = 101,935 gates
|C_pcd,6| = 32,027 gates
```

These are finite source-profile bounds, not compiler measurements in this
repository.

### 4.2 Required alpha relation shape

The alpha circuit is the relation that actually imports the prior verifier:

```text
public instance:
  x4 : F4

private witness:
  vk6          : VerificationKey6
  z            : F4
  z_loc        : F4
  z_in         : F4
  b_base       : Bool
  pi_in_c4     : Proof6Circuit4
  b_res        : Bool
  alpha_advice : AlphaCircuitAdvice4

constraints:
  vk6_bits,z_bits,z_in_bits are the Cbits4 witnesses in alpha_advice
  Cbits4 accepts (vk6,vk6_bits), (z,z_bits), and (z_in,z_in_bits)
  x4 = H4(vk6_bits || z_bits)
  Pi_step(z,z_loc,z_in,b_base) = 0
  b_base in {0,1}
  b_res in {0,1}

  x_in,4 = H4(vk6_bits || z_in_bits)
  x_in6_bits_in_F4 = CS4_to_6(x_in,4,alpha_advice)
  CV6(vk6,x_in6_bits_in_F4,pi_in_c4,alpha_advice) = b_res
  (1-b_base)(1-b_res) = 0

meaning:
  if b_base = 0, b_res must be 1
  if b_base = 1, CV6 is still evaluated consistently but acceptance is not
                 required
```

`CV6` and all of its division guesses and auxiliary checks are part of the
finite constraint system. Only the requirement that its output equal one is
gated by `b_base`; moving verifier evaluation itself under a host conditional
would weaken the exact source circuit. An evaluator callback that merely
returns a Boolean is not a T2 encoding.

The fixed circuit witness still has proof-coordinate wires on the base branch.
The typed `b_base` value is the only branch selector. The source permits any
correctly sized assignment in those unused proof slots; it does not select one
canonical padding value. A future target profile must choose a formed
`Proof6Circuit4` padding assignment, while each occurrence supplies advice and
`b_res` consistent with its actual `vk6`, `z`, `z_in`, and proof wires. The
relation still checks that those wires produce the declared `b_res`, but
assigns no prior-proof-*acceptance* meaning to that result. There is no
proof-byte sentinel and no inference that an all-zero string denotes absence.
A tagged authoring API may distinguish `Base` from `Recursive(Proof6)`, but
its elaboration to the fixed circuit witness must be total and must not
redefine the relation.

### 4.3 Required beta converter relation shape

The beta circuit converts an alpha proof back to the externally retained proof
system:

```text
public instance:
  x6 : FixedSeq<F6,2>

private witness:
  pi4_c6     : Proof4Circuit6
  beta_advice: BetaCircuitAdvice6

relation constant:
  pvk4 : exact processed verification key generated for C_pcd,4

constraints:
  x4_bits_in_F6 = CS4_from_6(x6,beta_advice)
  CV4_online(pvk4,x4_bits_in_F6,pi4_c6,beta_advice) = 1
```

The beta circuit does not re-evaluate `Pi_step`. It verifies the alpha proof.
`x4_bits_in_F6` is a vector of bit carriers in the beta circuit field, not an
`F4` semantic value and not evidence that `CS4_from_6` is a total bijection on
all field vectors. Collapsing the two circuits into one undifferentiated
"recursive verifier" would erase both the representation conversion and the
source's setup-cycle breaker.

### 4.4 Source two-stage proof construction

For one recursive node:

```text
x4 := H4(bits4_prover(vk6) || bits4_prover(z))

pi_in_c4 :=
  if b_base=0 then EncodeProof6ForCircuit4(pi_in)
  else formed base padding selected by the future exact target profile

pi4 := P4(
  pk4,
  x4,
  witness=(vk6,z,z_loc,z_in,b_base,pi_in_c4,b_res,alpha_advice))

x6 := S4_to_6_host(x4)
pi4_c6 := EncodeProof4ForCircuit6(pi4)

pi6 := P6(
  pk6,
  x6,
  witness=(pi4_c6,beta_advice))

output pi6
```

The first proof establishes satisfaction of the alpha relation. The second
establishes satisfaction of the converter relation. The public PCD verifier
checks only:

```text
x4 := H4(bits4_prover(vk6) || bits4_prover(z))
x6 := S4_to_6_host(x4)
V6(vk6,x6,pi6) = 1
```

The two proof-construction invocations are not two messages in one interactive
Core. The target represents them as two independently admissible
zero-challenge proof Protocols plus an application-level construction order.

## 5. Relations representation

### 5.1 Required exact definition-language module

The owner-local profile required for T2 must define one finite
arithmetic-circuit payload with:

- exact field and group value types;
- dense typed input and output ordinals;
- a finite acyclic graph of elementary field operations in which Booleanity,
  bit decomposition, curve arithmetic, pairings, hashing, and representation
  conversions are fully expanded rather than ambient callbacks;
- exact constant tables, including `pvk4` only in the beta relation;
- total output constraints; and
- a deterministic evaluator contract with an explicit gate, byte, depth, and
  intermediate-value envelope.

That module would inhabit the existing `relations.definition-language` and
`relations.satisfaction-evaluator` declaration contracts. The complete alpha
or beta circuit is the canonical `RelationDefinition.payload`; it is not a new
`ImportedVerifierId` and does not gain separate verdict authority. This record
fixes the required shape but does not claim that the complete payload and
definition/model certificate already exist.

The corresponding Interfaces are:

```text
RI4:
  PublicInstance = [x4:F4]
  PrivateWitness = [vk6,z,z_loc,z_in,b_base,pi_in_c4,b_res,alpha_advice]
  OracleStatement = []
  PhaseInput = []

RI6:
  PublicInstance = [x6:FixedSeq<F6,2>]
  PrivateWitness = [pi4_c6:Proof4Circuit6,beta_advice:BetaCircuitAdvice6]
  OracleStatement = []
  PhaseInput = []
```

No proof byte string, proving key, setup trapdoor, host callback, child Core
handle, OIR object, or checked theorem result belongs in either relation
definition.

### 5.2 Occurrence-local satisfaction

Each recursive node creates fresh owner-local relation occurrences:

```text
RX4_i = RelationInstance(RI4, x4_i)
RW4_i = PrivateWitnessAssignment(
  RX4_i,
  vk6_i,z_i,z_loc_i,z_in_i,b_base_i,pi_in_c4_i,b_res_i,alpha_advice_i)

RX6_i = RelationInstance(RI6, x6_i)
RW6_i = PrivateWitnessAssignment(RX6_i, pi4_c6_i,beta_advice_i)
```

Once the required module/profile exists,
`CheckRelationSatisfaction(RX4_i,RW4_i)` evaluates the complete alpha graph and
`CheckRelationSatisfaction(RX6_i,RW6_i)` evaluates the converter graph. A
Negative result means the exact supplied occurrence does not satisfy that
relation. It says nothing about whether another witness exists and is not a
Protocol verdict.

The transition `x6_i=S4_to_6_host(x4_i)` is an exact total value derivation. The
PCD message relation `z_in -> z` is inside `Pi_step`; it is not inferred from
proof acceptance. For multiple nodes, `z_i` and `z_(i+1)` remain distinct
occurrences even when their values coincide.

### 5.3 Correspondence to outer proof Protocols

For each raw SNARK side, an ordinary `ProtocolRelationBinding` maps the sole
Statement binding to the corresponding public relation instance. An ordinary
`PlanWitnessBinding` maps every relation private-witness occurrence to its
typed Plan Witness surface coordinate. The selected conservative Plan form
declares the complete circuit witness, including advice, as ingress; a later
exact Plan may instead construct some coordinates and expose them through
typed derived-witness exports.

The bindings establish type, occurrence, and structural coverage only. They do
not establish:

- satisfaction of the alpha or beta relation;
- correctness of either SNARK prover;
- soundness or knowledge of either verifier;
- setup origin or key/relation specialization; or
- recursive-composition security.

The Relations-owned grounding equations required for the selected schema are
shown schematically below. Strict T2 must lower each source to the current
literal run-slot grammar (`BindingValue(binding_ref)`, `OccurrenceOutput`, and
the applicable typed selector); the shorthand is not a new selector grammar.

| Equation | Sources | Required equality | Meaning |
|---|---|---|---|
| `GE4Statement` | `ProtocolValue(Protocol4,Statement(x4))`, `InstancePublic(RI4,x4)` | same exact `F4` value | the alpha verifier run and alpha relation instance concern the same public instance |
| `GE6Statement` | `ProtocolValue(Protocol6,Statement(x6))`, `InstancePublic(RI6,x6)` | same exact `FixedSeq<F6,2>` value | the beta verifier run and beta relation instance concern the same public instance |
| `GEPCDToBeta` | `ProtocolValue(ProtocolPCD,Statement(z))`, the `vk6` projection of `ProtocolValue(ProtocolPCD,PublicParameter(pcd_vk))`, steps `bits4_prover`, `H4`, and `S4_to_6_host`, `InstancePublic(RI6,x6)` | derived `X6` equals the exact beta public-instance value | the source PCD endpoint derives, rather than accepts, the raw beta-SNARK instance |
| `GEPCDToAlphaWitness` | `ProtocolValue(ProtocolPCD,Statement(z))`, the `vk6` projection of `ProtocolValue(ProtocolPCD,PublicParameter(pcd_vk))`, `WitnessValue(RI4,z)`, `WitnessValue(RI4,vk6)` | each public endpoint value equals its distinct alpha-witness occurrence | one concrete honest construction uses the public message/key in the alpha witness without making those witness occurrences public relation inputs |
| `GE4To6Witness` | `ProtocolValue(Protocol4,Message(pi4))`, step `EncodeProof4ForCircuit6`, `WitnessValue(RI6,pi4_c6)` | encoded result equals the exact `Proof4Circuit6` witness value | one concrete two-stage construction feeds the alpha proof into the beta circuit representation |
| `GE6ToNext4Witness` | `ProtocolValue(Protocol6,Message(pi6))`, step `EncodeProof6ForCircuit4`, `WitnessValue(RI4,pi_in_c4)` | encoded result equals the exact `Proof6Circuit4` witness value | optional value grounding for a later recursive witness; a direct causal claim additionally requires the Plan-owned handoff capability and private join |

The first two equations are the public run/relation grounding required by the
ordinary raw-Protocol relation bindings. `GEPCDToBeta` is the public derived
grounding for the source PCD wrapper. The other three require confidential
occurrence-local invocations because they read Witness values. In particular,
`GE6ToNext4Witness` is not required for source validity: a copied or
independently obtained proof remains legal if the exact embedded verifier
accepts it. When a concrete construction claims a direct same-process causal
handoff, the equation supplies the public/value side only. The source Plan must
also export the exact proof occurrence and
`IssueAcceptedPlanWitnessIngressSupply` must consume that output right and the
target `WitnessIngress`. `JoinCausalPlanWitnessHandoff` checks the private
source/target occurrences against the retained
`CausalPlanWitnessHandoffCapability`; the final public/private conjunction is
`JoinCausalPlanStepRecurrence`. None of these runtime joins changes verifier
validity or makes immediate-predecessor provenance mandatory.

## 6. Core and Protocol representation

### 6.1 Two ordinary zero-challenge verifier Cores

For `j in {4,6}`, the required verifier Core schedule is finite and flat:

```text
root scope:
  bind x_j as Statement
  bind the exact public CRS or verification projection as PublicParameter

  ProverMessage(pi_j : Proof_j)
  InvokeCheck(V_j(public_parameter,x_j,pi_j))
  guarded Accept requiring check=true
  unconditional Reject fallback
```

Each Core has exactly four event occurrences, one prover decision, one check,
two terminals, and zero Challenges, VerifierMessages, Oracles, Claims, and
Reductions. The verifier algorithm has an exact ABI and evaluation contract;
its internal pairing checks are not runtime child Protocols.

The canonical Protocol for each Core is `Fresh`. Its challenge resolver is
unused because the Core has no Challenge occurrence. Canonical-framed and
duplex Fiat--Shamir siblings are not selected and add no source behavior;
proof hashing for transport or audit does not manufacture a
ChallengeInterpretation.

These two Cores model the underlying preprocessing-SNARK proof systems. They
are necessary for exact alpha/beta relation correspondence, but `Protocol6`
alone is not the source's public PCD endpoint.

### 6.2 The source PCD endpoint

The externally exposed source verifier receives message `z`, source
verification key `pcd_vk=(vk4,vk6)`, and proof `pi6`; its computation projects
and uses `vk6`, but the source API still carries the pair. It does not trust a
caller-authored `x6`. Its separate flat Core is:

```text
root scope:
  bind z:F4 as Statement
  bind pcd_vk:PCDVerificationKey as PublicParameter

  ProverMessage(pi6:Proof6)
  InvokeCheck(PCDVerify6(pcd_vk,z,pi6)) where PCDVerify6 exactly performs:
    vk6 := pcd_vk.vk6
    x4 := H4(bits4_prover(vk6) || bits4_prover(z))
    x6 := S4_to_6_host(x4)
    return V6(vk6,x6,pi6)
  guarded Accept requiring check=true
  unconditional Reject fallback
```

`ProtocolPCD = Protocol(CorePCD,Fresh)` is the public proof Protocol and
`GEPCDToBeta` records its derived-instance grounding. The raw `Protocol6`
remains the proof-system endpoint used to state beta-relation correspondence;
substituting it for `ProtocolPCD` would expose `x6` and omit the public `z`
binding. An optional `PlanPCD` may inline the finite `P4`-then-`P6` recipe, or
a Realization may orchestrate the two owner-local Plans and supply the final
semantic `Proof6`; neither form is runtime child-Core execution.

### 6.3 Why an imported-verification Core effect is wrong here

The prior proof is neither observed by the outer verifier nor checked by the
outer Core. It is private witness material used while constructing `pi4`.
Placing `V6(pi_in)` in an outer Core module effect would:

1. reveal a source-private witness coordinate to the outer verifier;
2. add a verifier-observable check and possibly a different verdict path;
3. duplicate the same predicate in Core and Relations;
4. change proof-system composition into direct verifier aggregation; and
5. make OIR package an event absent from the source Protocol.

A direct imported verifier does not require one universal Core constructor.
When the verifier-observable operation is a pure exact Boolean decision, its
native home is the existing typed `CheckDecl`/`InvokeCheck` path. A
`ModuleEffect` is reserved for a source whose verifier-observable imported
operation is genuinely stateful, has several typed observations, or otherwise
cannot be represented as that pure Check. Neither form is the representation
of verifier-in-circuit recursion.

The broad opening sentence of `pir/canonical-pir.md` Section 6 should therefore
be narrowed at convergence: a pure **verifier-observable** imported Boolean
verification uses Core `Check`; richer verifier-observable imported behavior
may use an exact PIR effect extension; verifier-in-relation recursion uses
Relations.

## 7. Prover Plans and construction order

### 7.1 Per-Protocol Plans

Each zero-challenge Core has one decision point. The alpha Plan contains:

```text
WitnessIngress:
  vk6,z,z_loc,z_in,b_base,pi_in_c4,b_res,alpha_advice

public proving material:
  either the source's full public CRS through an opened Core PublicParameter
  or one setup-specialized Plan constant

recipe:
  required exact P4 construction over the admitted witness and proving material
  -> pi4:Proof4
  -> MessageValue at the sole ProverDecisionPoint
```

The beta Plan analogously consumes `pi4_c6`, `beta_advice`, its public proving
material, and the required exact `P6` construction to emit `pi6`. Randomness
used internally by the preprocessing-SNARK provers is Plan private randomness
with exact fixed requirements; it is not relation witness unless the selected
proof system's relation explicitly says so.

The existing full-CRS/Core and setup-specialized-Plan controls are
source-faithful. A reusable minimal-verifier Plan could benefit from a public
prover-parameter lane, but the accumulation comparison does not independently
force that grammar change and the package therefore defers it under the frozen
promotion rule.

Neither Plan needs a post-final-challenge completion recipe: these Cores have
no challenge and the proof value is the sole decision move. The adjacent
folding cases, not recursive SNARK verification, decide the Plan-completion
question.

### 7.2 Two-Plan orchestration

One PCD node invokes the alpha proof construction and then the beta proof
construction. A `ProverPlan` is intentionally scoped to one `ProtocolId`; it
must not absorb both into a universal recursive Plan.

The application-level order is finite:

```text
admitted alpha Plan after profile closure + RX4_i/RW4_i
  -> semantic Proof4 occurrence

total S4_to_6_host and EncodeProof4ForCircuit6 derivations
  -> RX6_i/RW6_i

admitted beta Plan
  -> semantic Proof6 occurrence
```

Concrete scheduling, buffers, persistence, and supplier handles belong to
Realization. Evidence may record that one implementation followed the order.
Neither creates a new semantic authority or proves that the constructed proof
will verify.

## 8. Interface, OIR, and proof packaging

### 8.1 Protocol Interfaces

Each raw side and the public PCD endpoint require an Interface with:

- total slots for its Statement and public parameter input;
- one semantic proof transport entry preserving the eight group-element roles;
- one separately selected exact canonical group and tuple codec;
- one completion variant for Accept and one for Reject; and
- no Fiat--Shamir interpretation-failure completion.

The `ProtocolPCD` Interface binds public `z`, public `pcd_vk=(vk4,vk6)`, and
`Proof6`. The
raw `Protocol4` and `Protocol6` Interfaces bind `x4`/`vk4`/`Proof4` and
`x6`/`vk6`/`Proof6` respectively. The PDF fixes proof roles and reports byte
lengths but does not close any of these codecs; exact codec selection is a T2
profile obligation, not a fact inferred from `337 B` or `374 B`.

The externally retained PCD proof is `Proof6`. `Proof4` is an intermediate
semantic proof value. A realization may serialize it between the two proving
invocations, but doing so does not make it part of the public PCD proof
package.

Malformed bytes, noncanonical coordinates, wrong curve, subgroup failure,
wrong tuple order, or trailing data fail at Interface/OIR decoding before a
semantic proof value exists. A well-formed proof tuple whose equations are
false reaches the applicable verifier and yields Reject or relation
non-satisfaction, depending on which verifier is evaluating it.

### 8.2 Current OIR boundary

The current `OirEndpointGraphProfile` supports only canonical-framed
Fiat--Shamir endpoints and explicitly classifies Fresh endpoints as
`Unsupported(FreshEndpoint)`. It therefore cannot project any of the three
selected verifier endpoints even though their semantic shapes are finite.

The needed extension is an OIR-owned sibling profile, not a recursion-specific
operation:

```text
OirFreshEndpointGraphProfile:
  same bounded role, dependency, type, constant, pure-node, role-ABI,
    action-spine, claim, terminal, completion, and optional-Plan laws
  ChallengeInterpretation = Fresh
  StaticFs = absent
  Fresh Challenge ingress rules present only when the source Core has a
    Challenge occurrence
```

For this zero-challenge member the graph has no challenge ingress and no FS
state. It carries one proof transport, one verifier check, and two terminals.
The imported inner-verifier circuit remains in Relations and does not appear
as an OIR action. A source/target projection that adds it is Negative.

This profile is a known owner-local endpoint extension. Its absence prevents a
Native all-owner classification, but it does not reopen Core or recursive
identity.

### 8.3 Serialized intake versus direct causal handoff

When a prior `Proof6` is persisted and later used as recursive witness
material, the layers are:

```text
ProtocolPCD or Protocol6 semantic Proof6 occurrence
  --Interface/OIR codec--> canonical external bytes
  --Realization storage/transport--> received bytes occurrence
  --Plan-preparation private supplier using the same admitted codec-->
      fresh Proof6 semantic value
  --EncodeProof6ForCircuit4--> fresh pi_in_c4 witness occurrence
```

The first decode is public endpoint intake owned by Interface/OIR. The second
is private-material preparation owned by the Plan/Realization supplier path;
malformed stored bytes return `Malformed` or `Refused` before a prepared Plan
session and are not retroactively an OIR endpoint failure. This path creates an
ordinary fresh supplied witness occurrence. Even with a codec or transport
receipt, it does not establish the package's direct causal-handoff proposition.

The direct same-process path instead has the source Plan export the exact proof
value in its accepted continuation arm. `IssueAcceptedPlanWitnessIngressSupply`
atomically consumes that output right and the target's exact unfilled ingress,
returning `ReadyPlanWitnessIngressSupply`, its one-use capability, and a
`CausalPlanWitnessHandoffCapability`. The target occurrence is still fresh;
occurrence identity is never shared. `EncodeProof6ForCircuit4` then derives the
typed circuit witness, and `JoinCausalPlanWitnessHandoff` checks the two private
groundings against the live capability. If a public recurrence equation is
also claimed, `JoinCausalPlanStepRecurrence` requires exact agreement on both
run objects and both relation instances.

An affirmative artifact/codec correspondence or Realization receipt may show
that serialized values agree, but cannot mint, persist, recover, or substitute
for any live one-use Plan handoff capability. The recursive relation itself
still verifies the exact circuit equation
`CV6(vk6,x_in6_bits_in_F4,pi_in_c4,alpha_advice)=b_res` and, on a recursive
branch, requires `b_res=1`; it does not trust the receipt as proof validity. The
receipt, bytes, source path, and buffer identity stay out of
`RelationDefinitionId`, `CoreId`, and `ProtocolId`. Direct handoff results and
capabilities are likewise nonidentified process-local runtime objects.

## 9. Acyclic identity and setup construction

### 9.1 Typed owner table

| Object or fact | Owner | Exact role |
|---|---|---|
| fields, curves, groups, pairings, hash, field conversions, proof records, and finite circuit algorithms | authenticated semantic modules | exact finite denotations, ABIs, and evaluation contracts |
| alpha and beta predicates, relation Interfaces and instances, private assignments, satisfaction, bindings, and grounding equations | Relations | exact verifier-in-circuit semantics and occurrence-local relation meaning |
| outer Statement/public-parameter bindings, proof publication, verifier check, and Accept/Reject terminals | Core | one flat verifier-observable execution per proof system |
| zero-challenge `Fresh` interpretation | Protocol | source-faithful Challenge interpretation; no hidden Fiat--Shamir state |
| witness ingress, proving material, private randomness, and `P4`/`P6` construction recipes | Plan | honest proof construction without verifier authority |
| proof transport roles, exact byte codec, invocation slots, and completion presentation | Interface and OIR | external packaging and projection without importing the inner verifier as an action |
| one-use same-process output-to-ingress supply and live causal capability | Plan | optional direct semantic handoff between exact occurrences |
| concrete scheduling, serialized storage/transport, buffers, and supplier provenance | Realization | implementation placement and operational provenance; no authority to mint the direct Plan handoff |
| setup/key correspondence, circuit/verifier correspondence, soundness, knowledge, recursion depth, and theorem applicability | Analysis | qualified propositions under exact premises |
| source locks, setup observations, proof/run records, measurements, and correspondence artifacts | Evidence | support and observations, never semantic truth by presence |

The imported-verifier ownership shapes relevant to this decision are as
follows. A pure direct Boolean check whose input and outcome are verifier-
observable belongs to Core as an exact `Check`. Richer stateful or multi-
observation verifier behavior may use the exact `ModuleEffect` seam. A
verifier embedded in the predicate being proved belongs to the Relations
definition/evaluator. Proof bytes belong to Interface/OIR and concrete
transport to Realization in every case.

### 9.2 Semantic identity DAG

The source-faithful dependency order is:

```text
exact algebra and finite-circuit profile schemas
  -> generic V4 and V6 verifier semantics and proof ValueTypes

source-profile H4 parameter generation
  -> exact runtime matrix M4
  -> exact H4(M4) algorithm/module instance

finite alpha circuit payload containing M4 and parameterized V6 graph
  -> D4 = RelationDefinitionId(alpha payload,M4)
  -> RI4 and its semantic model

generic Core4(V4 ABI) -> Fresh Protocol4 -> Interface4 and Plan4
  -> ProtocolRelationBinding4(Protocol4,RI4)
  -> PlanWitnessBinding4(PlanWitnessSurface4,RI4)

after alpha setup produces the exact public vk4/pvk4 value:
  finite beta circuit payload containing V4_online graph and pvk4 constant
  -> D6 = RelationDefinitionId(beta payload)
  -> RI6 and its semantic model

generic Core6(V6 ABI) -> Fresh Protocol6 -> Interface6 and Plan6
  -> ProtocolRelationBinding6(Protocol6,RI6)
  -> PlanWitnessBinding6(PlanWitnessSurface6,RI6)

H4(M4) + generic V6 verifier ABI
  -> CorePCD -> Fresh ProtocolPCD -> public PCD Interface
```

The generic verifier Cores are parameterized by public verification material;
they do not depend on relation-specific setup outputs. The relation bindings
are descendants of both owners and never flow back into either identity.

No `RelationDefinition` contains its outer `ProtocolId`, binding, Interface,
Plan, OIR, run, proof value, or checked result. If exact protocol/definition
correspondence is needed, it is a separately identified proposition and
support basis.

The symbolic identity dependencies are therefore:

```text
AlgebraAndVerifierProfileIds
  -> H4ParameterSchemaId
  -> exact generated M4 value
  -> H4InstanceId(M4)
  -> D4 = RelationDefinitionId(alpha finite circuit body,M4)
  -> RI4 = RelationInterfaceId(D4, typed public/private declarations)

Core4Id = PIRId(exact public types, Proof4 message, V4 check, terminals)
Protocol4Id = ProtocolId(Core4Id, Fresh)
I4      = ProtocolInterfaceId(Protocol4Id, exact slots/codecs/completions)
Plan4   = ProverPlanId(Protocol4Id, exact ingress/material/randomness/P4 recipe)

D4 --source setup algorithm--> runtime pk4,vk4,pvk4 values
pvk4 value + AlgebraAndVerifierProfileIds
  -> D6 = RelationDefinitionId(beta finite circuit body)
  -> RI6 = RelationInterfaceId(D6, typed public/private declarations)

Core6Id = PIRId(exact public types, Proof6 message, V6 check, terminals)
Protocol6Id = ProtocolId(Core6Id, Fresh)
I6      = ProtocolInterfaceId(Protocol6Id, exact slots/codecs/completions)
Plan6   = ProverPlanId(Protocol6Id, exact ingress/material/randomness/P6 recipe)

CorePCDId = PIRId(H4InstanceId(M4), S4_to_6_host, V6,
                  z/PCDVerificationKey/Proof6 types, terminals)
ProtocolPCDId = ProtocolId(CorePCDId, Fresh)
IPCD = ProtocolInterfaceId(ProtocolPCDId, exact slots/codecs/completions)

ProtocolRelationBinding4 =
  RelationsId(Protocol4Id,RI4,GE4Statement coordinates)
PlanWitnessBinding4       = RelationsId(PlanWitnessSurface4,RI4)
ProtocolRelationBinding6 =
  RelationsId(Protocol6Id,RI6,GE6Statement coordinates)
PlanWitnessBinding6       = RelationsId(PlanWitnessSurface6,RI6)

all setup/circuit/key and theorem correspondence propositions
  = Analysis descendants of the exact owners and runtime setup values
```

`Core6Id` depends on the verification-key *type* and generic `V6` algorithm,
not on the later runtime `vk6` value. `D4` likewise contains parameterized
`V6` semantics but not `Protocol6Id`, `Core6Id`, or `vk6`. `CorePCDId` binds
the already selected `H4(M4)` algorithm but still treats the concrete
`pcd_vk=(vk4,vk6)` as invocation material. A setup-specialized Plan may
depend on the resulting proving-key value, but no relation or Core identity
depends back on that Plan.

### 9.3 The source setup-cycle breaker

A naive construction hardcodes `vk6` in the alpha circuit and `vk4` in the
beta circuit. Then:

```text
C4 -> vk4 -> C6 -> vk6 -> C4
```

The source deliberately avoids that cycle:

1. construct the alpha circuit with `vk6` as witness and bind it through the
   public digest `x4=H4(vk6||z)`;
2. generate `(pk4,vk4)` for the alpha circuit;
3. construct the beta circuit with processed `vk4` hardcoded;
4. generate `(pk6,vk6)` for the beta circuit; and
5. use the now-fixed `vk6` in the alpha witness and public digest.

The target preserves this order literally. It does not solve the cycle with a
hash fixed point, a self-referential Protocol ID, an ambient setup registry, or
an unauthenticated placeholder.

Key generation, common origin, trapdoor handling, and honest specialization
remain setup construction plus Evidence/Analysis. A canonical key value in a
relation body or invocation proves none of them.

### 9.4 Separate correspondence premise

After the acyclic semantic subjects and setup values exist, Analysis may form
one exact proposition of the following shape:

```text
SetupKeyCorrespondence(
  exact M4 and H4(M4), D4, D6,
  exact G4 and G6 algorithms,
  pk4, vk4, pvk4, pk6, vk6,
  beta hardcoded pvk4 occurrence,
  alpha witness vk6 occurrence,
  Core4 public vk4 occurrence,
  Core6 public vk6 occurrence,
  CorePCD H4(M4) dependency and public pcd_vk occurrence)
```

Its premises state that `M4` was generated under the selected hash-parameter
profile, `D4` and `CorePCD` use that exact matrix, `(pk4,vk4)` was generated
for exactly `D4`, `pvk4` is the exact source processing of that `vk4`, `D6`
contains exactly that `pvk4`, and `(pk6,vk6)` was generated for exactly `D6`. An affirmative result
can support a recursive-composition theorem or an implementation
correspondence. A missing or Negative result leaves semantic execution
well-formed but activates no such claim.

This proposition does not enter `D4`, `D6`, either Core, either Protocol, or
either Plan's parametric semantic body. It therefore records the source's
construction order without manufacturing a self-ID fixed point. The apparent
cycle is removed by asymmetric parameter placement; the later correspondence
premise checks that the concrete keys followed that placement. It neither
silently derives common origin from equal values nor proves setup honesty.

## 10. Non-cycle falsification

Fractal's recursion relation has the same semantic ownership despite a
different algebraic construction. For fixed security parameter, index-size
bound, instance length, message arity, compliance predicate, URS, and verifier
constraint system, its Construction 11.7 forms:

```text
public instance:
  (ivk,z_out)

private witness:
  z_loc and [(z_in_i,pi_in_i)] for i in 1..m

relation:
  Phi(z_out,z_loc,z_in_1,...,z_in_m) accepts
  and, on a recursive node,
  V(urs,ivk,(ivk,z_in_i),pi_in_i) accepts for every i
```

This is again one finite outer relation graph with prior proof values as
private witness. The outer proof system verifies only the newly constructed
outer proof. There is no pairing-friendly curve cycle and therefore no
alpha/beta proof converter, but the owner split is unchanged.

Fractal also adds a decisive Analysis boundary. Its recursive construction
instantiates the random oracle before putting the verifier in a constraint
system; the paper explicitly does not claim that arbitrary random-oracle
instantiation is secure. A target record cannot carry a QROM or post-quantum
property from the pre-instantiation proof into recursive composition merely
because the relation graph is expressible.

The comparison falsifies two possible overgeneralizations:

- curve-cycle fields and proof conversion are profile-local, not recursive
  Core semantics; and
- transparent or post-quantum setup does not remove the need for an exact
  finite verifier relation and separate theorem-applicability judgment.

## 11. Descent and resource bounds

### 11.1 No dynamic Core descent

One admitted Core run has descent depth zero. Its verifier check evaluates one
finite algorithm under one fixed contract. The verifier circuit inside the
outer relation is a finite DAG, not a runtime child execution. There is no
stack of Core capabilities, nested transcript state, inherited Interface, or
child terminal authority.

### 11.2 Finite relation evaluation

The selected alpha relation has exactly `101,935` source-profile gates and the
beta relation exactly `32,027`. Those two source counts are the only numeric
intrinsic bounds closed by this record. A strict-T2 relation-language profile
must additionally fix:

- maximum graph nodes and edges;
- maximum canonical constant and witness bytes;
- maximum bit-decomposition width;
- exact field, curve, extension-field, and pairing operation counts;
- maximum intermediate values and nesting depth; and
- deterministic work and memory charges.

The PDF and this architecture mapping do not supply numeric values for those
remaining limits, a complete canonical circuit-body byte length, or evaluator
transition/work bounds. They remain profile obligations. Once declared,
crossing a bound is `DeterministicLimitExceeded`. It is not relation
false, invalid proof, Core Reject, or permission to select a larger member at
runtime.

### 11.3 Recursion depth belongs to the run and Analysis

For a concrete PCD transcript choose an exact finite node DAG and maximum path
depth `D`. Each node uses the same admitted relations and Protocols with fresh
instances, witnesses, invocations, and proof values. `D` does not enter
`CoreId` or cause the Core to unroll `D` prior verifiers.

BCCT Theorem 6.1 applies to constant-depth compliance predicates. The selected
`Pi_step` permits compliant chains of arbitrary length, so its semantic depth
is `d(Pi_step)=infinity` in BCCT's Definition 5.8. Merely observing one run of
finite depth `D` does not satisfy Theorem 6.1. The separate PCD depth-reduction
construction changes the predicate/system and is not activated by recording a
smaller run. Therefore:

- one finite run record may bind a concrete `D` and resource total;
- an all-depth or polynomial-depth claim needs an exact Analysis family and
  the applicable source theorem;
- a successful finite execution is not evidence for extractor efficiency; and
- source proof-tree depth reduction is not a Core scheduling optimization.

## 12. Qualified failure ledger

| Boundary | Exact condition | Outcome |
|---|---|---|
| Source/profile intake | wrong paper revision, curve/profile substitution, missing circuit constant, or mismatched proof type | source lock or candidate formation fails |
| Relation formation | cyclic graph, wrong field edge, missing verifier subgraph, malformed branch, unbound key, wrong gate count, or non-total output | `Malformed`, `KindMismatch`, or `Refused` |
| Relation support | exact circuit language, algebra module, verifier graph, or evaluator unavailable | `Unsupported` or `MissingDependency` |
| Public proof decoding | noncanonical bytes, wrong curve, invalid point/subgroup, wrong tuple arity/order, or trailing bytes at endpoint intake | Interface/OIR `Malformed` or `Refused`; no semantic proof value |
| Private proof re-entry | stored bytes fail the selected private supplier's exact codec before Plan preparation | Plan/Realization supplier `Malformed` or `Refused`; no prepared Plan session |
| Alpha satisfaction | on a recursive branch `pi_in_c4` yields `b_res=0`, digest/key/message constraint fails, circuit advice is inconsistent, compliance fails, or base selector is invalid | occurrence-local relation Negative |
| Beta satisfaction | formed `pi4_c6` fails `CV4_online`, circuit advice is inconsistent, or reverse representation conversion disagrees | occurrence-local relation Negative |
| Honest construction | missing witness/proving material, randomness failure, or exact prover algorithm cannot produce a move | Plan strategy stops; no outer terminal result |
| Outer verification | formed outer proof fails its verifier equation | Core Reject |
| Outer verification | formed outer proof passes its verifier equation | Core Accept only; no relation or theorem inference |
| Resource | admitted evaluator, codec, prover recipe, or verifier exceeds its exact bound | `DeterministicLimitExceeded` |
| Setup/correspondence | key origin, relation specialization, converter correspondence, or ceremony premise absent | Analysis/Evidence cannot affirm; semantic execution is unchanged |
| Endpoint projection | current bounded OIR profile receives any of the three Fresh Protocols | `Unsupported(FreshEndpoint)` |
| Recursive theorem | proof-of-knowledge, extractor, CRH, depth, setup, or instantiation premise absent | no recursive-composition property result |

The same malformed byte sequence cannot be both an Interface failure and a
false verifier equation: decoding must first produce the exact semantic proof
type. Likewise, a false relation occurrence is not Core Reject, and Core
Accept does not turn a relation result affirmative.

## 13. Negative mutations

The candidate exact encoding must distinguish at least the following
mutations before strict T2 can be claimed:

1. replace the finite verifier circuit in the alpha relation with an ambient
   host callback;
2. execute `Protocol6` as a runtime child of the alpha Core;
3. expose `pi_in` as an outer Core message even though it is source-private
   witness;
4. put raw proof bytes directly in the relation while omitting the exact
   decoder computation;
5. treat `Proof4` and `Proof6` as one type because both have eight elements;
6. omit `vk6` or `z_in` from the input to the hash checked by the alpha
   relation;
7. accept caller-authored `x4` without checking the source
   `Cbits4`/`H4(vk6_bits||z_bits)` relation;
8. hardcode both `vk4` and `vk6` in mutually generated circuits;
9. replace the source setup order with a self-referential semantic ID or hash
   fixed point;
10. treat all-zero proof bytes as a base-case sentinel instead of using the
    typed `b_base` selector and a formed target-profile padding assignment;
11. omit the beta converter and claim the alpha proof is the source's external
    PCD proof;
12. combine alpha and beta proof generation into two messages of one Core;
13. let an Interface/OIR proof digest stand in for verifier execution;
14. identify a stored `pi_in` occurrence with a prior publication merely
    because their canonical values are equal;
15. require physical handoff identity even though the source requires only a
    valid prior proof value;
16. put recursion depth `D` in a dynamic Core loop or evaluator callback;
17. infer relation satisfaction from Core Accept;
18. infer recursive soundness or knowledge from one-step relation
    satisfaction;
19. inherit Fractal's QROM/post-quantum property after a concrete random-oracle
    instantiation without a separate applicability result;
20. project a Fresh Protocol through the current canonical-FS OIR profile;
21. add the imported inner-verifier graph as an OIR action; or
22. bind setup lineage, proof bytes, run receipts, or theorem results into
    `CoreId` to make a later check convenient;
23. equate semantic `X4`/`X6` values with the bit-carrier vectors consumed by
    `CV4_online` or `CV6`;
24. omit the exact division and verifier-circuit advice while claiming source
    circuit satisfaction;
25. replace `Cbits4`'s source-permitted representations with
    `bits4_prover` without explicitly classifying the stronger target
    relation; or
26. expose raw `Protocol6(x6,pi6)` as the public PCD endpoint and thereby omit
    public `z` plus the checked `H4`/`S4_to_6_host` derivation.

Mutations 1--3 and 21 distinguish Relations ownership from PIR/OIR ownership.
Mutations 4--5 and 13 distinguish semantic proof values from transport.
Mutations 6--12 distinguish the actual BCTV cycle breaker and two-stage
construction. Mutations 14--16 distinguish occurrence and run recursion from
semantic identity. Mutations 17--19 distinguish execution from Analysis.
Mutations 23--25 distinguish semantic values, circuit representations, and
advice. Mutation 26 distinguishes the raw beta-SNARK endpoint from the source
PCD endpoint.

## 14. Analysis and Evidence obligations

No cryptographic property activates from this architecture record. At minimum, a future
property package must state and separately support:

1. exact relation-definition/model correspondence for both finite circuits;
2. exact correspondence between each imported verifier constraint graph and
   its semantic/software verifier algorithm;
3. setup/key specialization for `C_pcd,4` and `C_pcd,6`, including the
   source's asymmetric key-dependency order;
4. collision resistance and encoding assumptions for `H4` and the
   key/message digest;
5. completeness, soundness, and proof of knowledge of both preprocessing
   SNARKs under their exact setup;
6. the recursive-composition theorem's extractor-strength and depth premises;
7. the exact compliance-predicate and transcript-DAG interpretation;
8. zero-knowledge composition, if claimed, including what the recursive
   witness contains;
9. Fractal-specific hash-instantiation and classical/QROM applicability, if
   that profile is selected; and
10. implementation correspondence for every curve, codec, verifier circuit,
    hash, conversion, proof layout, and resource observation.

For the selected `Pi_step`, Item 6 cannot cite BCCT Theorem 6.1 directly:
`d(Pi_step)=infinity`. It must instead select a depth-bounded predicate or the
paper's separate depth-reduction construction with all of that construction's
premises.

Evidence may record source digests, compiler/circuit observations, key
generation, proof bytes, replay, and implementation measurements. None is a
substitute for the semantic relation or theorem proposition it supports.

## 15. Closure verdict and model-change request

The architecture decision is resolved, but strict T2 is not. The record fixes
one finite BCTV schema (`s=n_msg=n_loc=l=1`), its two-gate compliance
predicate, source alpha/beta gate counts, exact high-level occurrence graph,
source endpoint distinction, setup order, owner split, identity directions,
failure classes, and falsifying mutations. It does **not** contain enough
source material to claim one admitted target relation body or endpoint
projection.

The remaining strict-T2 blockers are:

| Owner | Missing exact object |
|---|---|
| semantic modules / Relations | complete canonical alpha and beta circuit payloads; exact `Proof6Circuit4`, `Proof4Circuit6`, `AlphaCircuitAdvice4`, and `BetaCircuitAdvice6` carriers; one formed base-padding lowering policy; admitted definition/model evaluator and correspondence basis |
| setup profile | exact `M4` generation/instance binding and one concrete `pvk4`-specialized beta body, with exact `G4/G6` and processing algorithms |
| Core / portable algorithms | closed `V4`, `V6`, `PCDVerify6`, proof-to-circuit encoders, host/circuit representation conversions, and their evaluation contracts |
| Interface | exact Proof4 and Proof6 canonical byte codecs; the PDF's `337 B` and `374 B` measurements are insufficient |
| OIR | the owner-local Fresh endpoint graph sibling and exact projection for raw alpha, raw beta, and public PCD endpoints |
| resources | numeric graph, canonical-byte, advice, intermediate, evaluator-transition, work, and memory bounds beyond the source gate counts |

Until those objects exist, the achieved depth is T1 and the classification is
`ProfileOrModule`, not `Native` or a completed conservative grammar extension.
Fractal remains a materially different non-cycle falsifier and preserves the
same ownership conclusion.

Retain:

1. verifier-in-circuit recursion is a Relations predicate, not a runtime child
   Core;
2. proof values, proof bytes, and verifier semantics remain distinct;
3. proof-value recursion does not imply recursive semantic identity;
4. setup/key cycles are broken by explicit construction order and parameter
   placement, not self-reference;
5. recursion depth and extraction strength belong to Analysis; and
6. direct verifier-observable proof checking uses an exact Core `Check` when
   it is a pure Boolean operation, and only richer observable behavior needs a
   PIR module effect; both are different source shapes from recursion inside
   a relation.

The bounded owner-local work is:

- define or select the exact finite arithmetic-circuit Relations module and
  evaluator profile;
- select the concrete setup/hash and proof-codec profiles and close the public
  `ProtocolPCD` mapping;
- define the Fresh OIR endpoint sibling before endpoint projection is claimed;
  and
- narrow the overbroad imported-verification sentence in
  `pir/canonical-pir.md` so it does not move verifier-in-relation recursion into
  Core.

No first-class `RecursiveProof`, `ImportedVerifier`, `Accumulator`, child
execution, recursive codec, or setup-result root is justified.

## 16. Nonclaims

This record does not establish:

- repository implementation or wire-format support for BCTV, Fractal, PCD,
  recursive SNARKs, or either curve proof system;
- correctness of the selected finite circuit expansion or its reported gate
  count in any compiler;
- proof-system completeness, soundness, knowledge, zero knowledge, simulation,
  or recursive composition;
- collision resistance, curve security, pairing correctness, setup honesty,
  key specialization, trapdoor destruction, or proof-byte provenance;
- Fractal's post-quantum or transparent-recursion properties after hash
  instantiation;
- arbitrary recursion depth, IVC/NIVC, proof aggregation, accumulation,
  decider correctness, compression, or asymptotic succinctness;
- OIR, endpoint, Realization, compiler, or deployment support; or
- semantic freeze, migration readiness, or normative cutover.
