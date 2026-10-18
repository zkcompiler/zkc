# Checked compiler stages

A security theorem about an original protocol transfers to the program a
runtime executes only if every compiler stage between them is linked by a
checked rule whose soundness theorem relates the stages' meanings, and the
rules compose. This note describes the common shape of such rules, the semantic
relations different properties need, and the two rules this package implements:
transcript construction and participant projection.

## The shell

A checked rule from a source stage to a target stage has five parts.

1. **Stage meanings.** Each stage has its own meaning, independent of the rules
   that mention it: a process over a declared action interface
   (`PIR.Proc`), or a monadic computation over an oracle. Adjacent rules meet at
   a shared stage meaning.
2. **Certificate.** Data the compiler emits beside the target to guide the
   check. It may be empty, when the check recomputes the correspondence from
   the target itself, or it may be a per-compile equation. A certificate must be
   bound to its source and target, by digest, entry and policy comparisons that
   the check performs.
3. **Check.** A total function from source, target and certificate to
   `Except String Unit`, with a named refusal for each obligation. It runs per
   compile in the kernel (`decide +kernel`), so the compiler pass under check is
   not trusted for the checked property; what remains trusted is that the
   checked artifact is the compiled one (the exporter and its rendering into
   Lean data, which are tested boundaries).
4. **Relation.** A property-specific relation between the two meanings, chosen
   by what the stage must preserve (below).
5. **Soundness.** Acceptance implies the relation for every parameter the
   meanings leave free: monad, oracle, service handle, inputs related by an
   explicit input relation, and proof.

Rules compose along a shared meaning when their relations compose: from
`R₁ ⟦a⟧ ⟦b⟧` and `R₂ ⟦b⟧ ⟦c⟧` a composition law yields `R₃ ⟦a⟧ ⟦c⟧`. The
composed check is the conjunction of the checks on the artifacts involved.

## Relations by property

One relation does not fit every stage. The shell is shared; the relation is
chosen per stage, and the composition law and the preserved properties follow
from it.

| Relation | Form | Preserves | Composition |
|---|---|---|---|
| Exact process equality | `⟦t⟧ = T ⟦s⟧` for a fixed semantic transformer `T` (identity, output selection, the Fiat–Shamir transform) | Every property of the process: outcome distributions in every environment, hence completeness, soundness and any view-based property | Rewriting; transformers compose as functions |
| Representation refinement | A simulation between `⟦t⟧` and `⟦s⟧` up to a representation relation on values, actions and stops (limbs for field elements, bytes for typed messages, memory for environments); the target may also stop for resource or codec reasons | Acceptance reflection: when the target accepts, the source accepts on related values, which suffices for soundness. Completeness also needs the converse, which holds only under resource and progress assumptions: sufficient bounds, codecs that accept honest encodings, loops that finish within budget | Representation relations compose; the stop conditions of both stages accumulate |
| Probabilistic reduction with loss | A bound relating experiments: the target's advantage or extraction probability against the source's, with an explicit loss in the query count and field size | Only the stated security property, with its loss | Losses add or compose; adversary classes and query bounds must match |

The two implemented rules use exact equality. Probabilistic loss enters only
in the security consumer, VCVio's Fiat–Shamir theorem for Sigma protocols,
applied to the transform of the original verifier. Lower stages, from the
participant program to the executed `zkc.program`, are representation
refinements, and their completeness statements need the resource and progress
assumptions above.

## Transcript construction

- Source meaning: the exported validator's interactive reading `spec`, in which
  a challenge is the selected query on a service handle and the observation of a
  message the validator sends is that message's delivery.
- Target meaning: the same export's ideal reading `ideal` for a challenge
  function on typed histories.
- Certificate: the export's policy (suite, public inputs, replaced service,
  selected query and delivery sites, framing) and its occurrence templates. The
  context is derived from the original roster.
- Check: `check`, and `checkExport` against the original export.
- Relation: `ideal context challenge … = transform context challenge (spec …)`
  for every monad and challenge function.
- Soundness: `check_sound` ([specification](../spec/fiat-shamir.md#the-rule)).

## Participant projection

- Source meaning: the admitted original program's participant process at the
  validator role, `Program.participant`.
- Target meaning: the exported validator's interactive reading `spec`.
- Certificate: none besides the export. A deterministic lockstep walk recomputes
  which exported reference holds which original component (`Slot`). It follows
  protocol applications into the callee's body in the child context and matches
  each repeat with one exported loop whose body it walks once, so the check is
  linear in the program, not in the number of iterations.
- Check: `project`.
- Relation: equality of the two processes read through the validator's outputs,
  for inputs related by the published input positions.
- Soundness: `project_sound` ([specification](../spec/participant-projection.md)).
  A repeat's soundness is an induction on its iterations inside the walk's
  soundness, which is itself an induction on the walk.

The rule replaces the per-Entry equation that previously tied the compiled
Schnorr validator's interactive reading to the original verifier. That equation
was a valid certificate, checked per compile, but it bound the export to the
original only by name, needed an Entry-specific proof and cost kernel time that
grew with the unfolded program. The projection rule makes the same mathematical
correspondence a theorem about every accepted export: a validator calculation
must be implemented by the same calculation on the references holding its
operands, so a mutation of the verifier's arithmetic that keeps the transcript
wiring is refused.

## Composition

The compiler does not export the interactive role-local program. Both rules
read the one constructed export: the projection rule as its interactive reading,
the construction rule as both its interactive and its ideal reading. The
intermediate stage is a meaning, not an artifact. `checkCompiled` runs both
checks on the export against one admitted original (`Structured.Imported`): the
construction rule reads its snapshot and the projection rule the program that
snapshot admits, so no check can pair a snapshot with a program it does not
admit. `compiled_transform` composes their equalities:

```text
ideal (export) = transform (spec (export))      construction
spec (export)  = original validator             projection, through the outputs
ideal (export) = transform (original validator) composed
```

A security theorem about `transform` of the original verifier therefore
applies to the compiled verifier with no Entry-specific proof beyond the input
relation and the position of the acceptance output. The compiled Schnorr and
Sumcheck proof Entries are both linked this way; for Sumcheck the transformed
original rewrites further, with an existing source theorem, to the rounds
followed by the multilinear check. The composed Sumcheck Entry, with two
applications, needs no Entry-specific proof for the composed equation: its
admission and the composed check are evaluated in the kernel, and the generic
theorem applies. Instantiating the theorem at an Entry's inputs and acceptance
output takes the input relation and output selection lemmas, which the Schnorr,
Sumcheck, Schnorr AND and Chaum–Pedersen Entries state. Those lemmas need the
admitted program's entry types in literal form: the Sigma Entries are therefore
admitted from printed typed bodies, because with a kernel-evaluated admission
the elaborator reads the entry types only by evaluating the admission, which
took minutes per Entry in an experiment.

Security composes the same way. `CompiledSchnorrFiatShamir` and
`CompiledSumcheckFiatShamir` prove their bounds about `transform` of the
original verifier (VCVio's Schnorr extraction; round-by-round soundness of the
imported Sumcheck verifier) and rewrite with the composed equation, so the
compiled verifiers' ideal interpretations inherit the bounds without a proof
about the compiled programs. `ExecutableSchnorrFiatShamir` continues one stage
down through the lowering rule, and a walk over its proof's dependencies shows
that the proof reaches the general rules and the Entry's admitted original, and
not the Entry's `spec_equation`. The walk also lists the Entry-specific
equations between processes that the proof reaches; all are about the original
side, and the two the kernel checks by evaluation are the Proof Entry's
validator process (`SchnorrProof.process_equation`) and its retained DLog
formula's process (`SchnorrProofBinding.formula_process`).

## Stage meanings

| Stage | Artifact | Meaning |
|---|---|---|
| Original protocol | Structured export, admitted to `Program` | `Program.participant` per role, over the participant actions |
| Role-local interactive | Virtual: the constructed export read by `spec` | `spec`, over the same actions |
| Constructed | `zkc.constructed-participant/0` | `ideal`, a monadic function of a challenge function and a typed proof |
| Executable participant | The validator participant of the `zkc.program/0` candidate, straight-line validators with single-level local calls | `Zkc.Executable.execute`: framed proof bytes, any decoder, an instruction budget, frames and transcript custody, related to the metered `ideal` by the [lowering rule](../spec/executable.md) |
| Below the executable participant | Not modeled | Representation refinements of the executable meaning with resource stops |

## Toward lower stages

The rule from the constructed participant to the executable participant is a
representation refinement. `Zkc.Executable` realizes it for straight-line
validators whose constructed programs have no helper `call` instructions and no
loops (the executable's single-level local calls are frames the reading treats
transparently): the reading of the program into
constructed instructions is the certificate, and the relation is outcome class,
whole-proof consumption and challenge interaction against a metered ideal
meaning. The meanings above fix what such a rule must expose in general:

- the same action interface for receives and replies, with codecs that relate
  proof bytes to typed messages, refusing on decoding failure where the ideal
  reading refuses;
- the transcript capability as an abstract state related to the typed history
  by the suite's absorption of encoded events, so that a challenge computed from
  the state is the challenge function applied to the history;
- the prepared helper bodies. Constructed programs call the original's helpers
  by name; an executable stage runs prepared bodies, so a helper-preparation
  rule (inlining and canonicalization with a body correspondence) must relate
  them before the composed theorem reaches executed code;
- resource stops (bounds, allocation, capacity) as additional refusals, which
  preserve acceptance reflection and are excluded from completeness by explicit
  resource premises.

## Certificates and scalability

Lockstep rules suit passes that keep operation order and only erase,
annotate or reinterpret operations, as projection and transcript construction
do. A pass that reorders, merges or rewrites operations needs a certificate:
a map from target operations to source operations with a dependency check, or
a rewriting trace whose algebraic side conditions are checked or proved. The
projection rule compares operations, not their algebra; an equal comparison
with swapped operands is refused. A total calculation the export omits is
admitted only while no later use needs its result. Inlining is absorbed into the
walk where it is structural: a Math helper whose body consists of carrier
calculations is walked inline, so the conjunction the compiler inlines from
`zkc::boolean::both` is matched without a certificate.

Per-compile equations remain the fallback certificate for a stage without a
general rule. Their cost is kernel time proportional to the unfolded program and
an Entry-specific proof per compile; their source binding must come from the
check, not from naming.

## Deterministic obligations of the random-oracle model

The random-oracle assumption bundles a probabilistic idealization with
deterministic correspondence obligations. Of the latter:

- Proved. The canonical occurrence encoding is injective and
  prefix-free in the template and the iteration coordinates
  (`occurrence_inj`), and the bridge checks in the kernel that the model
  encoding of each exported template is its native bytes. The construction
  rule's simulation proves that at every exported observation and challenge the
  ideal transcript state is the transform's absorbed history: each exported
  occurrence template, read through `Template.origin`, is exactly the event the
  transform absorbs at the original site, and the transform's challenge input is
  that history (`Synchronized` in `check_sound`).
- Assumed. The suite's framing, labels and payload codecs encode typed histories
  injectively, and the native kernels absorb exactly the encoded occurrences and
  payloads; proof bytes decode canonically to the typed messages in order. Model
  origins omit iteration coordinates, which the native occurrence bytes carry: a
  model history stands for the native bytes only because a deterministic
  validator's coordinates at each occurrence are determined by its absorbed
  history. Likewise, the native fields the model origin does not read (protocol
  names, a query's service port, contract and owner) are fixed by the exported
  instruction rather than checked against the original.
