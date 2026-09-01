# Formal Assurance Architecture Research

> **Kind:** Temporary cross-cutting research-program index
> **State:** Active; F0 architecture research started, F1 and F2 reserved as
> dependent feasibility programs
> **Authority:** None. This package changes no current or target semantics,
> artifact identity, theorem status, Analysis judgment, implementation claim,
> or product-roadmap priority.
> **Main-lane relation:** Side research against the holdout-stable semantic
> candidate. It does not replace the dependency-ordered post-freeze program or
> activate Stage 4B.
> **Deletion rule:** Absorb selected contracts, rationale, and explicit
> deferrals into their durable owners, then remove this package before
> `docs-next/` cutover.

## Central question

What is the ideal assurance architecture for turning one exact admitted zkc
subject into a formally interpreted subject and then into one qualified,
property-specific Analysis judgment, while:

- preserving zkc-native interaction, reduction, interleaving, challenge,
  Oracle, failure, and terminal meaning;
- permitting VCVio-native operational and game reasoning;
- reusing ArkLib or another theorem library only when an exact correspondence
  is established;
- allowing untrusted, replaceable, or proof-producing exporters and compiler
  passes behind small independently checked boundaries; and
- preventing a proof assistant, theorem name, receipt, formal syntax, producer,
  or serialized proof artifact from becoming ambient semantic authority?

The current design is one candidate, not the default winner. F0 may recommend
alignment, an additive formal subject, a changed owner boundary, or a larger
semantic redesign when the gain and migration cone justify it.

## Program sequence

```text
F0  ideal assurance architecture and current-design falsification
  -> F1  concrete admitted-subject reification and correspondence
  -> F2  zkc-native operational interpretation and one property pilot
```

### F0 — assurance architecture

Reconstruct the exact current and selected target boundaries, derive a clean-
room ideal architecture, compare equal-resolution candidates, and identify
every required subject, identity, authority, proposition, checker, trust root,
and refusal. F0 ends with a provisional architecture, explicit main-design
changes or positive non-change rationale, and exact F1/F2 entry contracts.

### F1 — subject reification

Test the F0 architecture by deriving one complete formal subject from an exact
admitted bounded Protocol/Relations/Analysis source. The exporter may be
untrusted; a smaller independent checker or proof object must establish the
claimed subject correspondence. F1 may reveal that F0 omitted an observable,
bound the wrong identity, or assigned authority to the wrong owner; such a
finding reopens F0 explicitly.

### F2 — operational semantics

Interpret the F1 subject as a typed oracle computation, initially using VCVio
as the leading candidate substrate, and establish one bounded runner or trace
correspondence plus one property-specific theorem path. A second discriminating
case must exercise a zkc-native feature such as interleaving, shared challenge,
or Fiat--Shamir game structure. ArkLib remains a comparison and selective
theorem-provider candidate where its subject matches exactly.

F1 and F2 are research programs, not commitments to one Lean encoding,
provider, extraction tool, or durable schema.

## Package record

- [`f0-charter-and-method.md`](f0-charter-and-method.md) fixes F0 scope,
  candidate discipline, workstreams, scenarios, gates, and handoff contracts.
- [`f0-current-baseline.md`](f0-current-baseline.md) starts the live current-
  and target-model reconstruction and records the first design pressures and
  non-implications.
- [`f0-source-ledger.md`](f0-source-ledger.md) records the first exact live
  VCVio/ArkLib source pass, their actual layering, material open boundaries,
  and the resulting architecture implications and source limits.

Later F0 records will extend the primary-source ledger and add code/spec
correspondence, the candidate matrix, scenario and counterexample results, the
convergence decision, and the current-to-target gap map. F1 and F2 gain their
own package indexes only after F0 defines their exact entry gates.

## Known risks and non-claims

- A formal interpretation is not automatically faithful to the admitted zkc
  subject.
- A checked correspondence does not establish a cryptographic property.
- A property theorem does not establish compiler-pass preservation or backend
  realization.
- A VCVio or ArkLib proof does not by itself verify zkc's C++, MLIR carrier,
  canonical encoder, generated code, cryptographic primitives, or deployment.
- A feasibility prototype is disposable evidence and cannot rotate a durable
  profile, establish theorem truth, or authorize implementation.
- F0 may find no required kernel change; that outcome is valid only after the
  generative and capability-expanding candidates receive equal-resolution
  treatment.

## Intended durable destinations

- integrated architecture and owner boundaries: `docs-next/project/`;
- formal subjects and exact source views: `docs-next/pir/` and
  `docs-next/relations/`;
- theorem providers, validation bases, qualified judgments, trust closure,
  and property transport: `docs-next/analysis/`;
- transformation preservation and decision consumption: `docs-next/compiler/`;
- endpoint projection and operational correspondence: `docs-next/oir/` and,
  only after activation, `docs-next/realization/`;
- execution order and deferred product commitments: the single authoritative
  roadmap under `docs/`.

No durable page may depend semantically on this package.
