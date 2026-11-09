# Shared program and proof plan

The selected architecture is the 9 November 2026 unified-proof design and plan referenced in
[IMPLEMENTATION.md](IMPLEMENTATION.md). `ProtocolProof` remains the proof owner and now depends
on the shared `ZkcProgram` foundation as well as pinned mathematical libraries. Concrete IR,
source readers, generated subjects and production clients remain outside its dependency cone.

## Current Package 1 acceptance

1. Use one canonical `PIR.Process`/`Outcome`/`Execution` and generic `Zkc.Source.Region` from
   `lean/program`. Public clients and access programs author Process; FreeM is internal only.
2. Interpret Process through `Internal.effects`/`Internal.encode` and upstream `FreeM.runKernel`.
   Preserve full outcome, reached state and ordered log, including process and handler stops,
   unconditional mass, and deterministic agreement under Dirac handlers. Keep measurability
   and countable-reply premises explicit.
3. Preserve fixed property meanings and both root closures. Local operation contracts,
   exact same-interface `Installation`, whole initial-law coverage and directed terminal
   implications must derive the requested conclusion, not assume it.
4. Migrate extraction and simulation access as well as the roots: explicit Event parameters,
   success only on a valid returned witness, `Outcome View` observations and structural
   Process call bounds. Keep canonical/custom and closed/conditional receipt distinctions.
5. Retain complete adaptive/nested and shared-state model clients, property profiles and
   counterexamples. A shared challenge must not acquire independence; a stopped execution
   must not disappear from a probability law or enter a success-only denominator.
6. Integrate the proof handoffs, check the shared-package/import boundaries, and record the
   exact final package build, declaration audit and review scope. Cross-package integration
   retains its separate gates; earlier checkpoint evidence does not certify this migration.

The proof-owned implementation, complete models, property controls, probability and adequacy
laws are integrated. The final proof-package build and standard-axiom audit passed; see
[VALIDATION.md](VALIDATION.md). Cross-package wiring and architecture acceptance remain
integration responsibilities.

## Later architecture units

- **Package 2, parent-owned:** differing-interface representation, property-appropriate
  transports, service wiring and broader composition. Cover malformed replies, all terminal
  results, whole initial distributions, shared state and explicit security losses. Existing
  same-interface installation and Process substitution do not complete these obligations.
- **Package 3:** one checked construction/companion path and its proposer over typed Region,
  with explicit residual obligations, reusable callback/invariant rules and a soundness theorem.
- **Package 4:** consolidate reusable mathematical library ownership and retire redundant paths
  after statement-preserving validation.

An automatic constructor, security-transforming reduction library and actual protocol adoption
are not Package 1 results. Production connections need their own later adoption and validation
unit; complete mathematical models do not establish compiler or deployed-protocol security.

## Historical standalone checkpoint (`276b63146`)

The original checkpoint concerned fixed requests, upper/lower root closures, component and
contract rules, two complete model clients and refusal controls over the then-public FreeM
surface. [VALIDATION.md](VALIDATION.md) and [REVIEW.md](REVIEW.md) retain its build, audit and
independent-review records and limits. Those records describe that bounded checkpoint, not
validation of the shared-package extraction or current Process migration.

Its original acceptance requirements remain useful: local-to-global closure for every admitted
adaptive client, quantitative composition without inferred independence, unconditional
completeness, and nontrivial whole-model claims with refused mutations. The public carrier and
package dependency decisions above supersede the original no-shared-program/FreeM authoring
choices. The old implementation checkpoint remains historical evidence.

## Historical property-interface unit

The subsequent property unit preserved the original kernel backend while adding promise regions,
optional witness relations, complete measurable observations, bounded extraction and operational
simulation. It fixed access, algorithm, quantifiers, guarantees and resource scope in requests;
separated built-in/custom receipts; and made conditional premises and nonvacuity explicit.
Its plan required closed receipts and relevant refused mutations for every built-in property,
followed by affected-module checks and a package/audit gate.

Package 1 retains those semantic distinctions and reindexes operational requests to Process and
complete Execution. Historical validation does not discharge the current migration checks.
Runtime/PPT adequacy, a report generator and imported protocol proofs remain outside that
property unit and the present documentation work.
