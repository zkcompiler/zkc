# GKR canonical claims

The canonical subject fixes the actual authored pair and the registered
`circuit_outputs` target. The source verifier, honest producer, compiled
correspondence and claim receipts use that same pair. The mathematical circuit
is `Zkc.Protocols.Gkr.Circuit`; it is independent of the producer's working
arrays and proof messages.

## Independent target and admission

`RootEncoding` derives the input/output decoding, wiring blocks, selector
capacity and machine bounds from `CircuitEncoding.Admitted`. Its output
predicate is `CircuitEncoding.Outputs`. A malformed circuit shape has a false
target, including unused malformed wiring at zero layers. A shape-valid false
output remains admitted.

`CanonicalPair` retains the current native producer and validator exports.
`Canonical` and `Generated.Subject` select the source's registered output
clause through `Relations.registry`. `Canonical.holds_all` identifies its
meaning for every typed adversarial statement. Soundness reads the actual
validator's seven public inputs. The honest-input policy supplies circuit
admission and role agreement for completeness.

## Actual source and compiled correspondence

`GkrSourceAdmission` accounts for every raw admission branch. `RootSource`
composes those branches with the complete source-reading theorem and the
existing GKR component soundness laws. `CanonicalSource` gives fixed-target
rejection for all typed public statements without a supplied representation.
The generated normal forms use the current eight-input Pending ABI, including
the prefix carried into the right rounds, and the actual terminal input call.

`OccurrenceRouting`, `OccurrenceLayerRouting` and `OccurrenceRootRouting`
prove resolution for the full source validator. Every nested round,
coefficient and layer index is retained. Shared `FiatShamir.OccurrenceReading`
transfers reading, losslessness, constant-price rejection and costs over those
checked routes. `CanonicalReading` retains full optional returns, exact
ordered history, empty final occurrence frames, and every stop.

`CanonicalVerifier` associates the complete nominal validator with the
mathematical honest replay. `CanonicalReadback.actual` then relates the actual
source producer to that actual validator: the producer computes its proof,
both sides share the exact history, and their complete source returns remain
in the postcondition. Its mathematical premises are independent admission and
circuit outputs.

The generated `OriginalCertificates.producer` and `.validator`
certify the full actual compiled participants, for all typed inputs and
replies, including stops. Their live relations check the complete input ABI;
return relations retain the complete physical frames and transcript values.
`CanonicalInstallation` installs this validator certificate together with the
same nominal reading used by `CanonicalCompleteness` for the pair. No helper
success, representation witness or transcript equality is supplied by a caller.

## Structural connection generation

Run `python3 lean/security/checks/generate_gkr_connections.py --write` from the
repository to regenerate the two constructed views and ten concrete connection
modules for each installation. Omit `--write` for exact comparison, including
the committed ownership and authored-connection inventory in `checks/`.
The owner uses the selected `lake` executable (`--lake` overrides `PATH`), this
checkout's toolchain and prepared dependencies. Historical before/after counts
come from the committed baseline data; regeneration does not require development
commits to remain in Git history.

`ZkcTools.ConstructionBindings.Frames` traverses recursive SSA syntax. Qualified
source repeat occurrences select the output, layer, two rounds and coefficient
regions; the selected descriptors supply capture lengths, count/initial/yield
references and callback paths. Source visibility and a proposed input permutation
supply the full optional input ABI. `Generation.GkrConnections` is a registered
family installation of the existing GKR callback laws. Its small typed
`Installation` contains the actual participants and their input orders. The
shared traversal and constructed-view printer contain no GKR dispatch or
additional evaluator.

`ConnectionTactics` shares the layer, root and repeat assembly strategies.
`OutputTemplate` retains the parametric output-loop law as ordinary library
mathematics. `Original.Simulation.participant` installs any full body certificate
with its checked input/live relation and complete return readback. Generated
callback equations and proofs are independently elaborated and kernel checked;
the descriptor or printer does not grant semantic authority. Unsupported shapes
refuse, or fail their emitted correspondence proof.

`LayoutVariant` is a formal perturbation of the canonical artifact trees with
explicit provenance: it reverses live input slots within equal nominal sorts,
prepends a pure coordinate allocation and renames recursive uses and yields.
This changes allocated offsets, input references and callback selectors. The
same owner generates the `Rebound` connections, including both complete roots
and their arbitrary-handler execution theorems. Structural and occurrence
checks are independent of those full connections.
`TestsSecurity.GkrStructuralGeneration` checks rebinding and refuses a mismatched
input descriptor and the old callback descriptor. This variant has no claimed
native byte identity; canonical artifacts and property consumers stay fixed.

The ownership manifest records current input/output hashes. The inventory
accounts separately for the original 20 linkage files, retained mathematical
and source-presentation libraries, generated installations, and newly authored
templates/rules. The original 2,709 lines were not all duplication, and moving
work into a generator is not a reduction in total authored library code.

## Generated endpoints

`checks/GenerateGkrCanonical.lean` uses the shared fixed-subject, ABI,
soundness, completeness and registration printers. `Generated.ABI` fixes
public positions, role projections and public-binding history before evidence
is supplied. `CanonicalPolicy` proves independent target and admission laws at
that ABI and supplies an admitted nonvacuous circuit.

`CanonicalSoundness` gives the charged export at the four actual selected
challenge sites. Each site has price `4 / cardinality(bls12-381.fr)`. The
validator has at most 40 draws, and the scalar adaptive bound is
`4 * (Q + 40) / cardinality(bls12-381.fr)`. `CanonicalCompleteness` transports
the actual producer's readback through the same full correspondence and proves
perfect compiled-ideal completeness.

`checks/GenerateGkrCanonicalClaims.py` uses the common data-only request
renderer. The proposed quantities acquire receipts only through the checked
theorem applications in `Generated.SubjectSoundnessClaims` and
`Generated.SubjectCompletenessClaims`.

## Validation and maintained consumers

`TestsSecurity.GkrCanonicalClaims` checks the complete, scalar-sound and
charged-sound receipt clients for the same fixed subject. Its controls reject
a zero-error soundness request and a different retained target.
`TestsSecurity.GkrCanonical` includes actual producer-generated proof controls,
false outputs and malformed wiring. `GkrRootEncoding`, `GkrSourceAdmission`,
`GkrSourceRoot` and `GkrCurrentReading` cover admission and current source
contracts. These controls supplement the universal theorems.

The maintained coordinate-erased whole compiled route remains available
through `Source.compiled_binding` in `RootContract`, `GkrProof.compiled_transform` and the
ArkLib compiled GKR soundness consumers. Its current bodies and imports are
ported directly. Superseded normal-form modules are replaced, without
compatibility aliases. The protection ledger records the selected theorem
statements; source and compiled artifact identities require separate exact
association and receipt checks.
