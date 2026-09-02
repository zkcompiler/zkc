# F1-R1A Target Basis and the Identity/Admission Gap

> **Kind:** Temporary F1 exact-source prerequisite result
> **State:** F1-R1A target profile/source basis complete at bounded research
> resolution; one-slice F1-R1B target carrier/admission is now complete at
> bounded research resolution. F1-R1C0 returns `CannotAnswer` and reopens F0-V
> at the owner-view publication boundary; R1C waits on that repair, while R1D,
> F1-I, and F2 remain open
> **Authority:** None. This result changes no current or target semantic law,
> profile identity, admission outcome, Analysis judgment, or product claim.
> **Evidence:** The focused gate under
> [`evaluation/formal-source-target-basis-f1r1a/`](../../../../evaluation/formal-source-target-basis-f1r1a/README.md)
> passes 10/10 expected boundary checks.

## 1. Question and result

F1-R1A asks whether the first exact-source prerequisite is already available:

> Can the selected target Interaction profile, its exact owner source, and the
> Core/Protocol/view declaration routing be reconstructed independently, while
> mechanically refusing substitution of the executable K2 fixture surface?

The bounded answer is **Affirmative** for the profile/source basis and
**Refused** for fixture substitution. Two independent publication compilers
reproduce the complete target `pir.interaction` profile and its frozen v0
identity. The target source commits the Appendix A carrier, admission law,
static-view law, and evaluator signature.

This does not complete target reification. The repository still has no
executable durable target body compiler/admission evaluator or target static-
view evaluator. The K2 implementation is deliberately witness-local and
cannot fill that gap by changing a profile argument or recomputing IDs.

## 2. Exact inspected boundary

The reproduced target Interaction coordinate is:

| Coordinate | Value |
|---|---|
| profile family | `pir.interaction` revision `0` |
| profile body length | `133333` octets |
| profile body SHA-256 | `46a4b92b28962ace15009ca2a05ee26e92b0729fb6d7231fd46f3aa6735d1365` |
| profile digest | `f21774d19ebf5e045b1d5c70f9bd0ee1c7eb1202dc11f948900eb067e102ce87` |
| target Core top-level fields | ordinals `0..13` |
| target Protocol top-level fields | ordinals `0,1` |

The owner manifest routes `pir.interactive-core` to
`interactive-core-body-v0` and `pir.protocol` to
`fresh-protocol-body-v0`. It also commits `core-admission-v0`,
`static-view-issuance-v0`, and `interaction-evaluator-v0`. This establishes
exact source selection and identity reconstruction, not execution of those
declarations.

The executable K2 Schnorr discriminator instead has:

| Coordinate | K2 witness | Target requirement |
|---|---|---|
| Interaction profile digest | `8bd3dcbe3e74c131f2def5ee386ec54e439ebf03edaa55565c0ed1f5a776e3da` | frozen digest above |
| Core top-level fields | ordinals `0..7` | ordinals `0..13` |
| Fresh Protocol top-level fields | ordinals `0,1` | ordinals `0,1` |
| Protocol Core dependency | exact K2 Core ID | exact admitted target Core ID |

The matching Protocol wrapper is intentionally a useful discriminator: a
first-level shape check alone would accept it even though its dependency is
the wrong semantic subject.

## 3. Executable identity/admission separation

The gate performs two unsafe-looking constructions deliberately. First, it
passes the decoded eight-field K2 Core body to Foundation's ordinary identity
constructor with the target Interaction profile. Foundation validly forms a
new `pir.interactive-core` typed ID. Second, it recursively places that new ID
in a target-profiled two-field Fresh Protocol body and again forms a typed ID.

Both are refused by this prerequisite gate as candidate target subjects:

```text
profiled_content_id(target_profile, arbitrary canonical body)
  -> a well-formed typed identity

necessary target Core carrier check
  -> Refused: eight-field body is not InteractiveCoreBody

necessary target Protocol dependency check
  -> Refused: referenced Core has no target admission
```

This is not a Foundation defect. Foundation owns canonical value and identity
formation; Interaction owns the meaning and admission of Interaction-profiled
subjects. Making Foundation execute every domain law would recreate the
ambient semantic authority that the redesign intentionally removed.

The minimum trustworthy chain is therefore:

```text
exact owner source publication
  -> owner body compiler
  -> owner carrier validation and semantic admission
  -> exact admitted owner handle
  -> owner-derived view/read closure
  -> neutral formal-source package
  -> independent correspondence checker
  -> qualified Analysis judgment
```

No suffix of this chain can be inferred from typed identity formation alone.

## 4. F1-R1 decomposition

The previous `F1-R1 exact offline target body/view reification` label hid four
different failure boundaries. The executable result refines it as follows:

```text
F1-R1A  exact target profile and owner-source basis       [complete, bounded]
  -> F1-R1B  exact target carrier and admission           [complete, bounded slice]
  -> F1-R1C0 owner-view source determinacy                [complete, CannotAnswer]
  -> F0-V    owner-view schema/publication repair         [open]
  -> F1-R1C  exact owner static views and read closure    [waiting on F0-V]
  -> F1-R1D  Relations/correspondence/package integration [open]
  -> F1-I    live owner handles and source authority      [open]
```

This is a sequencing refinement inside the existing A/S/C architecture. It
does not add a `FormalKernel`, change the Core/Protocol ownership split, or
make profile publication an admission authority.

### F1-R1B — target carrier and admission

The next bounded subject should be one complete fourteen-field Fresh Schnorr
Core and its two-field Fresh Protocol. The gate must use:

1. the frozen target Interaction profile;
2. exact K1 value types, algorithms, evaluation contracts, semantic modules,
   and declaration references;
3. a complete Appendix A encoder, with all fourteen fields present even when
   a family is empty;
4. the complete target admission sequence, including exact-used module
   closure, type/ABI checks, scopes, bindings, occurrence backlinks,
   visibility, challenge/correlation policy, claim/terminal liveness, and
   unconditional fallback; and
5. at least one separately implemented body re-encoder or admission checker.

Required negative cases include missing and unused modules, wrong declaration
kinds, ABI mismatch, bad scope opening, stale occurrence backlinks, private
challenge influence, duplicated shared-challenge identity, dead claims,
terminal omission, and a missing unconditional fallback.

F1-R1B may reuse K1's constitutional encoding and value machinery and may use
K2 to derive test values or execution traces. It must not reuse K2's Core body,
profile bundle, or admission result as target authority.

The subsequent
[`F1-R1B target-admission result`](f1r1b-target-core-admission.md) executes this
gate for one complete finite Schnorr slice. It forms every target Core field,
authenticates exact dependencies, applies the ten applicable admission stages,
and requires the resulting offline admitted handle for Fresh formation. The
result is deliberately bounded: unimplemented target families return
`Unsupported`, and no current implementation authority or owner view is
claimed.

### F1-R1C — owner views and read closure

After target admission, implement the exact owner evaluator for
`PublicBindingView`, `StrategyDecisionView`, `PublicCoinView`, `EffectView`,
`ClaimReductionView`, and Protocol `ExecutionView`. The evaluator must derive
fields from one exact admitted target handle and return the target qualified
outcome partition. The offline research lane may reconstruct portable view
values, but it must not forge the live capability that F1-I later requires.

The F1-R0 protected-observation map then becomes a test of those owner outputs,
not a hand-authored source of semantic facts. Missing owner observability
reopens F0; ordinary encoder or evaluator absence is an implementation gap.

The subsequent
[`F1-R1C0 source-determinacy audit`](f1r1c-owner-view-source-determinacy.md)
classifies the present case as the former. The static-view prose is
profile-authenticated and names all six surfaces, but the published profile
does not expose the promised closed schema catalog, exact nested grammars,
field-to-law bindings, or complete authority-envelope bodies. F0-V must repair
that PIR-owned contract before an R1C evaluator can distinguish implementation
from invention.

### F1-R1D — integrated exact package

Only after R1B/R1C should the program add exact Relations definition/model/
instance and Protocol-correspondence roots, replace the F1-R0 manual bodies,
and require both checker paths to reproduce the complete target package. This
is the first offline candidate for the Q1 proposition shape, but Q1 remains
incomplete until F1-I binds exact live owner authority.

## 5. Main-design implications

The result argues against waiting for the entire semantic redesign. R1B and
R1C0 already exposed the carrier/admission and view-publication boundaries
while changes are still cheap. Work should continue sequentially on the shared
design branch through F0-V review, then resume R1C against the repaired source.

It also argues against jumping directly to VCVio or ArkLib. A provider can
help with Q2 and later theorem obligations only after the source side has an
admitted target subject and exact views. Otherwise a successful provider
proof can be attached to a recursively relabelled but unadmitted source.

No durable target semantic change was selected by F1-R1A or the subsequent
bounded F1-R1B result. F1-R1C0 now provides evidence that the target owner-view
publication contract requires a repair, but this research note does not select
its durable encoding or perform the resulting identity migration. The one
factual publication-page count corrected from seventeen to eighteen indexed
profiles remains documentation drift and does not change a profile preimage.

## 6. Assurance-lattice position

| Level | F1-R1A result |
|---|---|
| Q0 source admission | open for the target executable path |
| Q1 exact admitted-source reification | open; profile/source basis only |
| Q2 provider correspondence | not started |
| Q3--Q6 theorem environment, truth, applicability, property | not started |
| Q7--Q10 transition, transport, OIR, realization | not started |

## 7. Non-claims

- Source-shape extraction is not a complete body compiler or law parser.
- Independent profile reconstruction is not independent target admission.
- Typed IDs for relabelled data do not authenticate semantic admission.
- The gate does not establish live owner authority or mint a capability.
- No provider artifact, theorem, cryptographic property, Compiler
  preservation result, endpoint correspondence, or implementation support is
  established.
