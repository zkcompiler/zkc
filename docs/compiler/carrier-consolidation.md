# Current interactive carrier

The executable interactive carrier is `zkc.protocol/1` followed by
`zkc.participants/1`. It carries nominal logical types, declared operation
bindings, implementation selection and logical function origins. C++, Rust and
Lean admit this carrier independently. This is an implementation decision under
the existing selected model, not a new refinement or cryptographic theorem.
The finite source/table carrier and its independent checks retain their scope.

## Authoring and admission

Text modules headed `arkworks.multilinear.bls12-381/1` or
`arkworks.bls12-381/1` are BLS authoring conveniences. The text parser elaborates
them into explicit declarations before semantic admission, construction, MLIR
import or execution; the carrier never names a profile. A module header naming
any other profile is refused as `source-profile`. Ordinary `module { ... }`
explicit/generic authoring is unchanged. Unknown syntax can still be
parsed/formatted where structurally valid; formation rejects unknown
types/contracts at admission.

| Short type/operation family | Explicit identity or selection |
|---|---|
| `field`, `table`, `point`, `round`, `rng`, `nonce` | `bls12-381.fr` |
| `group`, `groups` | `bls12-381.g1` |
| PCS values and `pcs.*` | `multilinear.kzg.bls12-381/1` |
| `transcript` and `transcript.*` | `merlin3.bls12-381.fr64be/1`; observations also carry payload identity and codec |
| `curve.*` except `curve.response` | G1 operation argument |
| `curve.response` | Fr operation argument; nonce remains an atomic affine resource |
| Implementations | Actual `arkworks/<contract>` installation |

The table describes recognized short types in their respective heading.
A module heading is not a PCS scheme identity. Reference-group public scalars
are not BLS G1 points. The [group exchange](../../examples/protocols/group-exchange.pir)
uses actual G1 operations and retains nonce consumption.

The current carrier provides no compatibility guarantee for earlier profile-based
transcripts, artifact digests or proofs. Current artifact results, inputs,
configuration, primitive requests and observations each use their documented
form; a shared version suffix does not imply compatibility across carriers.

Elaboration retains instruction order, sites, source locations and loop counts.
It inserts declarations, not executable operations, and gives each function its
logical origin. Generated binding symbols avoid authored top-level names.
This is a defaults notation; it is not the former profile-specific allowlist.

The carrier's second field lists explicit bindings. A profile string in that
position is malformed (`interactive-shape`). The current readers admit only
this shape, and the MLIR module has no profile attribute.

## Evidence and reference material

Current BLS examples include two-factor, committed-two-factor, DLEQ and
supplied-participant execution.
Abstract opaque types and correlated capability interfaces have no automatic
nominal implementation in this carrier.

Tests preserve malformed admission, distinct stopped outcomes, completed resource
transitions, unaffected resources, session/origin separation, wrong setup
selection and fixed-budget boundaries. The real curve tests replace scalar-group
simulation for executable exchange evidence; mock arithmetic remains labeled as
mock arithmetic. The independent Lean reference is not generated from Rust or
C++ contract tables.

## Integration boundary

Source inspection, claim checking, MLIR import/export, construction and native
dispatch consume explicit nominal bindings. Primitive requests identify their
actual contracts, types and codecs; profile-tagged requests are refused.

Direct native-backend construction with trusted input keys and construction with
an authorized setup registry remain distinct host policies. Neither changes
source semantics or reinstalls a profile interpreter. BLS resource convenience
methods select fixed documented nominal domains and use the same capability
store as their explicit-domain counterparts.

The finite table evidence carrier retains its own checkers and does not act as
an execution fallback for an unsupported interactive carrier.
