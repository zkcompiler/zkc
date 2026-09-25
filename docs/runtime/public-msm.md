# Public-operand Ristretto MSM

`dalek-vartime/curve.msm` is an explicitly selected dense implementation of
`curve.msm(ristretto255.group)`. The default remains `dalek/curve.msm`, using
Dalek's scalar-constant-time `MultiscalarMul`. There is no automatic selection
by participant name and no combined verification equation or transcript change.

The installed mathematical signature is unchanged:

```text
vector:ristretto255.scalar@dalek.scalar-vector/1
× groups:ristretto255.group@dalek.ristretto-vector/1
→ group:ristretto255.group@dalek.ristretto/1
```

Its additional implementation precondition is that **both scalars and points
are public**. The pinned `curve25519-dalek` 4.1.3
[`VartimeMultiscalarMul`](https://docs.rs/curve25519-dalek/4.1.3/curve25519_dalek/traits/trait.VartimeMultiscalarMul.html)
implements `sum_i scalars[i] * points[i]`, including the identity for empty
inputs. The adapter invokes this existing upstream implementation directly.
No serial fallback, new dependency, diagonal representation or algebraic fusion
is installed.

The intended conditional [refinement](../spec/verification/refinement.md) keeps
operand order, nominal types, canonical result encoding, retained-value charges,
source checks, and protocol/transcript actions fixed. Equal-length validation,
input value/element/group ceilings, and the 512-byte output allowance run through
the existing dense path before either MSM. Unequal lengths still return
`refused:length-mismatch`; insufficient output capacity still returns
`exhausted:output-bytes`. Malformed compressed points fail the existing canonical
wire decoder. Wrong domains, contracts and representations fail binding or
operand admission. Dense and public results have the same value type and charge.

The observation relation compares ordered semantic requests, replies, checks,
stops, messages and transcript values. If an observer records physical
implementation identities, project only this implementation choice to its logical
`curve.msm` operation. Full physical trace equality is not asserted. Clock time
and upstream scratch allocation differ; current retained-value accounting does
not measure Dalek's temporary heap. External allocation failure or universal
machine-level resource behavior is not covered by the bounded tests.

## Explicit host authority

Every `NativeBackend` constructor starts with an empty `PublicRolePolicy`.
`with_public_role_policy(PublicRolePolicy::new(roles)?)` accepts a caller-owned
assertion that the listed roles' operands and observable resource outputs are
public in this backend's entry/session. Policies contain at most 64 exact names
of at most 256 bytes, with no wildcard interpretation. `EntryPolicy` and affine
resource custody still apply. Before executing the selected kernel, the backend
checks the actual active `Frame.role()` against that policy; absence returns
`refused:public-operands-required`, even for an empty MSM.

An ordinary interactive host, including one with a participant named `V`, grants
nothing by default. A Rust caller can explicitly assert publicness; that assertion
is a trust premise, not evidence that an arbitrary interactive source has public
inputs. Native signature advertisement admits mathematical types independently
of this per-invocation leakage premise.

The artifact host derives the grant from its checked public artifact profile:

- Every serializable input of the descriptor-selected validator is public-bound.
- Verifier keys are bound to checked public configuration; its only other original
  resource is the selected RNG, issued with zero draw budget. Its hidden seed is
  inaccessible to scalar operations; it cannot yield secret operands.
- Original source signatures cannot introduce transcript resources. Exactly one
  fresh transcript is initialized from the checked public source/descriptor,
  application context, public inputs and key configuration. Transcript outputs
  are deterministic functions of those roots and public proof messages.
- The prescribed construction and actual physical candidate are checked before
  use. Received prover values come from public proof bytes. The finite installed
  operation catalog has no other ambient source of private scalar values.

`Admitted::executable_implementation_roles(entry)` walks actual admitted
participant calls and local functions. Before input loading, resource issuance
or proof access, artifact admission rejects a restricted implementation reachable
by any role other than that selected validator, with
`artifact-public-implementation-role`. Shared functions are attributed to every
role that reaches them. Fixed zero-trip loop bodies and exclusively unreachable
callees are omitted, matching executable receiving-port semantics; other loops
are traversed once without unrolling. Reachability remains conservative after
checks or stops. There is no application-name or source-generator matching.
Successful binding grants only the descriptor-selected validator, even if its
name differs from `V`; the producer never receives a grant.

This is a finite public-artifact argument about ordinary operands and observable
resource outputs, not a general secrecy lattice. Expanding the installed catalog
with ambient secret state or introducing new resource kinds requires revisiting
this argument.

## Evidence boundaries

C++, Rust source resolution, native advertisement and Lean independently admit
this exact mathematical binding and reject other domains/contracts. Lean checks
actual-candidate correspondence; it does not prove the native timing/leakage
property or Dalek's implementation. Finite tests compare canonical outputs,
malformed inputs, output budgets, reached roles, and semantic observations.
Neither constant-time behavior of the whole runtime nor production zero knowledge
follows. Application claim contracts retain their own body/cryptographic trust
premises. Kernel microbenchmarks do not establish a whole-application speedup.
