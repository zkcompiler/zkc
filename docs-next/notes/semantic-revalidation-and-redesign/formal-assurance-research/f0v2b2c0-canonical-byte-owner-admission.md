# F0-V2B2C0 Canonical-Byte Owner Admission

> **Kind:** Temporary reopened-F0 owner-admission and authority-design result
> **State:** Complete at admission-substrate resolution with
> `CannotAnswer/F0V2B2C0-C-CONSTRUCTOR-ISOLATION`; the selected substrate
> passes, while extended constructors and complete projection remain B2C1
> **Authority:** None. This note and executable package do not change PIR,
> the published Interaction profile, an evaluator, compiler, runtime, or
> Analysis judgment
> **Predecessor:**
> [`F0-V2B2B constructor-complete schema`](f0v2b2b-constructor-complete-schema-and-inhabitance.md)
> **Executable gate:**
> [`evaluation/formal-source-owner-admission-f0v2b2c0`](../../../../evaluation/formal-source-owner-admission-f0v2b2c0/README.md)

## 1. Decision

B2C must not extend the F1-R1B handle unchanged. The executable probe confirms
that F1-R1B's `AdmittedCore` is nonserializable but ordinarily mutable: its
`core_id` slot can be reassigned after admission. A projection that reads that
object has a time-of-check/time-of-use gap and cannot be described honestly as
an immutable owner projection.

The selected B2C substrate starts from canonical bytes instead:

```text
CanonicalCoreCandidate {
  asserted CoreId,
  exact Interaction profile ID,
  complete profiled body bytes
}
  -> strict Foundation decode and exact re-encode
  -> exact profile/body/ID authentication
  -> target owner admission
  -> AdmittedCoreSnapshot {
       exact Core/Profile references,
       profiled and domain bytes,
       immutable authenticated closure snapshot,
       retained bounded owner summary,
       exact evaluator fingerprint
     }
```

The live authority is noncopyable and nonserializable, but those properties
are no longer substitutes for source immutability. Its semantic input is the
retained byte snapshot. No caller-owned Core object or map is consulted after
admission.

Fresh formation receives the exact live Core snapshot and independently
authenticated environment contents. It requires profile equality, the exact
Core reference in the Protocol body, Fresh tag 0, equal dependency-closure
fingerprints, and the same evaluator fingerprint. It does not require the same
Python environment object. This permits cold reconstruction from equal
canonical preimages without weakening bearer authority.

## 2. Why B2C is split

The B2B entry contract combined two qualitatively different questions:

1. can an authenticated owner be retained without mutable-host aliasing; and
2. can every missing constructor be admitted and projected correctly?

Testing both only inside twenty-one constructor fixtures would let an
authority defect contaminate every result and make failures hard to localize.
B2C is therefore refined, without changing the B2A pressure census, into:

```text
B2C0  canonical-byte intake, immutable authority, exact bearer pairing
B2C1  isolated extended admission and dual six-view projection
```

This is not a new semantic stage or top-level owner. Both are temporary
falsifiers for the existing PIR admission and static-view lifecycle.

## 3. Executable result

The package matches 22/22 findings:

| Outcome | Count |
|---|---:|
| `Affirmative` | 10 |
| `CannotAnswer` | 1 |
| `Malformed` | 5 |
| `KindMismatch` | 3 |
| `Refused` | 3 |

The affirmative results establish only this bounded substrate:

- the exact F1-R1B Core consumes and re-encodes all profiled bytes;
- its currently applicable ten admission stages still pass;
- a second iterative parser reproduces the profile, fourteen field counts,
  effect tags, Fresh interpretation, and exact Core bearer;
- the new Core and Protocol authorities refuse ordinary assignment, copy,
  deepcopy, and serialization;
- mutating caller-retained backing dictionaries cannot mutate their retained
  closure snapshot; and
- byte-identical closure reconstruction succeeds while closure substitution
  refuses.

The negative controls preserve typed identity formation as distinct from owner
formation. In particular, Foundation can identify a canonical fifteen-field
record as kind `pir.interactive-core`; the target owner then rejects its extra
field as `Malformed`. A typed digest is not admission authority.

## 4. Design consequences for the main model

The ideal target lifecycle should state four separate objects explicitly:

```text
serialized candidate bytes
  -> authenticated candidate
  -> admitted immutable owner snapshot
  -> fresh purpose-bound view capability
```

“Nonserializable” addresses transfer of a live bearer. “Immutable snapshot”
addresses semantic stability after admission. “Content-equivalent closure”
addresses cold reconstruction. “Identical capability object” addresses a
particular delegated use. None implies another.

The current target prose already says that an admitted handle retains the
canonical body and that serialization is not the handle. B2C0 suggests making
the canonical byte snapshot, alias-freedom, and closure-content comparison
normatively explicit when the redesign is next edited. It does not edit that
target from this research note.

## 5. B2C1 entry contract

B2C1 inherits all twenty-one B2A pressure families assigned to B2C. Each
family needs one minimal authenticated Core and one named discriminator. The
reference path should project from admission-retained owner facts. The cold
path must start again from `AdmittedCoreSnapshot.domain_body`, strictly decode
it through a separately structured parser, and independently derive the same
six values.

Both paths must use exact target body encodings for every sorted-unique set.
B2B's JSON wire was only a diagnostic inhabitance order; it is not eligible as
the B2C ordering oracle. If exact target order conflicts with the B2B JSON
validator's order, B2C must use the target order and report the diagnostic
validator as inapplicable rather than reorder semantic data to satisfy it.

B2C1 must also distinguish:

- owner admission from Fresh-versus-FS eligibility;
- stored Core fields from derived owner facts;
- an authenticated module effect from an opaque arbitrary payload;
- per-family graph facts from B2D's integrated graph closure; and
- two implementations in this package from machine-checked proof or
  independent review.

## 6. Non-claims

B2C0 does not admit a previously unsupported target constructor, derive one of
the normalized six B2B views, establish owner/source correspondence, validate
the complete `PCGraph`, execute an Oracle or Protocol, publish or migrate a
profile, verify current implementation correspondence, prove a theorem, or
establish a cryptographic property. The overall result remains
`CannotAnswer` until B2C1 closes constructor isolation and dual projection.
