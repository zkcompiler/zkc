# F0-V2B2C0 canonical-byte owner-admission substrate

This package tests the authority and immutability boundary required before the
constructor-isolation portion of F0-V2B2C can be trustworthy. It does not yet
extend target admission to Oracle, Reduction, or Module-effect constructors,
and it does not claim complete six-view projection.

Run from the repository root:

```sh
python3 -B evaluation/formal-source-owner-admission-f0v2b2c0/run.py --check
```

The frozen result is
`CannotAnswer/F0V2B2C0-C-CONSTRUCTOR-ISOLATION`. Its 22 findings contain ten
scoped affirmatives, one explicit `CannotAnswer`, five malformed-input
controls, three profile/kind mismatches, and three semantic refusals.

## Design result

The predecessor F1-R1B handle prevents serialization but is not immutable:
ordinary Python assignment can replace its retained `core_id`. B2C cannot
derive owner-authoritative views from a carrier with that property. The new
bounded topology is therefore:

```text
exact profiled Core bytes + asserted typed ID + exact dependency closure
  -> strict decode consuming all bytes
  -> byte-identical re-encode
  -> profile/body/ID authentication
  -> applicable ten-stage target admission
  -> immutable, noncopyable, nonserializable Core snapshot authority

exact profiled Fresh Protocol bytes + same authenticated closure contents
  -> exact profile and Core bearer checks
  -> immutable paired Fresh Protocol snapshot authority
```

The Core handle retains no mutable typed Core object, environment mapping, or
caller-owned collection. It contains bytes, tuples, one immutable closure
snapshot, and evaluator-local mint state. Ordinary assignment, shallow copy,
deep copy, and pickle all refuse. A test admits through mapping proxies backed
by caller-retained dictionaries, mutates those dictionaries after admission,
and confirms that the retained body and closure fingerprint do not change.

Fresh formation compares the authenticated closure snapshot contents rather
than requiring the identical Python `Environment` object. Consequently, a
freshly reconstructed environment with byte-identical profile, module,
algorithm, contract, and prior-meta preimages succeeds, while an environment
with a changed closure refuses. This better matches semantic identity than
process-object identity while retaining one evaluator and one live Core
authority.

## Independent structural path

`independent.py` imports only the Foundation datum model. It starts from the
profiled bytes, performs strict decoding and re-encoding, walks the datum with
an iterative worklist, and independently recovers:

- the selected profile reference;
- all fourteen Core field cardinalities;
- the exact Core-effect tag sequence;
- the Fresh Protocol's Core reference and interpretation tag; and
- the bounded datum node, edge, and depth measures.

It does not import the reference typed decoder. Both paths agree on the exact
baseline Core and Protocol snapshots. This is implementation diversity inside
one research package, not independent human review or a formal proof.

## Negative controls

The gate refuses truncated and trailing bodies, a body-authenticated unknown
Core field, a substituted asserted Core ID, request/body profile substitution,
a mutable predecessor handle used as authority, a Protocol over another Core,
an FS interpretation presented to Fresh admission, and a changed dependency
closure. Identity formation for the fifteen-field body is intentionally
allowed before owner formation refuses it; this preserves the distinction
between typed hashing and semantic admission.

## B2C1 handoff

B2C1 should extend the strict decoder and owner admission from these immutable
bytes, not restore a mutable host carrier. For each B2A isolation family it
must:

1. authenticate and admit one smallest positive Core;
2. retain every derived owner fact needed by the normalized views;
3. project all five Core views plus the paired Fresh `ExecutionView`;
4. separately decode the same canonical body and reproduce those values;
5. order sorted-unique view collections by exact target body bytes; and
6. refuse the named family discriminator.

B2C0 does not establish constructor-complete admission, owner-view equality,
PCGraph correctness, runtime semantics, profile publication, implementation
correspondence, theorem applicability, or a formal or cryptographic property.
