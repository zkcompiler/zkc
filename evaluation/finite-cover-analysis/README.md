# Checked finite-cover Analysis instrument

This package activates one exact finite-cover discharge in the bounded
Analysis reference model. It is an executable research instrument, not a proof
assistant artifact or a generic Schnorr security result.

The selected subject is the repository's fixed Schnorr fixture with
`(p,q,g,Y)=(23,11,2,8)` and challenge set `{0,...,7}`. Its raw transcript-pair
carrier contains eight `Nat64` leaves and admits noncanonical commitment and
response encodings. The instrument therefore checks a verifier-observation
quotient rather than pretending that canonical fixture values exhaust the raw
carrier.

The package contains three intentionally separate components:

1. `portable_arithmetic.py` defines an ordinary Foundation semantic module for
   exact natural modular arithmetic, four authenticated portable algorithms,
   a universal quotient-factorization basis checker, and a focused
   evaluator/provider. The module does not extend the root semantic profile.
2. `independent_oracle.py` reconstructs the 308 representatives, canonical
   stream bytes, digest, and extractor outputs without importing either the
   portable implementation or the Analysis model.
3. `tests/test_finite_cover.py` checks the portable path, noncanonical quotient
   behavior, evaluator failure partition, ordinary hypothesis-free Analysis
   judgment, the distinct coverage/factorization/success-transfer boundary,
   exact operation binding, Nat64 boundary falsifiers, and stream/candidate
   mutations.

The finite stream exhausts the 308 accepted quotient representatives. The raw
`Nat64` universal is not inferred from a few lifted examples: a separate
quotient-factorization certificate authenticates the exact raw predicate,
normalization, embedding, candidate operation, and the algebraic periodicity
and invertibility facts that make the lift universal. Large noncanonical values
remain bounded falsification cases only.

The statement and challenge normalization legs use moduli 9 and 8 because
those are exactly one above their canonical maxima 8 and 7. The raw predicate
pins both coordinates before normalization, so these legs are checked narrowing
maps rather than periodicity assumptions. Tests pin the four portable-algorithm
identity digests in addition to the stream digest; changing any operation is a
deliberate fixture rotation.

The exact checked conclusion is only that the selected response-difference
portable extractor succeeds on every member of this one exact bounded pair
domain. The result does not establish generic special soundness, extractor
efficiency, asymptotic behavior, knowledge soundness, Fiat--Shamir security,
ROM security, or QROM security.

Run the bounded gate with:

```bash
python3 evaluation/finite-cover-analysis/run.py --check
```
