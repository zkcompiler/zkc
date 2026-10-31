# Compose a polynomial opening

[protocol.zkc](protocol.zkc) combines row commitments, the shared univariate
opening equations and FRI. It contains no native kernel calls or AIR dependency.
[main.zkc](main.zkc) selects the outer row commitment and transcript. FRI uses
`Direct<C::ValueField>` for its mathematical configuration; deployment selects
logical-oracle authentication independently of that outer commitment.

The prover commits a natural-order word before FRI challenges. It forms the
quotient `(f(X)-value)/(X-point)` and proves its degree is below four. The verifier
authenticates original rows at the exact positions returned by FRI and checks
that quotient equation against FRI's authenticated values. This bounds the
original polynomial's degree by four; a low-degree result alone does not check
the opening. Point seven is outside the selected evaluation coset.

```sh
zkc check --project=common/tests/fixtures/projects/polynomial-opening/zkc.toml
zkc prove example::Proof --project=common/tests/fixtures/projects/polynomial-opening/zkc.toml \
  --public=common/tests/fixtures/projects/polynomial-opening/inputs/example.Proof/public.json \
  --witness=common/tests/fixtures/projects/polynomial-opening/inputs/example.Proof/witness.json --output=opening.proof
zkc verify example::Proof --project=common/tests/fixtures/projects/polynomial-opening/zkc.toml \
  --public=common/tests/fixtures/projects/polynomial-opening/inputs/example.Proof/public.json --proof=opening.proof
```

`prepare.py` independently evaluates `1+2X+3X²+4X³` on the domain and creates
inputs. Parameters are small test parameters, the scheme is nonhiding, and its
proof encoding is zkc's. The example demonstrates composition and rejection
checks; it supplies no cryptographic security reduction.
