# Indexed product family

This application represents the polynomial `product(coordinates) + firstCoordinate`
over a commutative ring, with public dimension at least one. It retains an indexed
equation source in addition to the library's fixed-polynomial structured source.

- `Basic` proves honest round equations and Boolean summation for arbitrary dimension.
- `Expressions` gives coefficient/challenge references and their occurrence map.
- `Indexed` connects all round checks and the original terminal target, for arbitrary
  environments. `Locality` proves prefix and value-reference dependence and an
  online honest construction.
- `Typed` constructs typed checks and proves their lowering has exactly that meaning.
- `Wire` maps the check-bearing source coordinates to the scalar message schedule.

These are mathematical source and interpretation laws. They do not prove that a
native parser extracts those coordinates correctly. The actual ArkLib wire/verifier
adapter is an optional integration consumer. The broader structured Sumcheck source
uses its own fixed polynomial and terminal definition; no equivalence between these
two complete representations is asserted without an explicit correspondence.
