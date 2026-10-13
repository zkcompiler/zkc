# Lookup denominator products

This arithmetic component evaluates an AIR lookup or permutation denominator
product at two supplied shifts, `gamma` and `other_gamma`. For a vector of
already compressed tuple fingerprints and one uniform batch gate, each output is

```text
initial * product(gate * (shift - fingerprints[i]) + 1 - gate).
```

The private generic helper collects factors using the existing
[`air_interaction::gated_denominator`](../../../libraries/air/interaction.zkc),
then multiplies them with an indexed total fold. Both consumers read through
ordinary helpers with explicit `in_bounds` premises. Domain indices establish
each bound on its original container. The same helpers serve both shift calls;
arguments are reordered and a helper forwards both the shift and loaded value.

For Boolean `gate`, one selects all rows and zero makes every factor one,
including rows whose raw denominator is zero. An empty batch returns `initial`.
An active zero denominator returns zero; this arithmetic component performs no
inversion or nonzero admission. It does not enforce Booleanity, authenticate
fingerprints, prove a multiset equality or construct an AIR proof. A complete
protocol must supply those checks and may need a separate gate per row.

With built tools on `PATH`, run from the repository root:

```sh
zkc run --project=examples/projects/lookup-denominators/zkc.toml lookup_denominators::Demo
zkc run --project=examples/projects/lookup-denominators/zkc.toml lookup_denominators::ExtensionDemo
```

`Demo` uses KoalaBear; `ExtensionDemo` uses KoalaBear Ext8. The supplied
[base-field inputs](inputs/lookup_denominators.Demo/P.json) return `product = 0`
and `other_product = 120`. Changing `gate` to zero returns `2` for both. The
[extension inputs](inputs/lookup_denominators.ExtensionDemo/P.json) exercise
nonzero extension coordinates.

The [integration tests](../../../common/tests/protocol/test_indexed_callback_selection.py)
compare independent arithmetic in both fields and all four combinations of
simplification and finite bulk selection. They inspect executable vector
arithmetic and product sites separately from output values. See the
[finite library guide](../../../libraries/README.md#finite-computations).
