# Native pointwise maps

The [Entry](main.zkc) writes row formulas as ordinary `math fn` helpers and
applies them to whole columns with
[checked `map`](../../../docs/spec/language/definitions.md#checked-pointwise-maps).
The compiler realizes each map with a fixed number of checked vector operations;
the artifact does not grow with the number of rows.

`Check` gives V four public KoalaBear columns. Each row satisfies a selected gate:
`output = left * right` where `selector` is one and `output = left + right` where
it is zero. V maps the gate residual over the columns and accepts when every
residual is zero. Unequal column lengths fail the map's shape check before any
arithmetic; the run ends incomplete instead of reporting a rejection.

`Interactive` shares two Ext8 columns between P and V. V draws a challenge `r`
and sends it to P, which returns `map combine(each left, each right, r)`, the
column `left + r * right`. V recomputes the same column and compares it with the
received one. The challenge is a scalar shared by every row.

From the repository root, with built tools on `PATH`:

```sh
zkc compile \
  --project=examples/projects/native-map/zkc.json \
  --entry=example::Check --output=native-map.entry
```

The [integration tests](../../../tests/protocol/test_native_map.py) supply
satisfied, changed and unequal-length columns through the common Host. These
are public-column examples: they make no commitment, hiding or soundness claim.
