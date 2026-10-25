# Exact table queries and an AIR control

This [project](zkc.toml) selects KoalaBear and the
[explicit-table library](../../../libraries/relations/table/README.md).
`Membership` constructs masked queries and invokes a protocol whose selected
relation binds the actual verifier table, queries and acceptance result.
`Direct` evaluates the same predicate without a protocol or AIR consumer.
`IndexedRead` preserves exact coordinate identity.

Run these commands from this project directory with built tools on `PATH`:

```sh zkc-example
zkc check
zkc inspect --view=api
zkc run Direct
```

The included `inputs/example.Direct/arguments.json` selects two equal active
queries against one row; the returned result is true.

For `Direct`, ordinary arguments are `table` and `values` as arrays of field
strings, and `active` as an array of Booleans. For example,
`{"table":["1"],"values":["1","1"],"active":[true,true]}` returns true:
two queries may reuse one row. Changing the table to `["2"]` returns false.
Changing both flags to false returns true. Unequal query and mask lengths stop.
The integration tests compile the project and run these cases through the
current CLI, typed Host, numerical programs and VM.

`InteractionControl` retains the same membership application and separately
returns the existing AIR reciprocal-residual test result. In the KoalaBear
field, use table `[1,2]`, queries `[0,0]`, both active, and `gamma = 4/3`.
Supply reciprocals of `gamma - value` for the two queries followed by the two
table rows. Every denominator is nonzero and:

```text
2/gamma = 1/(gamma - 1) + 1/(gamma - 2)
```

The interaction equation returns true while membership returns false. Changing
one reciprocal makes the interaction equation false. This is an executable
boundary check: exact evaluation of that verifier equation does not establish
membership at an arbitrary fixed challenge. A complete randomized argument
needs its commitment, challenge-ordering, multiplicity and security laws.

The [tests](../../../common/tests/protocol/test_table_relations.py) also cover
empty inputs, changed masks, duplicate table rows, exact indexed reads and
reached malformed selection descriptors. Existing Entry controls separately
check skipped callbacks, stop prefixes and failed-result withholding.
