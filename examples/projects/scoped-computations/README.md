# Scoped computations

Callback parameters use `fn(...) -> ... effects(...)` for Local computation or
`math fn(...) -> ...` for total Math computation. The compiler selects each
callback statically; callbacks cannot escape into runtime data.

This [Entry](main.zkc) uses ordinary generic user combinators from
[`zkc::computation`](../../../libraries/zkc/computation.zkc). A component forwards a nested
Local callback that retains lexical access to its `adjust` member. The
protocol callback captures two record projections and an index; the checked
vector read executes inside the callback. Its P-only captures select P as the
owner even though the ordinary input is shared with V.

With `shared = 3`, `parameters = {shift: 7, table: [5]}`, and `position = 0`,
the result is 16. An out-of-range position preserves the normal checked-read
failure and publishes no completed result.

```sh
zkc check --project=examples/projects/scoped-computations/zkc.toml
zkc compile --project=examples/projects/scoped-computations/zkc.toml \
  example::Demo --output=scoped-computations.zkpkg
```

Scoped computations have fixed Math or Local signatures and cannot escape a
call. Runtime captures become explicit data inputs of private helpers. No
runtime function value or closure instruction is emitted. This example has no
finite domain or fold syntax; it demonstrates their shared callback foundation.

See [the language contract](../../../docs/spec/language/definitions.md#scoped-computations)
and [native integration controls](../../../common/tests/protocol/test_scoped_computations.py).
