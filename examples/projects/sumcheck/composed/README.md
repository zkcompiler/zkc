# Composed Sumcheck

[TwoSums](protocol.zkc) calls the library's `Reduce` twice and checks each
returned evaluation against its corresponding public table. This is ordinary
protocol composition; neither the compiler nor the runtime knows TwoSums.
[Entries](main.zkc) select a field and a construction separately.

From this directory, with built tools on `PATH`:

```sh
zkc prove
zkc verify
```

The single proof Entry uses the supplied public inputs. `Interactive` runs the
complete protocol; `Reduction` exposes one reduction's role-local result for
inspection. Its `variables` input describes the original table; `rounds` can
select a shorter prefix. Library callers retain the checked residual view for
further reductions; this inspection Entry exports its raw values. Select the desired run Entry explicitly when preparing inputs with
`zkc prepare` or invoking `zkc run`.

A reduction returns an obligation, not acceptance. `check` folds the verifier's
own table in MSB-first coordinate order and requires exactly one matching value.
Using the wrong table or leaving a nontrivial residual dimension cannot satisfy
this complete client. The example makes no hiding or security-theorem claim.
