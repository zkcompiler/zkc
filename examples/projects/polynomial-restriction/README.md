# Coefficient restriction

`Restriction` calls the shared bilinear coefficient helper, reduces four
coefficients to two, evaluates the result at an arbitrary future field point,
and returns the caller's frame unchanged. This is a bounded mathematical helper
example, with no proof-system or cryptographic claim.

The checked source binding is
`lean/ZkcExamples/Structured/PolynomialRestrictionBinding.lean`. The security
library adapter in `ZkcSecurity.Examples.PolynomialRestriction` proves update
simulation, closure, all-future evaluation and reuse of the existing Sumcheck
round law. Its negative control distinguishes agreement on Boolean vertices
from agreement at arbitrary field points. The generated body equation preserves
the complete source caller, including ordered observations and private returns.

From the repository root, regenerate constructor data and exact bodies with:

```sh
python3 lean/bridges/structured/generate_polynomial_restriction.py \
  --compiler build/compiler/zkc-compile --check
```

Omit `--check` to update generated files. The command uses the shared snapshot
and body printers and builds only the source-data dependency it needs. The
maintained core and security package builds check the mathematical and binding
modules; native field/runner correspondence is outside this example's theorem.

Check the source declarations from this project directory:

```sh zkc-example
zkc check
```
