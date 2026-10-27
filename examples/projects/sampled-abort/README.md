# Sampled abort control

This formal control samples a private value and can stop before sending its
message. Its acceptance flag does not establish the declared equality target.
It exercises source occurrences, aborts and the need for a separate soundness
argument; it is not a secure equality protocol.

Check the source declarations from this project directory:

```sh zkc-example
zkc check
```

The corresponding formal construction and negative controls are in
`lean/ZkcExamples/Structured/Generated/Bindings/SampledAbortData.lean` and
`lean/security/TestsSecurity/SampledRootClaims.lean`. Source admission alone does
not discharge their security obligations.
