# Aliased private service control

`AliasedAnd` passes the same private random service to both parameters of
`Borrowed`, then uses that service in the Schnorr conjunction. This exercises
root identity through helper calls: parameter names do not create independent
random resources. It is a formal aliasing control, not a new proof system.

Check the source declarations from this project directory:

```sh zkc-example
zkc check
```

See the source and construction bindings in
`lean/ZkcExamples/Structured/Generated/Bindings/SchnorrAndAliasedData.lean` and the security controls
in `lean/security/TestsSecurity/`. The check above establishes source admission,
not independence of draws or a cryptographic security bound.
