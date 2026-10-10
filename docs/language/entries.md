# Selecting an Entry

A `protocol` defines the interaction. An Entry closes its static parameters and
selects how an application invokes it. The [declaration contract](../spec/language/entries.md)
owns the exact syntax and checks.

```text
run Demo = Transfer;
```

This selects a joint run. A `proof` Entry additionally chooses prover, verifier,
public inputs, acceptance and either derived or authored construction. See the
[Schnorr project](../../examples/projects/README.md) and the
[source guide](mathematical.md) for complete declarations.

Setup slots associate input selectors with application-owned key identities.
`complete result.ready;` selects a producer Boolean used by bounded attempts.
A complete same-kind Entry alias inherits the entire configuration. None of these choices
creates an application or embeds host filesystem paths in the protocol.

The compiler publishes the closed source, interface and selected artifact in an
[Entry package](../spec/formats/entry.md). Applications authenticate that
package and supply actual values through the common Host. Continue with
[running Entries](../runtime/entries.md) for CLI use and Rust integration.
