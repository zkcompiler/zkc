# Native message relay

This layout-source package exports `zkc::relay::{Relay, NativeRelay, Forward}`.
`Relay::pass` transports one complete ordinary payload from its first role to
its second. `NativeRelay` implements that interface with the default native
send. `Forward<T, C>` selects any module conforming universally to `Relay`.

Every abstract and forwarding contract requires the installed
`zkc::transport::NativeMessage(T)`. It checks external construction, installed
message support and a nonempty complete source-native carrier, together with
ordinary executable category formation. Copy/Drop remains separate; this
forwarding API requires neither permission.
There is no descriptor argument or source-defined native permission.

A layout-source project can depend on this leaf's `zkc.toml` and write:

```text
use zkc::relay::{Forward, NativeRelay}
pub protocol Demo roles(P, V)(x: bool @P) -> bool @V:
    y <- Forward<bool, NativeRelay>(x) @(P, V)
    return y
```

Transparent ordinary records are also supported. Unit, empty source products,
private/sealed/opaque representations and unsupported native message heads
refuse. A zero-cardinality installed carrier with a native frame is distinct
from an empty source layout. This package supplies no custom codec, proof of
honest behavior, statement authority or secrecy theorem. The owning
[requirement contract](../../../docs/spec/language/definitions.md#installed-consumer-requirements)
and [native message format](../../../docs/spec/formats/messages.md) define its
limits. Compiler controls cover source replay and universal conformance;
[Host tests](../../../common/tests/protocol/test_consumer_requirements.py)
execute Boolean and transparent record clients.
The [implementation status](../../../docs/status.md#installed-native-message-source-requirements)
records the supported layout-source API inspection and execution scope. Pending
assurance in inspection output is authored intent, not a proof receipt.
