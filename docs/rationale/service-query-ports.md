# Service queries use separate participant ports

The [native service profile](../spec/profiles/compiler/native-services.md) keeps
references typed in common SSA, then projects them to named endpoint ports and
explicit query instructions. The native service profile binds references only at entry;
no operation produces or dynamically selects a reference. Ports express that
contract directly and avoid extending every ordinary value and physical-type
consumer for values that cannot flow through those consumers.

## Alternatives and reason

A separate copyable reference value could also preserve affine-token discipline;
it is not inherently unsound. It becomes useful when service-bearing composition,
dynamic selection or reference results require ordinary value flow. Those are
concrete reasons to revisit the port representation. For the current contract,
separate ports keep the admission and runtime changes smaller and expose each
query to the scheduler. Outlining queries inside ordinary local functions would
hide those cuts and mix pure helper execution with service interaction.

## Reopen when

Revisit when service-bearing composition, dynamic selection or reference results
require ordinary value flow with a concrete consumer.
