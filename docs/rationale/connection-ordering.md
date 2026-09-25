# A connection between components keeps the order of shared events

When two components each establish a local statement about shared data, the
[relation that connects them](../spec/properties/relations.md#component-connections)
carries the information that fixes the order in which the shared events
happened. Each compared element carries its position, and the map from
positions and events into the compared representation is injective across the
whole admitted domain.

## Alternatives

- **Compare the unordered collections of shared events.** Two components can
  each accept a locally consistent history while the two histories together
  describe an execution that the shared object cannot perform. In the memory
  example one component reads a value before the other writes it, the two
  collections are exactly equal, and the connection accepts a public statement
  that the original machine makes impossible.
- **Reduce positions into a smaller domain.** An arbitrary natural timestamp
  cannot be injected into one finite field. Reducing addresses or counters
  without a range and injectivity argument lets two distinct histories collide.

This is not a defect of a particular comparison technique. It is a requirement
on the fields and local conditions that the comparison consumes. A larger
domain needs a larger representation or a separately analyzed random compression.

## Reopen when

A component family has a statement that provably does not depend on order, or a
compressed encoding is proved injective over the admitted domain. In the second
case that encoding may replace the explicit positions.
