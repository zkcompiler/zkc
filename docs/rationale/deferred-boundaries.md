# A deferred capability still fixes its boundary when postponing would be costly

The [architecture](../architecture.md) resolves a boundary in the first
implementing component when a later change would alter how source and plans are
written across more than one language, discard information that nothing else
retains, move ownership of a resource, or change what an existing conclusion
means. Everything else stays open.

## Alternatives

- **Decide every later capability now.** It blocks delivery on work with no
  current consumer. Additions that fit contracts already in place need only an
  extension point: more search strategies, more proved local rewrites, another
  implementation of the same backend contract, another front end producing the
  same source.
- **Defer every later capability entirely.** A boundary is then fixed by a
  component that never exercised it. Choices that a defined boundary forces are
  settled by its first real user, before anything depending on it is fixed: the
  exact source form and its reader, the field representation, the capacity
  calculation, the granularity of backend work, the choice of extraction route.
- **Treat a new meaning as an addition.** Concurrent intervention, unbounded
  repetition, stronger observers, specialization on private values, changed
  message or challenge structure and correspondence for generated code each need
  a new meaning or a new assurance argument. They are recorded with the property
  wanted and the obstacle, and are not prerequisites for the current delivery.

Demonstrating a boundary means exercising the promised extension without
rewriting the generic binding, sequencing or checking machinery. It does not
require a second complete protocol or a second backend. Refusing an unsupported
case shows that the existing meaning is protected, not that the new case is
supported. A described interface is not evidence.

## Reopen when

The first real user of a boundary shows that an intended extension needs a
different binding, ownership or evidence model. The boundary is revised before
anything depending on it is fixed.
