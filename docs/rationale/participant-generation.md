# A generated participant adds no communication and refuses when unsure

Both choices restrict how the compiler derives a participant from a protocol
under the [interaction rules](../spec/language/interaction.md).

## Generation does not add communication

If a generated participant does not already hold the information a step needs,
the compiler refuses.

**Rejected: insert a message or a released value so that generation succeeds.**
What each participant can observe is part of the protocol's meaning. Inserting
a value produces a different protocol from the one whose guarantees were
established, and knowing enough to perform an action is a different permission
from being allowed to reveal its result. Additional communication is written by
the protocol author, or produced by a separately stated transformation that
relates the new protocol's observations to the original.

**Reopen when** such a transformation exists together with that correspondence.

## Global choice requires an explicit projection rule

The [common-protocol profile](../spec/profiles/source/common-protocols.md) and
[scheduled lowering](../spec/profiles/compiler/scheduled-participants.md) admit
fixed public loops but exclude global dynamic choice. Local conditionals stay
inside their participant's algorithm. The separate
[shared-control reference check](../spec/profiles/source/located-execution.md#actual-agreement-for-shared-control)
checks actual guard/count agreement; it is not a global-choice projection pass.

**Rejected: infer communication or erase an uninvolved participant's guard.**
To project a global choice, a participant must know its branch, have equivalent
continuations on both branches, or recover the choice through an explicit
communication rule. Availability alone is only one sufficient criterion; its
failure does not show that the protocol is impossible to implement.

**Reopen when** a concrete client needs global choice and supplies the control,
merge and observation laws for its projection. That extension must state how
branch information reaches each affected participant.
