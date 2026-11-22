module

public meta import Lean

public meta section

/-!
The labels by which a library and a module of statements tell the walk what it may use.

They are registered apart from the walk so that a library that states a law of reads does not
import the walk.
-/

/-- **A law of a read.** A theorem `premises → xs[i]? = some value` (or `= none`): what a read
of a sequence at a position finds, where the premises hold. A walk that waits on a read uses the
labelled laws: it rewrites the read by them, proves each premise by a hypothesis that states it
or by arithmetic on the hypotheses, and goes on with the value when the read is then a value
found. A read that no law decides is split into its two forms, as any value that a step waits
on. -/
register_label_attr walk_read

/-- **How a value of a model reads.** An equation between an operation of a model and what it
is in the mathematics: that the addition of the arithmetic model over a field is the field's.
Where a walk stops at a goal that judges no process (the end of a program, the law of a
computation, the weight of an excluded set), the goal and the hypotheses are rewritten by the
labelled equations, so that a text finishes with the mathematics of its field and names no
operation of a model. -/
register_label_attr walk_value

/-- **The cap of a site.** A theorem `table.capFrom place applications site = value`, which a
module of statements proves for each charged draw of its root. Where a text pays a fee at such
a draw, the fee is compared with the value, and a fee that is not within it is refused with the
name of the site. -/
register_label_attr walk_cap

/-- **A judgment that reads no peer.** A theorem `Blind ρ judgment` (`Zkc/Formal/Application.lean`)
for every renaming `ρ` of roles: the judgment of an effect does not change when the peers of
the effect are renamed. Under a judgment for which a labelled theorem says so, a walk goes into
an application of a protocol: the callee's program, whose peers the application renames, is
judged as it stands. -/
register_label_attr walk_blind
