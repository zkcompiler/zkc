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

/-- **The cap of a site.** A theorem `table.capFrom place applications site = value`, which a
module of statements proves for each charged draw of its root. Where a text pays a fee at such
a draw, the fee is compared with the value, and a fee that is not within it is refused with the
name of the site. -/
register_label_attr walk_cap
