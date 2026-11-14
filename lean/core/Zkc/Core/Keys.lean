module

public import Zkc.Core.Raw

public section

/-! Keys: what names a site and a program point, apart from its number.

A site number and the path of a block are made by whoever writes a raw program, and change
when an unrelated instruction is added. A key does not: it is the identity that the
reference gives an occurrence of an event (the number of the event in the text of its
definition, the part of the event, and the iterations of the loops in sequence around it),
and a program point is a block of a loop in sequence, named by the loop's event and the
iteration.

A raw program is accompanied by the keys of its sites, per protocol and in the order of the
site numbers. Admission checks that the table has one key per site and no key twice.
-/

set_option autoImplicit false

namespace Zkc.Core

/-- The key of a site: the event of the text, its part, and the iterations of the loops in
sequence around it, the outermost first. -/
structure SiteKey where
  event : Nat
  part : String
  iteration : List Nat
  deriving Repr, Inhabited, DecidableEq, BEq, Hashable

/-- The key of a program point: a block of a loop in sequence, by the number of the loop
among the loops of its definition in the order of the text, and the iterations of the loops in
sequence around the block, the block's own last. -/
structure PointKey where
  loop : Nat
  iteration : List Nat
  deriving Repr, Inhabited, DecidableEq, BEq, Hashable

/-- The keys of the sites of each protocol of a package, in the order of the protocols and of
the site numbers. -/
abbrev SiteKeys := List (List SiteKey)

/-- No key stands twice in a list. -/
@[expose] def SiteKey.distinct : List SiteKey → Bool
  | [] => true
  | key :: rest => !rest.contains key && SiteKey.distinct rest

end Zkc.Core
