module

public import Zkc.Frontend.Lowered.Tree

@[expose] public section

set_option autoImplicit false

/-!
# What a written path stands for

The table of resolutions of a file maps the byte at which a `Path` starts to its resolution. It
is a projection of the lowered form, which holds the same steps in place; typing walks the tree
of the parser and asks the table.

A resolution is one step per segment. The first is found lexically; each later one is a step
from what came before: a declaration of a namespace, a member of the interfaces or sorts of a
static thing, an alternative of a variant, a generated member. A dot call, an operator and a
mathematical form need the type of an expression and have no entry; a bare alternative has the
step `bareAlternative`, which typing completes with the expected type.
-/

namespace Zkc.Frontend

open Syntax

/-- A resolved segment: the step and the static arguments written on it, lowered. Arguments
that an import fixed are those of the import's path, lowered in the file of the import;
`fixedBy` names the import, under whose scopes they are evaluated. -/
structure ResolvedSegment where
  step : Step
  staticArgs : Option (Array Lowered.StaticArgument)
  fixedBy : Option ImportId := none
  deriving Inhabited

/-- The resolution of a path: one entry per step, the namespace modules passed through
included. An import contributes the steps of its own path in place of the name it binds. -/
structure Resolution where
  segments : Array ResolvedSegment
  deriving Inhabited

/-- The resolutions of the paths of one file, by the byte at which the path starts. A name that
stands for a path without being one has an entry at its own first byte: a name listed in a
`use` or bound by `as`, the short form `{x}` of a field, the name that `:=` updates. -/
abbrev FileResolutions := Std.HashMap UInt32 Resolution

/-- The resolutions of a program, one table per file. -/
structure Resolutions where
  files : Array FileResolutions := #[]
  deriving Inhabited

namespace Resolutions

def find? (resolutions : Resolutions) (file : FileId) (path : Path) : Option Resolution :=
  match path with
  | .path span _ => (resolutions.files[file]?).bind (·[span.startByte]?)

def findName? (resolutions : Resolutions) (file : FileId) (name : Name) : Option Resolution :=
  (resolutions.files[file]?).bind (·[name.span.startByte]?)

/-- The number of entries of every file. -/
def size (resolutions : Resolutions) : Nat :=
  resolutions.files.foldl (· + ·.size) 0

end Resolutions

end Zkc.Frontend
