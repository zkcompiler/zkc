import Lean.Elab.Command

/-! The files that the checks read.

A check names a file by its path in the package, as in `fixtures/schnorr.json`. The path
is resolved against the directory of the package, which is the path of the module that is
being elaborated without the components of the module's name. It is not resolved against
the directory in which the build was started: the package is also built from the workspace
of a package that requires it.

`packagePath` is the resolved path, for a command that reads a file. `package_file "<path>"`
is the resolved path as a string literal, for a program that reads a file when it runs.
-/

set_option autoImplicit false

open Lean Elab

namespace Zkc.Core

/-- The directory that is a number of components above a path. -/
def directoryAbove : Nat → System.FilePath → System.FilePath
  | 0, path => path
  | above + 1, path => directoryAbove above (path.parent.getD "")

/-- A path in the package of the module that is being elaborated. -/
def packagePath (path : String) : CoreM System.FilePath := do
  let root := directoryAbove (← getMainModule).components.length (← getFileName)
  pure (if root.toString.isEmpty then path else root / path)

/-- A path in the package of the module that is being elaborated, as a string. -/
elab "package_file " path:str : term => do
  pure (mkStrLit (← packagePath path.getString).toString)

end Zkc.Core
