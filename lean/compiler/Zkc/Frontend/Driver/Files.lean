module

public import Zkc.Frontend.Semantics.Assemble
public import Zkc.Frontend.Syntax.Parser

@[expose] public section
set_option autoImplicit false

/-!
Source files as inputs: a file read and parsed, and the assembly of an entry with the modules
that it uses, each found as a file under a list of directories.
-/

namespace Zkc.Frontend.Driver

/-- A source file, read and parsed. -/
def readSource (path : System.FilePath) : IO SourceInput := do
  return ⟨path.toString, Syntax.parse path.toString (← IO.FS.readBinFile path)⟩

/-- The assembly of an entry with the modules that it uses: the module `a::b` is the file
`a/b.zkc` under the first of the directories that has it. -/
def assembleFiles (entry : SourceInput) (directories : List System.FilePath) : IO Assembly :=
  assemble #[entry] fun segments => do
    let relative := "/".intercalate segments.toList ++ ".zkc"
    for directory in directories do
      let path := directory / relative
      if ← path.pathExists then return some (← readSource path)
    return none

end Zkc.Frontend.Driver
