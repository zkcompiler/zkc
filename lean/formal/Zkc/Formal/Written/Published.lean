module

public meta import Lean

public meta section
open Lean Elab Command

/-!
What a module publishes, read from what Lean stored.

A module of statements defines its propositions before the text of the proofs, and after the
text it states the theorems of those propositions. The theorems after the text are elaborated
in the scope that the text leaves: a variable that the text declared there is a hypothesis of
every theorem that can use it, silently, and a check that reads Lean's exit code and its reports
of axioms sees nothing of that. A theorem with such a hypothesis is not a theorem of its
proposition.

`published T : P` reads the declaration `T` as Lean stored it and fails unless `T` is a theorem
whose statement is exactly the definition `P`, with no binder before it and no universe
parameter. Both names are taken as they are written, in full: nothing that a text opened or
declared takes part in finding them.
-/

namespace Zkc.Formal.Written

/-- **A theorem states exactly its published proposition.** `published T : P` fails unless the
declaration with the full name `T` is a theorem whose stored type is the definition with the
full name `P`. -/
elab "published " stated:ident " : " proposition:ident : command => do
  let env ← getEnv
  let theoremName := stated.getId
  let propositionName := proposition.getId
  let some declared := env.find? theoremName
    | throwErrorAt stated "published: there is no declaration `{theoremName}`"
  unless declared matches .thmInfo _ do
    throwErrorAt stated "published: `{theoremName}` is no theorem"
  let some defined := env.find? propositionName
    | throwErrorAt proposition "published: there is no declaration `{propositionName}`"
  unless defined matches .defnInfo _ do
    throwErrorAt proposition "published: `{propositionName}` is no definition"
  unless declared.levelParams.isEmpty && declared.type == mkConst propositionName do
    throwErrorAt stated
      m!"published: `{theoremName}` does not state `{propositionName}`. It states{indentExpr declared.type}"

end Zkc.Formal.Written
