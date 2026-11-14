module

public import Zkc.Core.Vocabulary
public import Zkc.Frontend.Semantics.Vocabulary

@[expose] public section

set_option autoImplicit false

/-!
# The vocabulary, read from the core

The types, the modules, the default representatives and the operation rows of the vocabulary
are one value of the core, `Zkc.Core.Vocabulary.table`, which also states what the arithmetic of
each type is. The checker reads it: a closed type of the vocabulary is a closed type of source
(a row of the vocabulary is a nominal type without static arguments), and the type and natural
members of each type and module are read at no static argument.
-/

namespace Zkc.Frontend

/-- A closed type of the vocabulary as a closed type of source. -/
partial def closedOfVocabulary : Zkc.Core.Vocabulary.Closed → ClosedType
  | .bool => .bool
  | .nat => .nat
  | .index bound => .index bound
  | .nonzero field => .nonzero (closedOfVocabulary field)
  | .seq element size => .seq (closedOfVocabulary element) size
  | .tuple components =>
    .tuple (components.toArray.map closedOfVocabulary) (components.toArray.map fun _ => none)
  | .row name => .nominal name #[]

/-- A closed type of source as a closed type of the vocabulary, when it is one. -/
partial def vocabularyOfClosed : ClosedType → Option Zkc.Core.Vocabulary.Closed
  | .bool => some .bool
  | .nat => some .nat
  | .index bound => some (.index bound)
  | .nonzero field => (vocabularyOfClosed field).map .nonzero
  | .seq element size => (vocabularyOfClosed element).map (.seq · size)
  | .tuple components _ => (components.toList.mapM vocabularyOfClosed).map .tuple
  | .nominal row arguments => if arguments.isEmpty then some (.row row) else none
  | _ => none

/-- The members of an entry of the vocabulary at no static argument. -/
def readMembers (types : List (String × Zkc.Core.Vocabulary.Term)) : Array (String × ClosedType) :=
  (types.filterMap fun (name, term) =>
    (term.at Zkc.Core.Vocabulary.table []).map fun closed => (name, closedOfVocabulary closed)).toArray

/-- The vocabulary as the checker reads it. -/
def vocabulary : Vocabulary where
  types := (Zkc.Core.Vocabulary.table.types.map fun entry =>
    ({ row := entry.row, sorts := entry.sorts.toArray, typeMembers := readMembers entry.typeMembers
       naturalMembers := entry.naturalMembers.toArray } : VocabularyType)).toArray
  modules := (Zkc.Core.Vocabulary.table.modules.map fun entry =>
    ({ row := entry.row, implements := entry.implements, typeMembers := readMembers entry.typeMembers
       naturalMembers := entry.naturalMembers.toArray } : VocabularyModule)).toArray
  representatives := Zkc.Core.Vocabulary.table.representatives.toArray

end Zkc.Frontend
