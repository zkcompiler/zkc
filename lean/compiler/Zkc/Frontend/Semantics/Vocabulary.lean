module

public import Zkc.Frontend.Semantics.Static

@[expose] public section

set_option autoImplicit false

/-!
# The vocabulary, as the checker reads it

The types and the modules that exist outside the language, with what each gives the sorts and
the interfaces it has, and the default representative of each sort. A
`type T = primitive("row")` and a `module M: I = primitive("row")` are checked against these
tables (NL9, SP3).
-/

namespace Zkc.Frontend

/-- A type of the vocabulary. A sort is named as its interface is in `zkc::algebra`. -/
structure VocabularyType where
  row : String
  sorts : Array String
  typeMembers : Array (String × ClosedType)
  naturalMembers : Array (String × Nat)
  deriving Inhabited

/-- A module of the vocabulary. The interface is named by its path, `zkc::hash::Hash`; a row
that a project binds has none in the table. -/
structure VocabularyModule where
  row : String
  implements : Option String
  typeMembers : Array (String × ClosedType)
  naturalMembers : Array (String × Nat)
  deriving Inhabited

structure Vocabulary where
  types : Array VocabularyType
  modules : Array VocabularyModule
  /-- For each sort, the row of its default representative (SP7). -/
  representatives : Array (String × String)
  deriving Inhabited

namespace Vocabulary

def type? (vocabulary : Vocabulary) (row : String) : Option VocabularyType :=
  vocabulary.types.find? (·.row == row)

def module? (vocabulary : Vocabulary) (row : String) : Option VocabularyModule :=
  vocabulary.modules.find? (·.row == row)

def representative? (vocabulary : Vocabulary) (sort : String) : Option String :=
  (vocabulary.representatives.find? (·.1 == sort)).map (·.2)

end Vocabulary

/-- What an entry of the vocabulary that a goal names is (GL1). -/
inductive EntryKind where
  | property
  | model
  deriving Inhabited, BEq, Repr

/-- An entry of the vocabulary named through a module that has no source file: a property or a
model of `zkc::security` (GL1). -/
structure VocabularyEntry where
  «module» : String
  name : String
  kind : EntryKind
  deriving Inhabited

/-- The entries of the vocabulary that a source names, by their module (`CORE-LIBRARY.md`
§2.9). -/
def vocabularyEntries : Array VocabularyEntry :=
  let security := "zkc::security"
  #[⟨security, "completeness", .property⟩, ⟨security, "soundness", .property⟩,
    ⟨security, "knowledge_soundness", .property⟩, ⟨security, "zero_knowledge", .property⟩,
    ⟨security, "honest_verifier_zero_knowledge", .property⟩,
    ⟨security, "unforgeability", .property⟩,
    ⟨security, "random_oracle", .model⟩, ⟨security, "generic_group", .model⟩,
    ⟨security, "algebraic_group", .model⟩, ⟨security, "johnson", .model⟩]

/-- Whether a module path names a module of the vocabulary that has no source file. -/
def isVocabularyModule (path : String) : Bool :=
  vocabularyEntries.any (·.module == path)

def vocabularyEntry? (path name : String) : Option VocabularyEntry :=
  vocabularyEntries.find? fun entry => entry.module == path && entry.name == name

end Zkc.Frontend
