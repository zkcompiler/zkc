module

public import Zkc.Core.Facts.Facts
public import Zkc.Core.Program.Refusal

@[expose] public section

/-!
What admission gives: the association of a program and its resolution, and an
admitted program.
-/

namespace Zkc.Core

/-! ## The specification association -/

/-- An argument of an instance of a generic declaration, as the association records it: a
number, or the key of a declaration. Nothing of the vocabulary, of the types or of the dialects
takes such arguments: a key of the vocabulary says everything that tells its type, row or law
from another. -/
inductive Static where
  | nat (n : Nat)
  | key (k : Key)
deriving DecidableEq, Repr

/-- An instance of a generic declaration: the declaration, the checked substitution and the
key of the instance's definition. What it depends on is computed from the program. -/
structure FamilyApplication where
  generic : Key
  arguments : List Static
  definition : Key

/-- The logical binders, the statement and the witness of a relation. -/
structure RelationBinding where
  relation : Key
  binders : List Key
  statement : List Key
  witness : List Key

/-- For proofs: what a statement about admitted definitions needs beyond them. The identity
of what runs does not depend on it; the subject of a proof includes it. -/
structure Association where
  families : List FamilyApplication
  relations : List RelationBinding
  /-- The interpretation chosen for each handle. -/
  interpretations : List (Key × Key)
  claims : List Key
  /-- The specification definitions that the above mention, transitively. -/
  specifications : List Key

/-- A family application whose instance is a definition of the program: the generic
declaration, the substitution, and the definition, found. -/
structure ResolvedFamily {V : Vocabulary} (p : Typed V) where
  generic : Key
  arguments : List Static
  subject : Subject p

/-- The association of a program, resolved: what was given, and for each family application,
in order, its definition found in the program. -/
structure Resolved {V : Vocabulary} (p : Typed V) where
  given : Association
  families : List (ResolvedFamily p)

/-- The resolution of an association in a program: the definition of each family application
is found by its key, and a key that is no definition of the program is refused. -/
def resolve {V : Vocabulary} (p : Typed V) (raw : Association) :
    Except (List (ProgramRefusal V)) (Resolved p) :=
  (raw.families.mapM fun (family : FamilyApplication) =>
      (match p.find family.definition with
      | some subject => .ok ⟨family.generic, family.arguments, subject⟩
      | none => .error [refuseWhole family.definition .association (.key family.definition)] :
        Except (List (ProgramRefusal V)) (ResolvedFamily p))).map
    fun families => ⟨raw, families⟩


/-! ## An admitted program -/

/-- An admitted program: the typed program, its annotation (the bound of each loop as often as
a count whose count has an upper bound, by its place), and the association for proofs, resolved
in the program. -/
structure Admitted (V : Vocabulary) where
  program : Typed V
  annotation : Annotation
  association : Resolved program

end Zkc.Core
