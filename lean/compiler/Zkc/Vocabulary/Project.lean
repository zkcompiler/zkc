module

public import Zkc.Core.Program.LinkedVocabulary
public import Zkc.Vocabulary.Standard

@[expose] public section

/-!
The vocabulary of a package: the standard vocabulary with the primitives that a project binds.

A project binds a primitive under a name and static arguments, with one signature over the
types of the standard vocabulary and the project's own types. The vocabulary of a package is
the standard one linked with those primitives. A proof about a package reads its vocabulary
from here, and needs nothing of the frontend that compiled the package.

How a source type becomes a parameter is the frontend's business (`Zkc.Frontend.Emit`).
-/

namespace Zkc.Vocabulary.Project

/-- The head of a source type in the static arguments of a primitive. A record, a variant, a
specification type or a module instance is named by the number of its instance in the
compilation of the package. Tuple labels and sort constraints describe source syntax and add
no identity of a run-time type. -/
inductive TypeHead where
  | bool | nat | rational | index (bound : Nat) | nonzero
  | seq (size : Option Nat) | tuple | nominal (row : String)
  | record (inst : Nat) | variant (inst : Nat)
  | specification (inst : Nat) | opaqueMember (inst : Nat) (member : String)
  deriving DecidableEq, Repr, Hashable

mutual
  /-- A static argument of a primitive: a natural, a module instance, or a type with its own
  arguments. -/
  inductive Parameter where
    | natural (value : Nat)
    | moduleRef (inst : Nat)
    | type (head : TypeHead) (args : Parameters)
  inductive Parameters where
    | nil
    | cons (head : Parameter) (tail : Parameters)
end

deriving instance DecidableEq for Parameter, Parameters
deriving instance Repr for Parameter, Parameters
deriving instance Hashable for Parameter, Parameters

/-- A primitive that a project binds: its name and its static arguments. -/
structure PrimitiveName where
  name : String
  arguments : Parameters
  deriving DecidableEq, Repr, Hashable

/-- A type over the nominal types of the standard vocabulary and the project's own. -/
abbrev LinkedType := Core.Ty (Sum Zkc.Vocabulary.TypeKey Parameter)

structure PrimitiveSignature where
  inputs : List LinkedType
  outputs : List LinkedType
  deriving DecidableEq

/-- A single signature for each project binding, including bindings reached through
different declarations with the same primitive spelling and evaluated static arguments. -/
structure Bindings where
  rows : List (PrimitiveName × PrimitiveSignature) := []
  distinct : (rows.map Prod.fst).Nodup := by decide

def Bindings.signature (b : Bindings) (k : PrimitiveName) : Option PrimitiveSignature :=
  b.rows.lookup k

def Bindings.insert (b : Bindings) (key : PrimitiveName) (signature : PrimitiveSignature) :
    Except PrimitiveName Bindings :=
  match h : b.signature key with
  | none => .ok ⟨(key, signature) :: b.rows, by
      apply List.nodup_cons.mpr
      refine ⟨?_, b.distinct⟩
      intro member
      obtain ⟨p, hp, same⟩ := List.mem_map.mp member
      have different := List.lookup_eq_none_iff.mp h p hp
      simp [same] at different⟩
  | some prior => if prior = signature then .ok b else .error key

def Bindings.primitives (b : Bindings) : Core.PurePrimitives Zkc.Vocabulary.standard Parameter PrimitiveName where
  signature key := (b.signature key).map fun s => (s.inputs, s.outputs)

/-- The vocabulary of a package with these bindings. -/
abbrev Bindings.vocabulary (b : Bindings) : Core.Vocabulary := b.primitives.vocabulary

end Zkc.Vocabulary.Project
