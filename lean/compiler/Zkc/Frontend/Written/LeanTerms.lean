module

public import Zkc.Core.Program.Dialects
public import Zkc.Frontend.Written.Diagnostic
public import Zkc.Frontend.Emit.Bindings

@[expose] public section
set_option autoImplicit false

namespace Zkc.Frontend.Written
open Core

def unsupported {α : Type} (what : String) : ExportM α := .error ("WK-CORE: unsupported " ++ what)

def list (xs : List String) := "[" ++ ", ".intercalate xs ++ "]"
def numbers (xs : List Nat) := list (xs.map toString)
def consList (items : List String) :=
  items.foldr (fun x tail => s!"(.cons {x} {tail})") ".nil"

/-- A public statement uses ordinary Lean products. A Core tuple has a terminal Unit. -/
def component (base : String) (index : Nat) (last := false) : String :=
  base ++ String.join (List.replicate index ".2") ++ (if last then "" else ".1")

partial def ty {b : Emit.Bindings} (t : b.vocabulary.Ty) : ExportM String := do
  let fields (ts : Tys b.vocabulary.TypeKey) := do
    let items ← ts.toList.mapM (ty (b := b))
    return consList items
  match t with
  | .nat => pure ".nat"
  | .fin n => pure s!"(.fin {n})"
  | .seq item size => return s!"(.seq {← ty (b := b) item} ({reprStr size}))"
  | .record key linear ts => return s!"(.record ⟨{key.number}⟩ {linear} {← fields ts})"
  | .variant key ts => return s!"(.variant ⟨{key.number}⟩ {← fields ts})"
  | .bool => pure ".bool"
  | .nominal (.inl k) => pure s!"(.nominal (.inl ({reprStr (show Zkc.Vocabulary.TypeKey from k)})))"
  | .tuple ts => return s!"(.tuple {← fields ts})"
  | _ => unsupported "Core value type in the written scalar/group profile"

def coin (k : Zkc.Vocabulary.LawKey) : ExportM String :=
  match k with
  | .uniform (.nominal t) => pure s!"(.coin (.uniform (.nominal ({reprStr t}))))"
  | _ => unsupported "sampling law"

end Zkc.Frontend.Written
