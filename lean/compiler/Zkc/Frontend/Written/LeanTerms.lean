module

public import Zkc.Core.Program.Dialects
public import Zkc.Frontend.Written.Diagnostic
public import Zkc.Frontend.Emit.Bindings

@[expose] public section
set_option autoImplicit false

/-! Lean source text for values that a generated module states: lists, numbers, keys, and the
types of a linked vocabulary. -/

namespace Zkc.Frontend.Written
open Core

def unsupported {α : Type} (what : String) : ExportM α := .error ("WK-CORE: unsupported " ++ what)

def list (xs : List String) := "[" ++ ", ".intercalate xs ++ "]"
def numbers (xs : List Nat) := list (xs.map toString)
def consList (items : List String) :=
  items.foldr (fun x tail => s!"(.cons {x} {tail})") ".nil"

def key (k : Key) : String := s!"⟨{k.number}⟩"
def keys (ks : List Key) : String := list (ks.map key)

def option {α : Type} (item : α → String) : Option α → String
  | none => "none"
  | some a => s!"(some {item a})"

/-- A public statement uses ordinary Lean products. A Core tuple has a terminal Unit. -/
def component (base : String) (index : Nat) (last := false) : String :=
  base ++ String.join (List.replicate index ".2") ++ (if last then "" else ".1")

mutual
  /-- A core type over nominal keys that `nominal` writes. -/
  def coreTy {K : Type} (nominal : K → String) : Core.Ty K → String
    | .bool => ".bool"
    | .nat => ".nat"
    | .fin n => s!"(.fin {n})"
    | .seq item size => s!"(.seq {coreTy nominal item} {option toString size})"
    | .tuple items => s!"(.tuple {coreTys nominal items})"
    | .record k linear fields => s!"(.record {key k} {linear} {coreTys nominal fields})"
    | .variant k alternatives => s!"(.variant {key k} {coreTys nominal alternatives})"
    | .nominal k => s!"(.nominal {nominal k})"
  def coreTys {K : Type} (nominal : K → String) : Core.Tys K → String
    | .nil => ".nil"
    | .cons head rest => s!"(.cons {coreTy nominal head} {coreTys nominal rest})"
end

/-- A nominal type of a linked vocabulary: a standard one, or one of the project's. -/
def linkedTypeKey : Sum Zkc.Vocabulary.TypeKey Emit.Parameter → String
  | .inl k => s!"(.inl ({reprStr k}))"
  | .inr p => s!"(.inr ({reprStr p}))"

def linkedTy (t : Emit.LinkedType) : String := coreTy linkedTypeKey t

/-- A type of the vocabulary of the bindings. -/
def ty {b : Emit.Bindings} (t : b.vocabulary.Ty) : String := linkedTy t

def tys {b : Emit.Bindings} (ts : Tys b.vocabulary.TypeKey) : String := coreTys linkedTypeKey ts

/-- A sampling law of the standard vocabulary. -/
def lawKey : Zkc.Vocabulary.LawKey → String
  | .uniform t => s!"(.uniform {coreTy (fun k => s!"({reprStr k})") t})"

end Zkc.Frontend.Written
