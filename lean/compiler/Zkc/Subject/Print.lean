module

public import Zkc.Core.Program.Dialects
public import Zkc.Vocabulary.Project
public import Zkc.Subject.Charges

@[expose] public section
set_option autoImplicit false

/-! Lean source text for values that a generated module states: lists, numbers, keys, and the
types of a linked vocabulary, charge tables and membership proofs. -/

namespace Zkc.Subject.Print
open Core

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
def linkedTypeKey : Sum Zkc.Vocabulary.TypeKey Zkc.Vocabulary.Project.Parameter → String
  | .inl k => s!"(.inl ({reprStr k}))"
  | .inr p => s!"(.inr ({reprStr p}))"

def linkedTy (t : Zkc.Vocabulary.Project.LinkedType) : String := coreTy linkedTypeKey t

/-- A type of the vocabulary of the bindings. -/
def ty {b : Zkc.Vocabulary.Project.Bindings} (t : b.vocabulary.Ty) : String := linkedTy t

def tys {b : Zkc.Vocabulary.Project.Bindings} (ts : Tys b.vocabulary.TypeKey) : String := coreTys linkedTypeKey ts

/-- A sampling law of the standard vocabulary. -/
def lawKey : Zkc.Vocabulary.LawKey → String
  | .uniform t => s!"(.uniform {coreTy (fun k => s!"({reprStr k})") t})"

/-- A table of caps as a term. -/
def capsTerm (table : CapTable) : String :=
  let draw (d : DrawCap) := s!"⟨⟨{d.key.number}⟩, {d.numerator}, {d.denominator}, {d.count}⟩"
  let call (c : CallCap) := s!"⟨⟨{c.key.number}⟩, {c.count}, {c.callee}⟩"
  -- what adds up along a run: an item then the rest, or a choice of two arms then the rest
  let rec tally : Core.Tally Cap → String
    | .nil => ".nil"
    | .item (.draw d) rest => s!"(.item (.draw {draw d}) {tally rest})"
    | .item (.call c) rest => s!"(.item (.call {call c}) {tally rest})"
    | .choice left right rest => s!"(.choice {tally left} {tally right} {tally rest})"
  let use (u : UseCaps) := s!"⟨⟨{u.definition.number}⟩, {tally u.caps}⟩"
  s!"⟨[{", ".intercalate (table.uses.map use)}]⟩"

/-- The member of a list of headers that is `depth` places after its head. -/
def memberAt : Nat → String
  | 0 => "Member.head"
  | depth + 1 => s!"(Member.tail {memberAt depth})"

end Zkc.Subject.Print
