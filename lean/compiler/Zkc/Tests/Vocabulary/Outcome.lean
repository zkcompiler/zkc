import Zkc.Core.Transform.Step
import Zkc.Vocabulary

/-!
Functions written by names over the standard vocabulary, at the field koala-bear, as the
conformance cases of the reference give them: each typed by `typeFn` and its facts checked by
`TypedFn.check`, as `Zkc/Tests/Core/Facts.lean` does over its own small vocabulary. The outcome
keeps the refusal of elaboration as well. The cases are in the modules beside this one, each by
its identifier; a generic definition is written at the instance that the case names, or at its
default instances (SP7), with every static natural a number, and lowered as §7.4 says.
-/

namespace Zkc.Vocabulary.Cases

open Zkc.Core

abbrev V : Zkc.Core.Vocabulary := Zkc.Vocabulary.standard
abbrev Ty : Type := Zkc.Vocabulary.Ty
abbrev Raw : Type := LocalRaw Zkc.Vocabulary.standard

/-! ## Types -/

abbrev F : Ty := .nominal (.field .koalaBear)
abbrev Fnz : Ty := .nominal (.nonzero .koalaBear)
abbrev byte : Ty := .fin 256
abbrev sized (τ : Ty) (n : Nat) : Ty := .seq τ (some n)
abbrev unsized (τ : Ty) : Ty := .seq τ none
abbrev Fr : Ty := .nominal (.field .bls12381Fr)
abbrev G1 : Ty := .nominal (.group .g1)
/-- The record `Coset<F, k>`: its one field `shift: nonzero<F>`. -/
abbrev cosetTy : Ty := .record ⟨60⟩ false (.cons Fnz .nil)

/-! ## Written operations -/

abbrev length (τ : Ty) : Raw := .owned .seqLength [τ] []
abbrev item (τ : Ty) : Raw := .owned .seqAt [τ] []
abbrev slice (τ result : Ty) : Raw := .owned .seqSlice [τ, result] []
abbrev sizedAs (it : Ty) (n : Nat) : Raw := .owned .seqSized [.seq it (some n)] []
abbrev widenSeq (it : Ty) (n : Nat) : Raw := .owned .seqUnsized [.seq it (some n)] []
abbrev concat (a b : Ty) : Raw := .owned .seqConcat [a, b] []
abbrev fill (it : Ty) (n : Nat) : Raw := .owned .seqFill [.seq it (some n)] []
abbrev natural (n : Nat) : Raw := .literal .nat [n]
abbrev element (n : Nat) : Raw := .literal F [n]
abbrev unit (n : Nat) : Raw := .literal Fnz [n]
abbrev truth (value : Bool) : Raw := .literal .bool [if value then 1 else 0]
abbrev plus : Raw := .owned .natAdd [] []
abbrev minus : Raw := .owned .natSub [] []
abbrev times : Raw := .owned .natMul [] []
abbrev quotient : Raw := .owned .natDiv [] []
abbrev remainder : Raw := .owned .natRem [] []
abbrev power : Raw := .owned .natPow [] []
abbrev less : Raw := .owned .natLess [] []
abbrev equal : Raw := .owned .natEqual [] []
abbrev negation : Raw := .owned .boolNot [] []
abbrev conj : Raw := .owned .boolAnd [] []
abbrev disj : Raw := .owned .boolOr [] []
abbrev toNat (bound : Nat) : Raw := .owned .finToNat [.fin bound] []
abbrev narrowTo (bound : Nat) : Raw := .owned .natBelow [.fin bound] []
abbrev make (τ : Ty) : Raw := .owned .make [τ] []
abbrev get (τ : Ty) (position : Nat) : Raw := .owned .get [τ] [position]
abbrev take (τ : Ty) : Raw := .owned .take [τ] []
abbrev variant (τ : Ty) (position : Nat) : Raw := .owned .variant [τ] [position]
/-- A row of the field koala-bear at all its elements. -/
abbrev frow (r : Zkc.Vocabulary.FieldRow) : Raw := .row (.field r .koalaBear .all)
/-- A row of the field koala-bear at its elements that are not zero. -/
abbrev nzrow (r : Zkc.Vocabulary.FieldRow) : Raw := .row (.field r .koalaBear .nonzero)
/-- `seq.sum` and `seq.add` on collections of koala-bear. -/
abbrev sumRow (size : Option Nat) : Raw := .row (.seq .sum (.atom (.field .koalaBear)) size)
abbrev seqAddRow (size : Nat) : Raw := .row (.seq .add (.atom (.field .koalaBear)) (some size))

/-! ## The outcome -/

/-- What the core says of a function by names: the refusal of elaboration, or the refusals of
the check of facts, or acceptance with the bounds of its loops. -/
inductive Outcome where
  | elaboration (refusal : ProgramRefusal V)
  | refused (refusals : List (ProgramRefusal V))
  | accepted (bounds : List (Place × Nat))
deriving DecidableEq

/-- The outcome for a function against the headers before it. -/
def run (fns : List (FnHeader V)) (hdr : FnHeader V) (body : Region Raw Unit) : Outcome :=
  match typeFn fns hdr body with
  | .ok f =>
      match f.check with
      | .ok bounds => .accepted bounds
      | .error refusals => .refused refusals
  | .error refusal => .elaboration refusal

/-- The outcome for a function with the key 1 and no callee. -/
def check (ins outs : List Ty) (canStop : Bool) (body : Region Raw Unit) : Outcome :=
  run [] ⟨⟨1⟩, ins, outs, canStop, none⟩ body

/-- The place of an instruction of a function with a key. -/
def placeIn (fn : Nat) (instruction : Nat) (blocks : List (Key × Nat) := []) : Place :=
  ⟨⟨fn⟩, blocks, some ⟨instruction⟩, none⟩

/-- An application refused at an instruction of the function with the key 1. -/
def unjustified (instruction : Nat) (written : Raw) (requirement : Requirement Raw)
    (known : List (Option Range)) (fn : Nat := 1) (blocks : List (Key × Nat) := []) :
    ProgramRefusal V :=
  ⟨.domain, placeIn fn instruction blocks, .unjustified written requirement known⟩

abbrev lengthOf (τ : Ty) : Operand Raw := .apply (length τ) [0]
abbrev anyNat : Option Range := some ⟨0, none⟩
abbrev pt (n : Nat) : Option Range := some (Range.point n)
abbrev rng (lo hi : Nat) : Option Range := some ⟨lo, some hi⟩

end Zkc.Vocabulary.Cases
