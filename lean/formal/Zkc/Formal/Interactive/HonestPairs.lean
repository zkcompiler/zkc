module

public import Zkc.Formal.Interactive.TableRestriction
public import Zkc.Formal.Interactive.PairRound

@[expose] public section
namespace Zkc.Formal.Interactive.Sumcheck.HonestPairs
open Core
open TableHalves (table)
variable {V : Vocabulary} (rows : ScalarRows V) {n : Nat}

structure SumRow (n : Nat) where
  key : V.RowKey
  typed : V.row key = some ⟨[table rows.scalarTy n],[rows.scalarTy],.pure⟩

variable (sr : SumRow rows n)

def SumRow.Arithmetic (M : Model V) [Lean.Grind.Field (rows.F M)] : Prop :=
  ∀ xs : List (rows.F M), xs.length = 2^n →
    M.apply sr.key _ sr.typed (.cons xs .nil) = some (.cons xs.sum .nil)

abbrev messageHeader (k : Key) (n : Nat) : FnHeader V :=
  ⟨k,[table rows.scalarTy (n+1)],[rows.pair],false,none,⟨[],[]⟩⟩

local macro "vAt " n:term:max : term => `(⟨$n,rfl⟩)
def sums (k : Key) (fns : List (FnHeader V)) :
    Fn V fns (messageHeader rows k n) (.cons 0 .nil) :=
  let t := rows.scalarTy
  let slice := OwnedOp.seqSlice t (some (2^(n+1))) (some (2^n)) rows.free
  .op ⟨0⟩ (.literal .nat [0] rfl) .nil (.cons 1 .nil) <|
  .op ⟨1⟩ (.literal .nat [2] rfl) .nil (.cons 2 .nil) <|
  .op ⟨2⟩ (.literal .nat [n] rfl) .nil (.cons 3 .nil) <|
  .op ⟨3⟩ (.owned .natPow) (.cons (vAt 2) (.cons (vAt 3) .nil)) (.cons 4 .nil) <|
  .op ⟨4⟩ (.owned slice) (.cons (vAt 0) (.cons (vAt 1) (.cons (vAt 4) .nil))) (.cons 5 .nil) <|
  .op ⟨5⟩ (.row sr.key _ sr.typed) (.cons (vAt 5) .nil) (.cons 6 .nil) <|
  .op ⟨6⟩ (.literal .nat [2] rfl) .nil (.cons 7 .nil) <|
  .op ⟨7⟩ (.literal .nat [n] rfl) .nil (.cons 8 .nil) <|
  .op ⟨8⟩ (.owned .natPow) (.cons (vAt 7) (.cons (vAt 8) .nil)) (.cons 9 .nil) <|
  .op ⟨9⟩ (.literal .nat [2] rfl) .nil (.cons 10 .nil) <|
  .op ⟨10⟩ (.literal .nat [n] rfl) .nil (.cons 11 .nil) <|
  .op ⟨11⟩ (.literal .nat [1] rfl) .nil (.cons 12 .nil) <|
  .op ⟨12⟩ (.owned .natAdd) (.cons (vAt 11) (.cons (vAt 12) .nil)) (.cons 13 .nil) <|
  .op ⟨13⟩ (.owned .natPow) (.cons (vAt 10) (.cons (vAt 13) .nil)) (.cons 14 .nil) <|
  .op ⟨14⟩ (.owned slice) (.cons (vAt 0) (.cons (vAt 9) (.cons (vAt 14) .nil))) (.cons 15 .nil) <|
  .op ⟨15⟩ (.row sr.key _ sr.typed) (.cons (vAt 15) .nil) (.cons 16 .nil) <|
  .op ⟨16⟩ (.owned (.makeTuple rows.fields)) (.cons (vAt 6) (.cons (vAt 16) .nil)) (.cons 17 .nil) <|
  .ret (.cons (vAt 17) .nil)

def MessageLaw (k : Key) (run : FunctionMeaning (messageHeader rows k n)) : Prop :=
  ∀ (M : Model V) [Lean.Grind.Field (rows.F M)], sr.Arithmetic rows M → ∀ x : Cube (rows.F M) (n+1),
    run M (.cons (Cube.flatten (n+1) x) .nil) = .done (.cons (Cube.sum n x.1,Cube.sum n x.2,()) .nil)

set_option maxHeartbeats 1800000 in
set_option maxRecDepth 4096 in
def sumsReadback (k : Key) : FunctionReadback _ (MessageLaw rows sr k) where
  inputs := .cons 0 .nil
  body := sums rows sr k
  armed _ := rfl
  holds fns tables := by
    intro M _ math x
    let a := Cube.flatten n x.1
    let b := Cube.flatten n x.2
    let slice := OwnedOp.seqSlice rows.scalarTy (some (2^(n+1))) (some (2^n)) rows.free
    have piece (i j : Nat) (fits : i ≤ j ∧ j ≤ (a++b).length ∧ j-i = 2^n) :
        localOp M (tables M) (.owned slice) (.cons (a++b) (.cons i (.cons j .nil))) =
          .done (.cons (((a++b).drop i).take (j-i)) .nil) := by
      change (if _ then _ else _) = _
      rw [ite_eq_left]
      exact ⟨fits.1,fits.2.1,by simp [fitsSize,fits.2.2]⟩
    have lenA := Cube.flatten_length n x.1
    have lenB := Cube.flatten_length n x.2
    have size : 2^(n+1) = 2^n + 2^n := by simp [Nat.pow_succ,Nat.mul_two]
    have lo := piece 0 (2^n) (by simp [a,b,Cube.flatten_length])
    have hi := piece (2^n) (2^(n+1)) (by simp [a,b,Cube.flatten_length,size])
    have lowValue : ((a++b).drop 0).take (2^n-0) = a := by simp [a,← lenA]
    have highValue : ((a++b).drop (2^n)).take (2^(n+1)-2^n) = b := by
      rw [size,Nat.add_sub_cancel,show (a++b).drop (2^n) = b by rw [← lenA]; exact List.drop_left]
      simp [b,← lenB]
    rw [lowValue] at lo
    rw [highValue] at hi
    have row (y : Cube (rows.F M) n) :
        localOp M (tables M) (.row sr.key _ sr.typed) (.cons (Cube.flatten n y) .nil) =
          .done (.cons (Cube.sum n y) .nil) := by
      simp only [localOp,math _ (Cube.flatten_length n y),Cube.sum_flatten]
    change (localOp M (tables M) (.owned slice) (.cons (a++b) (.cons 0 (.cons (2^n) .nil)))).bind _ = _
    rw [lo]
    change (localOp M (tables M) (.row sr.key _ sr.typed) (.cons a .nil)).bind _ = _
    rw [row x.1]
    change (localOp M (tables M) (.owned slice) (.cons (a++b) (.cons (2^n) (.cons (2^(n+1)) .nil)))).bind _ = _
    rw [hi]
    change (localOp M (tables M) (.row sr.key _ sr.typed) (.cons b .nil)).bind _ = _
    rw [row x.2]
    rfl

end Zkc.Formal.Interactive.Sumcheck.HonestPairs
