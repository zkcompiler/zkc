module

public import Zkc.Formal.Interactive.PublicTable
public import Zkc.Core.Evidence.FunctionEntry

@[expose] public section
namespace Zkc.Formal.Interactive.Sumcheck.TableHalves
open Core
variable {V : Vocabulary} (t : V.Ty) (free : Ty.isLinear V t = false)

abbrev table (t : V.Ty) (n : Nat) : V.Ty := .seq t (some (2^n))
abbrev header (k : Key) (n : Nat) : FnHeader V := ⟨k,[table t (n+1)],[table t n],false,none,⟨[],[]⟩⟩
local macro "varAt " n:term:max : term => `(⟨$n, rfl⟩)

def lowBody (k : Key) (n : Nat) (fns : List (FnHeader V)) :
    Fn V fns (header t k n) (.cons 0 .nil) :=
  .op ⟨0⟩ (.literal .nat [0] rfl) .nil (.cons 1 .nil) <|
  .op ⟨1⟩ (.literal .nat [2] rfl) .nil (.cons 2 .nil) <|
  .op ⟨2⟩ (.literal .nat [n] rfl) .nil (.cons 3 .nil) <|
  .op ⟨3⟩ (.owned .natPow) (.cons (varAt 2) (.cons (varAt 3) .nil)) (.cons 4 .nil) <|
  .op ⟨4⟩ (.owned (.seqSlice t (some (2^(n+1))) (some (2^n)) free)) (.cons (varAt 0) (.cons (varAt 1) (.cons (varAt 4) .nil))) (.cons 5 .nil) <|
  .ret (.cons (varAt 5) .nil)

def highBody (k : Key) (n : Nat) (fns : List (FnHeader V)) :
    Fn V fns (header t k n) (.cons 0 .nil) :=
  .op ⟨0⟩ (.literal .nat [2] rfl) .nil (.cons 1 .nil) <|
  .op ⟨1⟩ (.literal .nat [n] rfl) .nil (.cons 2 .nil) <|
  .op ⟨2⟩ (.owned .natPow) (.cons (varAt 1) (.cons (varAt 2) .nil)) (.cons 3 .nil) <|
  .op ⟨3⟩ (.literal .nat [2] rfl) .nil (.cons 4 .nil) <|
  .op ⟨4⟩ (.literal .nat [n] rfl) .nil (.cons 5 .nil) <|
  .op ⟨5⟩ (.literal .nat [1] rfl) .nil (.cons 6 .nil) <|
  .op ⟨6⟩ (.owned .natAdd) (.cons (varAt 5) (.cons (varAt 6) .nil)) (.cons 7 .nil) <|
  .op ⟨7⟩ (.owned .natPow) (.cons (varAt 4) (.cons (varAt 7) .nil)) (.cons 8 .nil) <|
  .op ⟨8⟩ (.owned (.seqSlice t (some (2^(n+1))) (some (2^n)) free)) (.cons (varAt 0) (.cons (varAt 3) (.cons (varAt 8) .nil))) (.cons 9 .nil) <|
  .ret (.cons (varAt 9) .nil)

def Law (upper : Bool) (k : Key) (n : Nat) (run : FunctionMeaning (header t k n)) : Prop :=
  ∀ (M : Model V) (lo hi : Cube (M.Val t) n), run M (.cons (Cube.flatten n lo ++ Cube.flatten n hi) .nil) =
    .done (.cons (Cube.flatten n (if upper then hi else lo)) .nil)

private theorem slice {fns : List (FnHeader V)} (M : Model V) (f : FnTable M fns) (n i j : Nat)
    (xs : List (M.Val t)) (fits : i ≤ j ∧ j ≤ xs.length ∧ j-i = 2^n) :
    localOp M f (.owned (.seqSlice t (some (2^(n+1))) (some (2^n)) free)) (.cons xs (.cons i (.cons j .nil))) =
      .done (.cons ((xs.drop i).take (j-i)) .nil) := by
  change (if _ then _ else _) = _
  rw [ite_eq_left]
  exact ⟨fits.1,fits.2.1,by simp [fitsSize,fits.2.2]⟩

theorem low_value (k : Key) (n : Nat) (fns : List (FnHeader V)) (tables : (M : Model V) → FnTable M fns) :
    Law t false k n (fun M args => (lowBody t free k n fns).denote (localSem M _ (tables M)) [] (Env.empty.extend (.cons 0 .nil) args)) := by
  intro M lo hi
  let xs := Cube.flatten n lo ++ Cube.flatten n hi
  change (localOp M (tables M) (.owned (.seqSlice t (some (2^(n+1))) (some (2^n)) free))
    (.cons xs (.cons 0 (.cons (2^n) .nil)))).bind _ = _
  rw [slice t free M _ _ _ _ xs (by simp [xs,Cube.flatten_length])]
  change Process.done (A := HList M.Val [table t n]) (HList.cons ((xs.drop 0).take (2^n-0)) .nil) = _
  simp [xs,← Cube.flatten_length n lo]

theorem high_value (k : Key) (n : Nat) (fns : List (FnHeader V)) (tables : (M : Model V) → FnTable M fns) :
    Law t true k n (fun M args => (highBody t free k n fns).denote (localSem M _ (tables M)) [] (Env.empty.extend (.cons 0 .nil) args)) := by
  intro M lo hi
  let xs := Cube.flatten n lo ++ Cube.flatten n hi
  have size : 2^(n+1) = 2^n + 2^n := by simp [Nat.pow_succ,Nat.mul_two]
  change (localOp M (tables M) (.owned (.seqSlice t (some (2^(n+1))) (some (2^n)) free))
    (.cons xs (.cons (2^n) (.cons (2^(n+1)) .nil)))).bind _ = _
  rw [slice t free M _ _ _ _ xs (by simp [xs,Cube.flatten_length,size])]
  have length := Cube.flatten_length n lo
  change Process.done (A := HList M.Val [table t n]) (HList.cons ((xs.drop (2^n)).take (2^(n+1)-2^n)) .nil) = _
  rw [size,Nat.add_sub_cancel,show xs.drop (2^n) = Cube.flatten n hi by rw [← length]; exact List.drop_left]
  simp [← Cube.flatten_length n hi]

def readback (upper : Bool) (k : Key) (n : Nat) : FunctionReadback _ (Law t upper k n) :=
  match upper with
  | false => ⟨.cons 0 .nil,lowBody t free k n,fun _ => rfl,low_value t free k n⟩
  | true => ⟨.cons 0 .nil,highBody t free k n,fun _ => rfl,high_value t free k n⟩

end Zkc.Formal.Interactive.Sumcheck.TableHalves
