module

public import ZkcFormal.Interactive.TableHalves

@[expose] public section
namespace ZkcFormal.Interactive.Sumcheck.TableRestriction
open Zkc.Core
open TableHalves (table)
variable {V : Vocabulary} (t : V.Ty)

abbrev header (k : Key) (n : Nat) : FnHeader V := ⟨k,[table t (n+1),t],[table t n],false,none,⟨[],[]⟩⟩
abbrev binary (n : Nat) : RowSignature V.TypeKey V.RowKey := ⟨[table t n,table t n],[table t n],.pure⟩
abbrev scaling (n : Nat) : RowSignature V.TypeKey V.RowKey := ⟨[table t n,t],[table t n],.pure⟩

structure Rows (n : Nat) where
  add : V.RowKey
  sub : V.RowKey
  scale : V.RowKey
  addType : V.row add = some (binary t n)
  subType : V.row sub = some (binary t n)
  scaleType : V.row scale = some (scaling t n)

variable {t} {n : Nat} (rows : Rows t n)

structure Arithmetic (M : Model V) [Lean.Grind.Field (M.Val t)] : Prop where
  add : ∀ (xs ys : List (M.Val t)), xs.length = 2^n → ys.length = 2^n →
    M.apply rows.add _ rows.addType (.cons xs (.cons ys .nil)) = some (.cons (List.zipWith (·+·) xs ys) .nil)
  sub : ∀ (xs ys : List (M.Val t)), xs.length = 2^n → ys.length = 2^n →
    M.apply rows.sub _ rows.subType (.cons xs (.cons ys .nil)) = some (.cons (List.zipWith (·-·) xs ys) .nil)
  scale : ∀ (xs : List (M.Val t)) (r : M.Val t), xs.length = 2^n →
    M.apply rows.scale _ rows.scaleType (.cons xs (.cons r .nil)) = some (.cons (xs.map (·*r)) .nil)

variable {fns : List (FnHeader V)} {lowKey highKey : Key}
variable (lo : Member fns (TableHalves.header t lowKey n)) (hi : Member fns (TableHalves.header t highKey n))
local macro "varAt " n:term:max : term => `(⟨$n,rfl⟩)

def body (k : Key) : Fn V fns (header t k n) (.cons 0 (.cons 1 .nil)) :=
  .op ⟨0⟩ (.call lo) (.cons (varAt 0) .nil) (.cons 2 .nil) <|
  .op ⟨1⟩ (.call hi) (.cons (varAt 0) .nil) (.cons 3 .nil) <|
  .op ⟨2⟩ (.call lo) (.cons (varAt 0) .nil) (.cons 4 .nil) <|
  .op ⟨3⟩ (.row rows.sub _ rows.subType) (.cons (varAt 3) (.cons (varAt 4) .nil)) (.cons 5 .nil) <|
  .op ⟨4⟩ (.row rows.scale _ rows.scaleType) (.cons (varAt 5) (.cons (varAt 1) .nil)) (.cons 6 .nil) <|
  .op ⟨5⟩ (.row rows.add _ rows.addType) (.cons (varAt 2) (.cons (varAt 6) .nil)) (.cons 7 .nil) <|
  .ret (.cons (varAt 7) .nil)

def Law (k : Key) (run : FunctionMeaning (header t k n)) : Prop :=
  ∀ (M : Model V) [Lean.Grind.Field (M.Val t)], Arithmetic rows M → ∀ (x : Cube (M.Val t) (n+1)) (r : M.Val t),
    run M (.cons (Cube.flatten (n+1) x) (.cons r .nil)) = .done (.cons (Cube.flatten n (Cube.restrict n x r)) .nil)

theorem value (k : Key) (tables : (M : Model V) → FnTable M fns)
    (low : TableHalves.Law t false lowKey n (fun M => tables M _ lo))
    (high : TableHalves.Law t true highKey n (fun M => tables M _ hi)) :
    Law rows k (fun M args => (body rows lo hi k).denote (localSem M _ (tables M)) []
      (Env.empty.extend (.cons 0 (.cons 1 .nil)) args)) := by
  intro M _ math x r
  let a := Cube.flatten n x.1
  let b := Cube.flatten n x.2
  let d := List.zipWith (·-·) b a
  let scaled := d.map (·*r)
  have hx := low M x.1 x.2
  have hy := high M x.1 x.2
  change tables M _ lo (.cons (a++b) .nil) = .done (.cons a .nil) at hx
  change tables M _ hi (.cons (a++b) .nil) = .done (.cons b .nil) at hy
  change (tables M _ lo (.cons (a++b) .nil)).bind _ = _
  rw [hx]
  change (tables M _ hi (.cons (a++b) .nil)).bind _ = _
  rw [hy]
  change (tables M _ lo (.cons (a++b) .nil)).bind _ = _
  rw [hx]
  have lenA := Cube.flatten_length n x.1
  have lenB := Cube.flatten_length n x.2
  have lenD : d.length = 2^n := by simp [d,a,b,Cube.flatten_length]
  have lenS : scaled.length = 2^n := by simpa [scaled] using lenD
  have sub : localOp M (tables M) (.row rows.sub _ rows.subType) (.cons b (.cons a .nil)) = .done (.cons d .nil) := by
    simp [localOp,math.sub b a lenB lenA,d]
  have scale : localOp M (tables M) (.row rows.scale _ rows.scaleType) (.cons d (.cons r .nil)) = .done (.cons scaled .nil) := by
    simp [localOp,math.scale d r lenD,scaled]
  have add : localOp M (tables M) (.row rows.add _ rows.addType) (.cons a (.cons scaled .nil)) =
      .done (.cons (List.zipWith (·+·) a scaled) .nil) := by simp [localOp,math.add a scaled lenA lenS]
  change (localOp M (tables M) (.row rows.sub _ rows.subType) (.cons b (.cons a .nil))).bind _ = _
  rw [sub]
  change (localOp M (tables M) (.row rows.scale _ rows.scaleType) (.cons d (.cons r .nil))).bind _ = _
  rw [scale]
  change (localOp M (tables M) (.row rows.add _ rows.addType) (.cons a (.cons scaled .nil))).bind _ = _
  rw [add]
  exact congrArg (fun xs : List (M.Val t) => Process.done (A := HList M.Val [table t n]) (.cons xs .nil))
    (Cube.flatten_interpolate r n x.1 x.2)

def check (free : Ty.isLinear V t = false) {hs : Headers V} (defs : Defs V hs) (unique : (hs.fns.map (·.key)).Nodup)
    (k : Key) : Option {ref : Member hs.fns (header t k n) // Law rows k (fun M => Defs.fnTable M defs _ ref)} := do
  let ref ← FunctionEntry.resolve hs.fns (header t k n)
  let entry := defs.functionEntry unique ref
  let .mk _ (.op _ _ (.call low) _ :: .op _ _ (.call high) _ :: _) _ := eraseFn entry.inputs entry.body | none
  let ⟨lo,lowLaw⟩ ← (TableHalves.readback t free false low n).locate entry.definitions entry.distinct
  let ⟨hi,highLaw⟩ ← (TableHalves.readback t free true high n).locate entry.definitions entry.distinct
  let expected : FunctionReadback.ArmedBody entry.earlier.fns (header t k n) := ⟨_,body rows lo hi k,rfl⟩
  let ⟨law⟩ ← entry.recognize expected (Law rows k) (value rows lo hi k _ lowLaw highLaw)
  return ⟨ref,law⟩

end ZkcFormal.Interactive.Sumcheck.TableRestriction
