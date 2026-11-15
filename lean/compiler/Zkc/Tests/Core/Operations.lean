import Zkc.Tests.Core.Elaboration

/-!
The operations that the core owns. For each written name, a function that elaborates and whose
printed form elaborates back to it; written forms with other types refused; the operations that
would copy or drop a part refused at a linear type; each meaning at a value; each domain at a
value outside it. The kernel evaluates each.
-/

namespace Zkc.Core.Operations

open Elaboration

/-- A function of one operation that the core owns, on the inputs named 0, 1, …; its result is
named after them. -/
def one (ins outs : List plain.Ty) (name : OwnedName) (types : List plain.Ty)
    (statics : List Nat) : NamedProgram plain :=
  single ins outs false (.mk ((List.range ins.length))
    [.op ⟨1⟩ ((List.range outs.length).map (· + ins.length)) (.owned name types statics)
      (List.range ins.length)]
    ((List.range outs.length).map (· + ins.length)))

/-- Whether a program elaborates and its printed form elaborates to what it elaborates to. -/
def roundTrips (named : NamedProgram plain) : Prop :=
  again named = elaborateFunctions named

def pair : plain.Ty := .tuple (.cons .nat (.cons .bool .nil))
def point : plain.Ty := .record ⟨3⟩ false (.cons .nat (.cons .bool .nil))
def handle : plain.Ty := .record ⟨4⟩ true (.cons .nat (.cons .bool .nil))

/-! ## Each written name elaborates, and its printed form elaborates back -/

def natAdd := one [.nat, .nat] [.nat] .natAdd [] []
def natSub := one [.nat, .nat] [.nat] .natSub [] []
def natMul := one [.nat, .nat] [.nat] .natMul [] []
def natDiv := one [.nat, .nat] [.nat] .natDiv [] []
def natRem := one [.nat, .nat] [.nat] .natRem [] []
def natPow := one [.nat, .nat] [.nat] .natPow [] []
def natEqual := one [.nat, .nat] [.bool] .natEqual [] []
def natLess := one [.nat, .nat] [.bool] .natLess [] []
def boolAnd := one [.bool, .bool] [.bool] .boolAnd [] []
def boolOr := one [.bool, .bool] [.bool] .boolOr [] []
def boolNot := one [.bool] [.bool] .boolNot [] []
def boolEqual := one [.bool, .bool] [.bool] .boolEqual [] []
def seqLength := one [.seq .nat none] [.nat] .seqLength [.seq .nat none] []
def seqAt := one [.seq .nat (some 3), .nat] [.nat] .seqAt [.seq .nat (some 3)] []
def seqSlice := one [.seq .nat none, .nat, .nat] [.seq .nat (some 2)] .seqSlice
  [.seq .nat none, .seq .nat (some 2)] []
def seqConcat := one [.seq .nat (some 2), .seq .nat (some 3)] [.seq .nat (some 5)] .seqConcat
  [.seq .nat (some 2), .seq .nat (some 3)] []
def seqFill := one [.nat] [.seq .nat (some 3)] .seqFill [.seq .nat (some 3)] []
def seqSized := one [.seq .nat none] [.seq .nat (some 2)] .seqSized [.seq .nat (some 2)] []
def natBelow := one [.nat] [.fin 4] .natBelow [.fin 4] []
def seqUnsized := one [.seq .nat (some 2)] [.seq .nat none] .seqUnsized [.seq .nat (some 2)] []
def finToNat := one [.fin 4] [.nat] .finToNat [.fin 4] []
def finWiden := one [.fin 4] [.fin 8] .finWiden [.fin 4, .fin 8] []
def makeSeq := one [.nat, .nat] [.seq .nat (some 2)] .make [.seq .nat (some 2)] []
def makeTuple := one [.nat, .bool] [pair] .make [pair] []
def makeRecord := one [.nat, .bool] [point] .make [point] []
def getTuple := one [pair] [.bool] .get [pair] [1]
def getRecord := one [point] [.nat] .get [point] [0]
def takeTuple := one [pair] [.nat, .bool] .take [pair] []
def takeRecord := one [handle] [.nat, .bool] .take [handle] []
def variant := one [.bool] [natOrBool] .variant [natOrBool] [1]

example : refusal natAdd = none := by decide
example : refusal natSub = none := by decide
example : refusal natMul = none := by decide
example : refusal natDiv = none := by decide
example : refusal natRem = none := by decide
example : refusal natPow = none := by decide
example : refusal natEqual = none := by decide
example : refusal natLess = none := by decide
example : refusal boolAnd = none := by decide
example : refusal boolOr = none := by decide
example : refusal boolNot = none := by decide
example : refusal boolEqual = none := by decide
example : refusal seqLength = none := by decide
example : refusal seqAt = none := by decide
example : refusal seqSlice = none := by decide
example : refusal seqConcat = none := by decide
example : refusal seqFill = none := by decide
example : refusal seqSized = none := by decide
example : refusal natBelow = none := by decide
example : refusal seqUnsized = none := by decide
example : refusal finToNat = none := by decide
example : refusal finWiden = none := by decide
example : refusal makeSeq = none := by decide
example : refusal makeTuple = none := by decide
example : refusal makeRecord = none := by decide
example : refusal getTuple = none := by decide
example : refusal getRecord = none := by decide
example : refusal takeTuple = none := by decide
example : refusal takeRecord = none := by decide
example : refusal variant = none := by decide

example : roundTrips natAdd := by rfl
example : roundTrips natSub := by rfl
example : roundTrips natMul := by rfl
example : roundTrips natDiv := by rfl
example : roundTrips natRem := by rfl
example : roundTrips natPow := by rfl
example : roundTrips natEqual := by rfl
example : roundTrips natLess := by rfl
example : roundTrips boolAnd := by rfl
example : roundTrips boolOr := by rfl
example : roundTrips boolNot := by rfl
example : roundTrips boolEqual := by rfl
example : roundTrips seqLength := by rfl
example : roundTrips seqAt := by rfl
example : roundTrips seqSlice := by rfl
example : roundTrips seqConcat := by rfl
example : roundTrips seqFill := by rfl
example : roundTrips seqSized := by rfl
example : roundTrips natBelow := by rfl
example : roundTrips seqUnsized := by rfl
example : roundTrips finToNat := by rfl
example : roundTrips finWiden := by rfl
example : roundTrips makeSeq := by rfl
example : roundTrips makeTuple := by rfl
example : roundTrips makeRecord := by rfl
example : roundTrips getTuple := by rfl
example : roundTrips getRecord := by rfl
example : roundTrips takeTuple := by rfl
example : roundTrips takeRecord := by rfl
example : roundTrips variant := by rfl

/-! ## Written forms with other types are refused -/

/-- A refusal of the operation of a function of one operation. -/
def refusedAs (name : OwnedName) (types : List plain.Ty) (statics : List Nat) :
    Option (ProgramRefusal plain) :=
  some ⟨.owned, at_ 1 1, .operation (.owned name types statics)⟩

example : refusal (one [.nat] [.nat] .seqLength [.nat] []) = refusedAs .seqLength [.nat] [] := by
  decide

/-- The two sequences of a slice are of one item type. -/
example : refusal (one [.seq .nat none, .nat, .nat] [.seq .bool none] .seqSlice
    [.seq .nat none, .seq .bool none] []) =
    refusedAs .seqSlice [.seq .nat none, .seq .bool none] [] := by
  decide

/-- A bound is widened, not narrowed. -/
example : refusal (one [.fin 8] [.fin 4] .finWiden [.fin 8, .fin 4] []) =
    refusedAs .finWiden [.fin 8, .fin 4] [] := by
  decide

/-- A sequence is made of a written number of items: its type has a size. -/
example : refusal (one [.nat] [.seq .nat none] .make [.seq .nat none] []) =
    refusedAs .make [.seq .nat none] [] := by
  decide

/-- A position past the last component. -/
example : refusal (one [pair] [.nat] .get [pair] [2]) = refusedAs .get [pair] [2] := by
  decide

/-! ## The operations that would copy or drop a part are not typed at a linear type -/

example : refusal (one [.seq token none] [.nat] .seqLength [.seq token none] []) =
    refusedAs .seqLength [.seq token none] [] := by
  decide

example : refusal (one [.seq token (some 2), .nat] [token] .seqAt [.seq token (some 2)] []) =
    refusedAs .seqAt [.seq token (some 2)] [] := by
  decide

example : refusal (one [.seq token none, .nat, .nat] [.seq token none] .seqSlice
    [.seq token none, .seq token none] []) =
    refusedAs .seqSlice [.seq token none, .seq token none] [] := by
  decide

example : refusal (one [token] [.seq token (some 2)] .seqFill [.seq token (some 2)] []) =
    refusedAs .seqFill [.seq token (some 2)] [] := by
  decide

/-- One component of a tuple with a linear component. -/
example : refusal (one [.tuple (.cons token (.cons .nat .nil))] [.nat] .get
    [.tuple (.cons token (.cons .nat .nil))] [1]) =
    refusedAs .get [.tuple (.cons token (.cons .nat .nil))] [1] := by
  decide

/-- One field of a linear record. -/
example : refusal (one [handle] [.nat] .get [handle] [0]) = refusedAs .get [handle] [0] := by
  decide

/-- Every field of a linear record is how it is used. -/
example : refusal (one [handle] [.nat, .bool] .take [handle] []) = none := by decide

/-! ## Each meaning at a value -/

abbrev model := Shapes.plainModel

example : ownedOp model .natAdd (.cons (2 : Nat) (.cons (3 : Nat) .nil)) =
    .done (.cons (5 : Nat) .nil) := rfl
example : ownedOp model .natSub (.cons (5 : Nat) (.cons (3 : Nat) .nil)) =
    .done (.cons (2 : Nat) .nil) := rfl
example : ownedOp model .natMul (.cons (2 : Nat) (.cons (3 : Nat) .nil)) =
    .done (.cons (6 : Nat) .nil) := rfl
/-- A division rounds down. -/
example : ownedOp model .natDiv (.cons (7 : Nat) (.cons (2 : Nat) .nil)) =
    .done (.cons (3 : Nat) .nil) := rfl
example : ownedOp model .natRem (.cons (7 : Nat) (.cons (2 : Nat) .nil)) =
    .done (.cons (1 : Nat) .nil) := rfl
example : ownedOp model .natPow (.cons (2 : Nat) (.cons (3 : Nat) .nil)) =
    .done (.cons (8 : Nat) .nil) := rfl
/-- A number to the power zero is one, zero too. -/
example : ownedOp model .natPow (.cons (0 : Nat) (.cons (0 : Nat) .nil)) =
    .done (.cons (1 : Nat) .nil) := rfl
example : ownedOp model .natEqual (.cons (2 : Nat) (.cons (2 : Nat) .nil)) =
    .done (.cons true .nil) := rfl
example : ownedOp model .natLess (.cons (2 : Nat) (.cons (2 : Nat) .nil)) =
    .done (.cons false .nil) := rfl
example : ownedOp model .natLess (.cons (2 : Nat) (.cons (3 : Nat) .nil)) =
    .done (.cons true .nil) := rfl
example : ownedOp model .boolAnd (.cons true (.cons false .nil)) = .done (.cons false .nil) :=
  rfl
example : ownedOp model .boolOr (.cons true (.cons false .nil)) = .done (.cons true .nil) := rfl
example : ownedOp model .boolNot (.cons true .nil) = .done (.cons false .nil) := rfl
example : ownedOp model .boolEqual (.cons false (.cons false .nil)) = .done (.cons true .nil) :=
  rfl
example : ownedOp model (.seqLength .nat none rfl) (.cons ([5, 6, 7] : List Nat) .nil) =
    .done (.cons (3 : Nat) .nil) := rfl
/-- Positions count from zero. -/
example : ownedOp model (.seqAt .nat none rfl)
    (.cons ([5, 6, 7] : List Nat) (.cons (1 : Nat) .nil)) = .done (.cons (6 : Nat) .nil) := rfl
/-- A slice excludes its upper bound. -/
example : ownedOp model (.seqSlice .nat none (some 2) rfl)
    (.cons ([5, 6, 7, 8] : List Nat) (.cons (1 : Nat) (.cons (3 : Nat) .nil))) =
    .done (.cons ([6, 7] : List Nat) .nil) := rfl
/-- A concatenation puts the first first. -/
example : ownedOp model (.seqConcat .nat (some 2) (some 1))
    (.cons ([1, 2] : List Nat) (.cons ([3] : List Nat) .nil)) =
    .done (.cons ([1, 2, 3] : List Nat) .nil) := rfl
example : ownedOp model (.seqFill .nat 3 rfl) (.cons (4 : Nat) .nil) =
    .done (.cons ([4, 4, 4] : List Nat) .nil) := rfl
example : ownedOp model (.seqSized .nat 2) (.cons ([5, 6] : List Nat) .nil) =
    .done (.cons ([5, 6] : List Nat) .nil) := rfl
example : ownedOp model (.natBelow 4) (.cons (3 : Nat) .nil) = .done (.cons (3 : Nat) .nil) :=
  rfl
example : ownedOp model (.seqUnsized .nat 2) (.cons ([5, 6] : List Nat) .nil) =
    .done (.cons ([5, 6] : List Nat) .nil) := rfl
example : ownedOp model (.finToNat 4) (.cons (3 : Nat) .nil) = .done (.cons (3 : Nat) .nil) :=
  rfl
example : ownedOp model (.finWiden 4 8 (by decide)) (.cons (3 : Nat) .nil) =
    .done (.cons (3 : Nat) .nil) := rfl
example : ownedOp model (.makeSeq .nat 2) (.cons (1 : Nat) (.cons (2 : Nat) .nil)) =
    .done (.cons ([1, 2] : List Nat) .nil) := rfl
example : ownedOp model (.makeTuple (.cons .nat (.cons .bool .nil)))
    (.cons (1 : Nat) (.cons true .nil)) = .done (.cons ((1 : Nat), true, ()) .nil) := rfl
example : ownedOp model (.makeRecord ⟨3⟩ false (.cons .nat (.cons .bool .nil)))
    (.cons (1 : Nat) (.cons true .nil)) = .done (.cons ((1 : Nat), true, ()) .nil) := rfl
example : ownedOp model (.getTuple (.cons .nat (.cons .bool .nil)) (.tail .head) rfl)
    (.cons ((1 : Nat), true, ()) .nil) = .done (.cons true .nil) := rfl
example : ownedOp model (.getRecord ⟨3⟩ (.cons .nat (.cons .bool .nil)) .head rfl)
    (.cons ((1 : Nat), true, ()) .nil) = .done (.cons (1 : Nat) .nil) := rfl
example : ownedOp model (.takeTuple (.cons .nat (.cons .bool .nil)))
    (.cons ((1 : Nat), true, ()) .nil) = .done (.cons (1 : Nat) (.cons true .nil)) := rfl
example : ownedOp model (.takeRecord ⟨4⟩ true (.cons .nat (.cons .bool .nil)))
    (.cons ((1 : Nat), true, ()) .nil) = .done (.cons (1 : Nat) (.cons true .nil)) := rfl
example : ownedOp model (.variant ⟨7⟩ (.cons .nat (.cons .bool .nil)) .head)
    (.cons (2 : Nat) .nil) = .done (.cons (.inl 2) .nil) := rfl

/-! ## Each domain at a value outside it -/

example : ownedOp model .natSub (.cons (3 : Nat) (.cons (5 : Nat) .nil)) = .halt .undefined :=
  rfl
example : ownedOp model .natDiv (.cons (3 : Nat) (.cons (0 : Nat) .nil)) = .halt .undefined :=
  rfl
example : ownedOp model .natRem (.cons (3 : Nat) (.cons (0 : Nat) .nil)) = .halt .undefined :=
  rfl
example : ownedOp model (.seqAt .nat none rfl) (.cons ([5, 6] : List Nat) (.cons (2 : Nat) .nil)) =
    .halt .undefined := rfl
/-- The first bound of a slice is at most the second. -/
example : ownedOp model (.seqSlice .nat none none rfl)
    (.cons ([5, 6] : List Nat) (.cons (2 : Nat) (.cons (1 : Nat) .nil))) = .halt .undefined :=
  rfl
/-- The second bound of a slice is at most the length. -/
example : ownedOp model (.seqSlice .nat none none rfl)
    (.cons ([5, 6] : List Nat) (.cons (1 : Nat) (.cons (3 : Nat) .nil))) = .halt .undefined :=
  rfl
/-- Into a sized result, the bounds are as far apart as its size. -/
example : ownedOp model (.seqSlice .nat none (some 3) rfl)
    (.cons ([5, 6, 7] : List Nat) (.cons (0 : Nat) (.cons (2 : Nat) .nil))) = .halt .undefined :=
  rfl
example : ownedOp model (.seqSized .nat 2) (.cons ([5] : List Nat) .nil) = .halt .undefined :=
  rfl
example : ownedOp model (.natBelow 4) (.cons (4 : Nat) .nil) = .halt .undefined := rfl

end Zkc.Core.Operations
