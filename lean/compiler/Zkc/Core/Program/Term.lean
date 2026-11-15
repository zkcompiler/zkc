module

public import Zkc.Core.Program.Vocabulary

@[expose] public section

/-!
Terms: one type, generic in a dialect.

A term is typed in a lexical context and returns values; a nested region sees the context
around it. A dialect gives its types, its operations, who performs a form of control and what
they may guard, choose, repeat and give. An operation, a guard, a choice, a loop, a block and
an attempt each have one key, which the producer gives; with the blocks around it, it is the
instruction's address. What elaboration decides about a body is said here: distinct addresses,
and linear values used once.
-/

namespace Zkc.Core

/-! ## Terms -/

structure Dialect where
  Ty : Type
  /-- An operation, with the types of its operands and of its results. -/
  Op : List Ty → List Ty → Type
  /-- Who performs a guard, a choice or a loop. -/
  Who : Type
  /-- The type is a condition that they may guard or choose on. -/
  Condition : Who → Ty → Prop
  /-- The type is a variant that they may choose on; inside the region of each alternative
  its payload has the type given. -/
  Alternatives : Who → Ty → List Ty → Prop
  /-- The type is a count that they may repeat by. -/
  Count : Who → Ty → Prop
  /-- The type of the iteration number inside their loop, and of the number of their
  attempt. -/
  index : Who → Ty
  /-- They may own an attempt. -/
  Attempt : Who → Prop
  /-- A region of their choice or loop may give a value of the type. -/
  Gives : Who → Ty → Prop
  /-- The type of the sequence of the values of a type that the iterations collect: of the
  size given, for a loop of a written number of iterations. -/
  collected : Option Nat → Ty → Ty

/-- How often a loop runs: a written number of times, or as often as a count that its
performers hold says. -/
inductive Times (D : Dialect) (w : D.Who) (Γ : List D.Ty) where
  | fixed (n : Nat)
  | value {t : D.Ty} (count : Var Γ t) (ok : D.Count w t)

/-- The number of iterations, when it is written. -/
def Times.size {D : Dialect} {w : D.Who} {Γ : List D.Ty} : Times D w Γ → Option Nat
  | .fixed n => some n
  | .value .. => none

mutual
  inductive Term (D : Dialect) : List D.Ty → List D.Ty → Type where
    | ret {Γ outs} (xs : HList (Var Γ) outs) : Term D Γ outs
    | op {Γ outs ins res} (key : Key) (o : D.Op ins res) (args : HList (Var Γ) ins)
        (rest : Term D (res ++ Γ) outs) : Term D Γ outs
    /-- They check a condition, and stop when it is false. -/
    | guard {Γ outs t} (key : Key) (w : D.Who) (c : Var Γ t) (ok : D.Condition w t)
        (why : Reason) (rest : Term D Γ outs) : Term D Γ outs
    | choose {Γ outs mid t} (key : Key) (w : D.Who) (c : Var Γ t) (ok : D.Condition w t)
        (gives : ∀ a, a ∈ mid → D.Gives w a) (onTrue onFalse : Term D Γ mid)
        (rest : Term D (mid ++ Γ) outs) : Term D Γ outs
    | cases {Γ outs mid t payloads} (key : Key) (w : D.Who) (x : Var Γ t)
        (ok : D.Alternatives w t payloads) (gives : ∀ a, a ∈ mid → D.Gives w a)
        (arms : Arms D Γ mid payloads) (rest : Term D (mid ++ Γ) outs) : Term D Γ outs
    /-- They repeat a region as often as `times` says. The region has the iteration number
    and the carried values; it returns the carried values and one value of each collected
    type. The loop gives the last carried values and a sequence per collected type, of the
    written size when the number of iterations is written. -/
    | loop {Γ outs carried each} (key : Key) (w : D.Who) (times : Times D w Γ)
        (gives : ∀ a, a ∈ carried ++ each → D.Gives w a) (init : HList (Var Γ) carried)
        (body : Term D (D.index w :: (carried ++ Γ)) (carried ++ each))
        (rest : Term D ((carried ++ each.map (D.collected times.size)) ++ Γ) outs) :
        Term D Γ outs
    /-- One iteration of a loop whose iterations differ in type, written out: the body runs
    once, under the iteration of the loop `key` with the number given. Nobody performs it. -/
    | block {Γ outs mid} (key : Key) (number : Nat) (body : Term D Γ mid)
        (rest : Term D (mid ++ Γ) outs) : Term D Γ outs
    /-- An attempt that `w` own: the body runs with the number of the attempt, which is `0` in
    the program as written; where a deployed role retries it, the body runs again, with the
    next number, after it stops with `abort`. The rest runs once, after the body. The body is
    in the scope around it, and every role may act in it. -/
    | attempt {Γ outs mid} (key : Key) (w : D.Who) (owns : D.Attempt w)
        (body : Term D (D.index w :: Γ) mid) (rest : Term D (mid ++ Γ) outs) : Term D Γ outs
  /-- A region per alternative, each with its payload. -/
  inductive Arms (D : Dialect) : List D.Ty → List D.Ty → List D.Ty → Type where
    | nil {Γ mid} : Arms D Γ mid []
    | cons {Γ mid payload payloads} (arm : Term D (payload :: Γ) mid)
        (rest : Arms D Γ mid payloads) : Arms D Γ mid (payload :: payloads)
end

/-! ## Addresses -/

mutual
  /-- The addresses of the instructions of a body: the blocks around each (the key of its
  stepped loop and its number, the outermost first) and its key. A block qualifies the
  instructions in it; the body of a loop and of an attempt and the regions of a choice do
  not. -/
  def Term.addresses {D : Dialect} (blocks : List (Key × Nat)) :
      {Γ outs : List D.Ty} → Term D Γ outs → List (List (Key × Nat) × Key)
    | _, _, .ret _ => []
    | _, _, .op key _ _ rest => (blocks, key) :: Term.addresses blocks rest
    | _, _, .guard key _ _ _ _ rest => (blocks, key) :: Term.addresses blocks rest
    | _, _, .choose key _ _ _ _ onTrue onFalse rest =>
        (blocks, key) :: (Term.addresses blocks onTrue ++ Term.addresses blocks onFalse ++
          Term.addresses blocks rest)
    | _, _, .cases key _ _ _ _ arms rest =>
        (blocks, key) :: (Arms.addresses blocks arms ++ Term.addresses blocks rest)
    | _, _, .loop key _ _ _ _ body rest =>
        (blocks, key) :: (Term.addresses blocks body ++ Term.addresses blocks rest)
    | _, _, .block key number body rest =>
        Term.addresses (blocks ++ [(key, number)]) body ++ Term.addresses blocks rest
    | _, _, .attempt key _ _ body rest =>
        (blocks, key) :: (Term.addresses blocks body ++ Term.addresses blocks rest)
  def Arms.addresses {D : Dialect} (blocks : List (Key × Nat)) :
      {Γ mid payloads : List D.Ty} → Arms D Γ mid payloads → List (List (Key × Nat) × Key)
    | _, _, _, .nil => []
    | _, _, _, .cons arm rest => Term.addresses blocks arm ++ Arms.addresses blocks rest
end

mutual
  /-- The keys of the blocks of a body. -/
  def Term.blockKeys {D : Dialect} : {Γ outs : List D.Ty} → Term D Γ outs → List Key
    | _, _, .ret _ => []
    | _, _, .op _ _ _ rest => Term.blockKeys rest
    | _, _, .guard _ _ _ _ _ rest => Term.blockKeys rest
    | _, _, .choose _ _ _ _ _ onTrue onFalse rest =>
        Term.blockKeys onTrue ++ Term.blockKeys onFalse ++ Term.blockKeys rest
    | _, _, .cases _ _ _ _ _ arms rest => Arms.blockKeys arms ++ Term.blockKeys rest
    | _, _, .loop _ _ _ _ _ body rest => Term.blockKeys body ++ Term.blockKeys rest
    | _, _, .block key _ body rest => key :: (Term.blockKeys body ++ Term.blockKeys rest)
    | _, _, .attempt _ _ _ body rest => Term.blockKeys body ++ Term.blockKeys rest
  def Arms.blockKeys {D : Dialect} : {Γ mid payloads : List D.Ty} → Arms D Γ mid payloads →
      List Key
    | _, _, _, .nil => []
    | _, _, _, .cons arm rest => Term.blockKeys arm ++ Arms.blockKeys rest
end

/-- Every instruction of a body has its own address, and no block has the key of an
instruction: a site and a place name one instruction. The blocks of one stepped loop repeat
keys, each under its number. -/
def Term.Distinct {D : Dialect} {Γ outs : List D.Ty} (t : Term D Γ outs) : Prop :=
  (decide (t.addresses []).Nodup &&
    t.blockKeys.all fun k => (t.addresses []).all fun address => address.2 != k) = true

/-! ## Linear values are used once -/

section
variable {α : Type}

/-- One use of a variable, as a count per variable of the context, the innermost first. -/
def Var.uses : {Γ : List α} → {a : α} → Var Γ a → List Nat
  | _ :: rest, _, .head => 1 :: List.replicate rest.length 0
  | _ :: _, _, .tail x => 0 :: Var.uses x

/-- The uses of two parts, added. -/
def addUses (first second : List Nat) : List Nat := List.zipWith (· + ·) first second

/-- The uses of a list of variables. -/
def HList.uses {Γ : List α} : {items : List α} → HList (Var Γ) items → List Nat
  | [], .nil => List.replicate Γ.length 0
  | _ :: _, .cons x rest => addUses (Var.uses x) (HList.uses rest)

end

section
variable {D : Dialect} (linear : D.Ty → Bool)

/-- Each value of a linear type among those bound at the front is used once. -/
def boundOnce (items : List D.Ty) (counts : List Nat) : Bool :=
  (items.zip counts).all fun entry => !linear entry.1 || entry.2 == 1

/-- No value of a linear type among these is used. -/
def unusedLinear (items : List D.Ty) (counts : List Nat) : Bool :=
  (items.zip counts).all fun entry => !linear entry.1 || entry.2 == 0

/-- The use of the count of a loop. -/
def Times.uses {w : D.Who} {Γ : List D.Ty} : Times D w Γ → List Nat
  | .fixed _ => List.replicate Γ.length 0
  | .value count _ => Var.uses count

/-- Two regions use each value of a linear type among these equally often. -/
def agreeLinear (items : List D.Ty) (first second : List Nat) : Bool :=
  (items.zip (first.zip second)).all fun entry => !linear entry.1 || entry.2.1 == entry.2.2

/-- The uses of two regions of which one runs: the more often of the two, for each value. -/
def joinUses (first second : List Nat) : List Nat := List.zipWith max first second

mutual
  /-- The uses of the variables of the context on every path, the innermost first: an operand
  or a returned value is a use. It is `none` when a value of a linear type bound inside is not
  used exactly once, when two arms of a choice use a value of a linear type from around them
  differently, or when a loop body uses a value of a linear type from around it. A value of
  another type may be copied or dropped: where arms differ on it, its count is the larger. The
  body of an attempt is counted once, as the program is written. -/
  def Term.uses : {Γ outs : List D.Ty} → Term D Γ outs → Option (List Nat)
    | _, _, .ret xs => some (HList.uses xs)
    | _, _, .op (res := res) _ _ args rest => do
        let inner ← Term.uses rest
        if boundOnce linear res inner then some (addUses (inner.drop res.length) (HList.uses args))
        else none
    | _, _, .guard _ _ c _ _ rest => do
        let inner ← Term.uses rest
        some (addUses inner (Var.uses c))
    | Γ, _, .choose (mid := mid) _ _ c _ _ onTrue onFalse rest => do
        let whenTrue ← Term.uses onTrue
        let whenFalse ← Term.uses onFalse
        let inner ← Term.uses rest
        if agreeLinear linear Γ whenTrue whenFalse ∧ boundOnce linear mid inner = true then
          some (addUses (addUses (joinUses whenTrue whenFalse) (inner.drop mid.length))
            (Var.uses c))
        else none
    | Γ, _, .cases (mid := mid) _ _ x _ _ arms rest => do
        let armUses ← Arms.uses arms
        let inner ← Term.uses rest
        let outer ← match armUses with
          | [] => some (List.replicate Γ.length 0)
          | first :: others =>
              if others.all (agreeLinear linear Γ first) then
                some (others.foldl joinUses first)
              else none
        if boundOnce linear mid inner then
          some (addUses (addUses outer (inner.drop mid.length)) (Var.uses x))
        else none
    | Γ, _, .loop (carried := carried) (each := each) _ w times _ init body rest => do
        let inBody ← Term.uses body
        let inner ← Term.uses rest
        let outer := inBody.drop (carried.length + 1)
        let bound := carried ++ each.map (D.collected times.size)
        if boundOnce linear (D.index w :: carried) inBody ∧ unusedLinear linear Γ outer = true ∧
            boundOnce linear bound inner = true then
          some (addUses (addUses outer (inner.drop bound.length))
            (addUses (HList.uses init) (Times.uses times)))
        else none
    | _, _, .block (mid := mid) _ _ body rest => do
        let inBody ← Term.uses body
        let inner ← Term.uses rest
        if boundOnce linear mid inner then some (addUses inBody (inner.drop mid.length))
        else none
    | _, _, .attempt (mid := mid) _ w _ body rest => do
        let inBody ← Term.uses body
        let inner ← Term.uses rest
        if boundOnce linear [D.index w] inBody ∧ boundOnce linear mid inner = true then
          some (addUses (inBody.drop 1) (inner.drop mid.length))
        else none
  /-- The uses of the values around a choice, per arm. -/
  def Arms.uses : {Γ mid payloads : List D.Ty} → Arms D Γ mid payloads → Option (List (List Nat))
    | _, _, _, .nil => some []
    | _, _, _, .cons (payload := payload) arm rest => do
        let inArm ← Term.uses arm
        let others ← Arms.uses rest
        if boundOnce linear [payload] inArm then some (inArm.drop 1 :: others) else none
end

/-- The values of a linear type among the inputs of a body are each used once, and so is
every one bound inside it. -/
def Term.UsedOnce {Γ outs : List D.Ty} (t : Term D Γ outs) : Prop :=
  ∃ counts, t.uses linear = some counts ∧ boundOnce linear Γ counts = true

end


mutual
  /-- The keys of the definitions that a term calls or applies, by its operations. -/
  def Term.calls {D : Dialect} (opCalls : ∀ {ins res : List D.Ty}, D.Op ins res → List Key) :
      {Γ outs : List D.Ty} → Term D Γ outs → List Key
    | _, _, .ret _ => []
    | _, _, .op _ o _ rest => opCalls o ++ Term.calls opCalls rest
    | _, _, .guard _ _ _ _ _ rest => Term.calls opCalls rest
    | _, _, .choose _ _ _ _ _ onTrue onFalse rest =>
        Term.calls opCalls onTrue ++ Term.calls opCalls onFalse ++ Term.calls opCalls rest
    | _, _, .cases _ _ _ _ _ arms rest => Arms.calls opCalls arms ++ Term.calls opCalls rest
    | _, _, .loop _ _ _ _ _ body rest => Term.calls opCalls body ++ Term.calls opCalls rest
    | _, _, .block _ _ body rest => Term.calls opCalls body ++ Term.calls opCalls rest
    | _, _, .attempt _ _ _ body rest => Term.calls opCalls body ++ Term.calls opCalls rest
  def Arms.calls {D : Dialect} (opCalls : ∀ {ins res : List D.Ty}, D.Op ins res → List Key) :
      {Γ mid payloads : List D.Ty} → Arms D Γ mid payloads → List Key
    | _, _, _, .nil => []
    | _, _, _, .cons arm rest => Term.calls opCalls arm ++ Arms.calls opCalls rest
end

end Zkc.Core
