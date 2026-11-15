module

public import Zkc.Core.Program.Term

@[expose] public section

/-!
Linear use: every value of a linear type is used once. It is defined by its decision, which
counts the uses of the values of linear type only and says, where a value is not used as it
must be, which value and where.
-/

namespace Zkc.Core

/-- A value of a linear type that is not used as it must be: the blocks and the instruction of
the place (no instruction for an input of the body); its position, among the values bound
there or, for a value from around the place, in the scope there, the innermost first; how often
it is used; and whether it comes from around the place (a choice, a case analysis or a loop
whose regions use it differently) rather than being bound there. -/
structure Misuse where
  blocks : List (Key × Nat)
  instruction : Option Key
  position : Nat
  found : Nat
  around : Bool
deriving DecidableEq

/-- The uses of two parts, added. -/
def addUses (first second : List Nat) : List Nat := List.zipWith (· + ·) first second

/-- The uses of two regions of which one runs: the more often of the two, for each value. -/
def joinUses (first second : List Nat) : List Nat := List.zipWith max first second

section
variable {D : Dialect} (linear : D.Ty → Bool)

/-- The number of values of linear type among types. -/
def linearCount : List D.Ty → Nat
  | [] => 0
  | τ :: types => cond (linear τ) (linearCount types + 1) (linearCount types)

/-- The position among the types of the first value of linear type whose count is not one,
with its count, reading the counts of the values of linear type in order. -/
def misuseAmong : (items : List D.Ty) → List Nat → Option (Nat × Nat)
  | [], _ => none
  | τ :: items, counts =>
      cond (linear τ)
        (match counts with
          | c :: counts =>
              cond (Nat.beq c 1) ((misuseAmong items counts).map fun m => (m.1 + 1, m.2))
                (some (0, c))
          | [] => some (0, 0))
        ((misuseAmong items counts).map fun m => (m.1 + 1, m.2))

/-- A list of `width` counts, one at a position and none elsewhere. -/
def oneAt : Nat → Nat → List Nat
  | _, 0 => []
  | 0, width + 1 => 1 :: List.replicate width 0
  | position + 1, width + 1 => 0 :: oneAt position width

/-- The position of a variable among the values of linear type of its context, the innermost
first. -/
def Var.linearIndex : {Γ : List D.Ty} → {a : D.Ty} → Var Γ a → Nat
  | _, _, .head => 0
  | b :: _, _, .tail x => cond (linear b) (Var.linearIndex x + 1) (Var.linearIndex x)

/-- One use of a variable, counted for the `width` values of linear type of its context: it
walks the variable only when its type is linear. -/
def Var.linearUses (width : Nat) {Γ : List D.Ty} {a : D.Ty} (x : Var Γ a) : List Nat :=
  cond (linear a) (oneAt (Var.linearIndex linear x) width) (List.replicate width 0)

/-- The uses of a list of variables, counted for the values of linear type. -/
def HList.linearUses (width : Nat) {Γ : List D.Ty} :
    {items : List D.Ty} → HList (Var Γ) items → List Nat
  | [], .nil => List.replicate width 0
  | _ :: _, .cons x rest => addUses (Var.linearUses linear width x) (HList.linearUses width rest)

/-- The use of the count of a loop, counted for the values of linear type. -/
def Times.linearUses (width : Nat) {w : D.Who} {Γ : List D.Ty} : Times D w Γ → List Nat
  | .fixed _ => List.replicate width 0
  | .value count _ => Var.linearUses linear width count

/-- The position in a context of the first value of linear type whose counts differ between
two regions, with its count in the second. -/
def firstDifference : (Γ : List D.Ty) → List Nat → List Nat → Nat × Nat
  | [], _, _ => (0, 0)
  | τ :: Γ, first, second =>
      cond (linear τ)
        (match first, second with
          | a :: first, b :: second =>
              cond (Nat.beq a b)
                (let found := firstDifference Γ first second; (found.1 + 1, found.2)) (0, b)
          | _, _ => (0, 0))
        (let found := firstDifference Γ first second; (found.1 + 1, found.2))

/-- The position in a context of the first value of linear type that is used, with its
count. -/
def firstUsed : (Γ : List D.Ty) → List Nat → Nat × Nat
  | [], _ => (0, 0)
  | τ :: Γ, counts =>
      cond (linear τ)
        (match counts with
          | c :: counts =>
              cond (Nat.beq c 0) (let found := firstUsed Γ counts; (found.1 + 1, found.2)) (0, c)
          | [] => (0, 0))
        (let found := firstUsed Γ counts; (found.1 + 1, found.2))

/-- What the arms of a case analysis use of the values around it, counted for the values of
linear type: when every arm uses each of them as often as the first, what any arm uses. -/
def joinArms (Γ : List D.Ty) (blocks : List (Key × Nat)) (key : Key) (width : Nat) :
    List (List Nat) → Except Misuse (List Nat)
  | [] => .ok (List.replicate width 0)
  | first :: others =>
      if others.all (fun other => decide (first = other)) then .ok (others.foldl joinUses first)
      else
        let found := firstDifference linear Γ first
          ((others.find? fun other => !decide (first = other)).getD first)
        .error ⟨blocks, some key, found.1, found.2, true⟩

mutual
  /-- How often each value of linear type of the context is used on every path, the innermost
  first, in a context with `width` values of linear type: an operand or a returned value is a
  use; where the regions of a choice or the arms of a case analysis agree, what any of them uses;
  the body of an attempt counted once, as the program is written. Or else the first value of
  linear type that is not used as it must be, with where: one bound by an instruction and not
  used once (its position among the values that the instruction binds); or one from around a
  choice, a case analysis or a loop whose regions use it differently, or whose loop body uses
  it at all (its position in the context there). -/
  def Term.linearUses (blocks : List (Key × Nat)) (width : Nat) :
      {Γ outs : List D.Ty} → Term D Γ outs → Except Misuse (List Nat)
    | _, _, .ret xs => .ok (HList.linearUses linear width xs)
    | _, _, .op (res := res) key _ args rest =>
        match Term.linearUses blocks (linearCount linear res + width) rest with
        | .error misuse => .error misuse
        | .ok inner =>
            match misuseAmong linear res inner with
            | some found => .error ⟨blocks, some key, found.1, found.2, false⟩
            | none =>
                .ok (addUses (inner.drop (linearCount linear res))
                  (HList.linearUses linear width args))
    | _, _, .guard _ _ c _ _ rest =>
        match Term.linearUses blocks width rest with
        | .error misuse => .error misuse
        | .ok inner => .ok (addUses inner (Var.linearUses linear width c))
    | Γ, _, .choose (mid := mid) key _ c _ _ onTrue onFalse rest =>
        match Term.linearUses blocks width onTrue with
        | .error misuse => .error misuse
        | .ok whenTrue =>
            match Term.linearUses blocks width onFalse with
            | .error misuse => .error misuse
            | .ok whenFalse =>
                match Term.linearUses blocks (linearCount linear mid + width) rest with
                | .error misuse => .error misuse
                | .ok inner =>
                    if whenTrue = whenFalse then
                      match misuseAmong linear mid inner with
                      | some found => .error ⟨blocks, some key, found.1, found.2, false⟩
                      | none =>
                          .ok (addUses (addUses (joinUses whenTrue whenFalse)
                            (inner.drop (linearCount linear mid))) (Var.linearUses linear width c))
                    else
                      let found := firstDifference linear Γ whenTrue whenFalse
                      .error ⟨blocks, some key, found.1, found.2, true⟩
    | Γ, _, .cases (mid := mid) (payloads := payloads) key _ x _ _ arms rest =>
        match Arms.linearUses blocks key width 0 arms with
        | .error misuse => .error misuse
        | .ok armUses =>
            match Term.linearUses blocks (linearCount linear mid + width) rest with
            | .error misuse => .error misuse
            | .ok inner =>
                match joinArms linear Γ blocks key width armUses with
                | .error misuse => .error misuse
                | .ok outer =>
                    match misuseAmong linear mid inner with
                    | some found =>
                        .error ⟨blocks, some key, payloads.length + found.1, found.2, false⟩
                    | none =>
                        .ok (addUses (addUses outer (inner.drop (linearCount linear mid)))
                          (Var.linearUses linear width x))
    | Γ, _, .loop (carried := carried) (each := each) key w times _ init body rest =>
        match Term.linearUses blocks (linearCount linear (D.index w :: carried) + width) body with
        | .error misuse => .error misuse
        | .ok inBody =>
            match Term.linearUses blocks
                (linearCount linear (carried ++ each.map (D.collected times.size)) + width)
                rest with
            | .error misuse => .error misuse
            | .ok inner =>
                match misuseAmong linear (D.index w :: carried) inBody with
                | some found => .error ⟨blocks, some key, found.1, found.2, false⟩
                | none =>
                    if (inBody.drop (linearCount linear (D.index w :: carried))).all
                        (Nat.beq · 0) then
                      match misuseAmong linear (carried ++ each.map (D.collected times.size))
                          inner with
                      | some found =>
                          .error ⟨blocks, some key, carried.length + 1 + found.1, found.2, false⟩
                      | none =>
                          .ok (addUses
                            (addUses (inBody.drop (linearCount linear (D.index w :: carried)))
                              (inner.drop (linearCount linear
                                (carried ++ each.map (D.collected times.size)))))
                            (addUses (HList.linearUses linear width init)
                              (Times.linearUses linear width times)))
                    else
                      let found := firstUsed linear Γ
                        (inBody.drop (linearCount linear (D.index w :: carried)))
                      .error ⟨blocks, some key, found.1, found.2, true⟩
    | _, _, .block (mid := mid) key number body rest =>
        match Term.linearUses (blocks ++ [(key, number)]) width body with
        | .error misuse => .error misuse
        | .ok inBody =>
            match Term.linearUses blocks (linearCount linear mid + width) rest with
            | .error misuse => .error misuse
            | .ok inner =>
                match misuseAmong linear mid inner with
                | some found => .error ⟨blocks, some key, found.1, found.2, false⟩
                | none => .ok (addUses inBody (inner.drop (linearCount linear mid)))
    | _, _, .attempt (mid := mid) key w _ body rest =>
        match Term.linearUses blocks (linearCount linear [D.index w] + width) body with
        | .error misuse => .error misuse
        | .ok inBody =>
            match Term.linearUses blocks (linearCount linear mid + width) rest with
            | .error misuse => .error misuse
            | .ok inner =>
                match misuseAmong linear [D.index w] inBody with
                | some found => .error ⟨blocks, some key, found.1, found.2, false⟩
                | none =>
                    match misuseAmong linear mid inner with
                    | some found => .error ⟨blocks, some key, found.1 + 1, found.2, false⟩
                    | none =>
                        .ok (addUses (inBody.drop (linearCount linear [D.index w]))
                          (inner.drop (linearCount linear mid)))
  /-- What the arms of a case analysis use, each counted for the values of linear type around
  it; or the first arm (by its position from `index`) whose payload is linear and not used
  once. -/
  def Arms.linearUses (blocks : List (Key × Nat)) (key : Key) (width : Nat) (index : Nat) :
      {Γ mid payloads : List D.Ty} → Arms D Γ mid payloads → Except Misuse (List (List Nat))
    | _, _, _, .nil => .ok []
    | _, _, _, .cons (payload := payload) arm rest =>
        match Term.linearUses blocks (linearCount linear [payload] + width) arm with
        | .error misuse => .error misuse
        | .ok inArm =>
            match Arms.linearUses blocks key width (index + 1) rest with
            | .error misuse => .error misuse
            | .ok others =>
                match misuseAmong linear [payload] inArm with
                | some found => .error ⟨blocks, some key, index, found.2, false⟩
                | none => .ok (inArm.drop (linearCount linear [payload]) :: others)
end

/-- The value of a linear type at which the decision of linear use fails: the first value of
linear type that is not used once, with where; nothing when every one is used once. -/
def Term.misuse {Γ outs : List D.Ty} (t : Term D Γ outs) : Option Misuse :=
  match Term.linearUses linear [] (linearCount linear Γ) t with
  | .error misuse => some misuse
  | .ok kept => (misuseAmong linear Γ kept).map fun found => ⟨[], none, found.1, found.2, false⟩

/-- Every value of a linear type among the inputs of a body is used once, and so is every one
bound inside it; the regions of a choice and the arms of a case analysis use each value of a
linear type from around them equally often, and a loop body uses none from around it. -/
def Term.UsedOnce {Γ outs : List D.Ty} (t : Term D Γ outs) : Prop :=
  t.misuse linear = none

/-- Whether every value of a linear type is used once in a body. -/
instance Term.decideUsedOnce {Γ outs : List D.Ty} (t : Term D Γ outs) :
    Decidable (t.UsedOnce linear) :=
  inferInstanceAs (Decidable (t.misuse linear = none))

end

end Zkc.Core
