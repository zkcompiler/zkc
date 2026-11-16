module

public import Zkc.Core.Program.Term

@[expose] public section

/-!
Linear use: every value of a linear type is used once. It is defined by its decision, which
counts the uses of the values of linear type only, by name, and says, where a value is not used
as it must be, which value (by its name) and where.

The uses below a point are counted per name. Where a binding binds names, the counts of the
names that it binds are read in the term that it binds them in, and then dropped: so the counts
that a region gives are those of the names around it, and a name that a region binds again
hides the one around it, as the context does. A body is decided with the names of the inputs of
its definition, as single assignment is (`Term.BoundOnce`): the context of a definition's body is
its inputs, and they are the values that the body has from outside.
-/

namespace Zkc.Core

/-- A value of a linear type that is not used as it must be: the blocks and the instruction of
the place (no instruction for an input of the body); its name; how often it is used; and
whether it comes from around the place (a choice, a case analysis or a loop whose regions use it
differently) rather than being bound there. -/
structure Misuse where
  blocks : List (Key × Nat)
  instruction : Option Key
  name : Name
  found : Nat
  around : Bool
deriving DecidableEq

/-! ## Counts of uses by name -/

/-- How often names are used: names with their counts, each name listed once. A name that is
not listed is not used. -/
abbrev Uses : Type := List (Name × Nat)

namespace Uses

/-- How often a name is used. -/
def count : Uses → Name → Nat
  | [], _ => 0
  | (used, uses) :: rest, name => cond (Nat.beq used name) uses (count rest name)

/-- The counts with `more` uses of a name added. -/
def addTo (name : Name) (more : Nat) : Uses → Uses
  | [] => [(name, more)]
  | (used, uses) :: rest =>
      cond (Nat.beq used name) ((used, uses + more) :: rest) ((used, uses) :: addTo name more rest)

/-- The counts of two parts, added. -/
def add (first second : Uses) : Uses :=
  first.foldr (fun entry sum => addTo entry.1 entry.2 sum) second

/-- The counts without the names given: those of a binding, once the term in which it binds them
is counted. -/
def drop (uses : Uses) (names : List Name) : Uses :=
  uses.filter fun entry => !names.any (Nat.beq entry.1)

/-- A name that two counts use differently often, with its count in the second; none when they
use every name equally often. -/
def differ (first second : Uses) : Option (Name × Nat) :=
  match first.find? (fun entry => !Nat.beq entry.2 (second.count entry.1)) with
  | some entry => some (entry.1, second.count entry.1)
  | none => second.find? fun entry => !Nat.beq entry.2 (first.count entry.1)

/-- A name that is used, with its count; none when no name is. -/
def used (uses : Uses) : Option (Name × Nat) :=
  uses.find? fun entry => !Nat.beq entry.2 0

end Uses

section
variable {D : Dialect} (linear : D.Ty → Bool)

/-- One use of a variable, counted when its type is linear. -/
def Var.linearUses {Γ : Ctx D.Ty} {a : D.Ty} (x : Var Γ a) : Uses :=
  cond (linear a) [(x.name, 1)] []

/-- The uses of a list of variables, counted for the values of linear type. -/
def HList.linearUses {Γ : Ctx D.Ty} : {items : List D.Ty} → HList (Var Γ) items → Uses
  | [], .nil => []
  | _ :: _, .cons x rest => (Var.linearUses linear x).add (HList.linearUses rest)

/-- The use of the count of a loop, counted when its type is linear. -/
def Times.linearUses {w : D.Who} {Γ : Ctx D.Ty} : Times D w Γ → Uses
  | .fixed _ => []
  | .value count _ => Var.linearUses linear count

/-- The first value of linear type among the names of a binding that the counts of the term in
which it binds them do not use once, with its count. A name that the binding binds again after
it is hidden by the later one, and is not used. -/
def misuseAmong (uses : Uses) : {types : List D.Ty} → Names types → Option (Name × Nat)
  | [], .nil => none
  | τ :: _, .cons name rest =>
      let found := cond ((Names.toList rest).any (Nat.beq name)) 0 (uses.count name)
      cond (linear τ && !Nat.beq found 1) (some (name, found)) (misuseAmong uses rest)

/-- What the arms of a case analysis use of the values around it: when every arm uses each of
them as often as the first, what the first uses. -/
def joinArms (blocks : List (Key × Nat)) (key : Key) : List Uses → Except Misuse Uses
  | [] => .ok []
  | first :: others =>
      match others.findSome? fun other => first.differ other with
      | none => .ok first
      | some found => .error ⟨blocks, some key, found.1, found.2, true⟩

mutual
  /-- How often each value of linear type from around a term is used on every path, by name: an
  operand or a returned value is a use; where the regions of a choice or the arms of a case
  analysis agree, what any of them uses; the body of an attempt counted once, as the program is
  written. Or else the first value of linear type that is not used as it must be, with where:
  one bound by an instruction (as a result, or as an input of one of its regions) and not used
  once; or one from around a choice, a case analysis or a loop whose regions use it differently,
  or whose loop body uses it at all. -/
  def Term.linearUses (blocks : List (Key × Nat)) :
      {Γ : Ctx D.Ty} → {outs : List D.Ty} → Term D Γ outs → Except Misuse Uses
    | _, _, .ret xs => .ok (HList.linearUses linear xs)
    | _, _, .op key _ args results rest =>
        match Term.linearUses blocks rest with
        | .error misuse => .error misuse
        | .ok inner =>
            match misuseAmong linear inner results with
            | some found => .error ⟨blocks, some key, found.1, found.2, false⟩
            | none => .ok ((inner.drop results.toList).add (HList.linearUses linear args))
    | _, _, .guard _ _ c _ _ rest =>
        match Term.linearUses blocks rest with
        | .error misuse => .error misuse
        | .ok inner => .ok (inner.add (Var.linearUses linear c))
    | _, _, .choose key _ c _ _ onTrue onFalse results rest =>
        match Term.linearUses blocks onTrue with
        | .error misuse => .error misuse
        | .ok whenTrue =>
            match Term.linearUses blocks onFalse with
            | .error misuse => .error misuse
            | .ok whenFalse =>
                match Term.linearUses blocks rest with
                | .error misuse => .error misuse
                | .ok inner =>
                    match whenTrue.differ whenFalse with
                    | none =>
                        match misuseAmong linear inner results with
                        | some found => .error ⟨blocks, some key, found.1, found.2, false⟩
                        | none =>
                            .ok ((whenTrue.add (inner.drop results.toList)).add
                              (Var.linearUses linear c))
                    | some found => .error ⟨blocks, some key, found.1, found.2, true⟩
    | _, _, .cases key _ x _ _ arms results rest =>
        match Arms.linearUses blocks key arms with
        | .error misuse => .error misuse
        | .ok armUses =>
            match Term.linearUses blocks rest with
            | .error misuse => .error misuse
            | .ok inner =>
                match joinArms blocks key armUses with
                | .error misuse => .error misuse
                | .ok outer =>
                    match misuseAmong linear inner results with
                    | some found => .error ⟨blocks, some key, found.1, found.2, false⟩
                    | none =>
                        .ok ((outer.add (inner.drop results.toList)).add (Var.linearUses linear x))
    | _, _, .loop key _ times _ init inputs body results rest =>
        match Term.linearUses blocks body with
        | .error misuse => .error misuse
        | .ok inBody =>
            match Term.linearUses blocks rest with
            | .error misuse => .error misuse
            | .ok inner =>
                match misuseAmong linear inBody inputs with
                | some found => .error ⟨blocks, some key, found.1, found.2, false⟩
                | none =>
                    match (inBody.drop inputs.toList).used with
                    | none =>
                        match misuseAmong linear inner results with
                        | some found => .error ⟨blocks, some key, found.1, found.2, false⟩
                        | none =>
                            .ok (((inner.drop results.toList).add
                              (HList.linearUses linear init)).add (Times.linearUses linear times))
                    | some found => .error ⟨blocks, some key, found.1, found.2, true⟩
    | _, _, .block key number body results rest =>
        match Term.linearUses (blocks ++ [(key, number)]) body with
        | .error misuse => .error misuse
        | .ok inBody =>
            match Term.linearUses blocks rest with
            | .error misuse => .error misuse
            | .ok inner =>
                match misuseAmong linear inner results with
                | some found => .error ⟨blocks, some key, found.1, found.2, false⟩
                | none => .ok (inBody.add (inner.drop results.toList))
    | _, _, .attempt key _ _ inputs body results rest =>
        match Term.linearUses blocks body with
        | .error misuse => .error misuse
        | .ok inBody =>
            match Term.linearUses blocks rest with
            | .error misuse => .error misuse
            | .ok inner =>
                match misuseAmong linear inBody inputs with
                | some found => .error ⟨blocks, some key, found.1, found.2, false⟩
                | none =>
                    match misuseAmong linear inner results with
                    | some found => .error ⟨blocks, some key, found.1, found.2, false⟩
                    | none => .ok ((inBody.drop inputs.toList).add (inner.drop results.toList))
  /-- What the arms of the case analysis with the key use of the values around it, each counted
  by name; or the first value of linear type that is not used as it must be, among them the
  payload of an arm that is not used once. -/
  def Arms.linearUses (blocks : List (Key × Nat)) (key : Key) :
      {Γ : Ctx D.Ty} → {mid payloads : List D.Ty} → Arms D Γ mid payloads →
        Except Misuse (List Uses)
    | _, _, _, .nil => .ok []
    | _, _, _, .cons inputs arm rest =>
        match Term.linearUses blocks arm with
        | .error misuse => .error misuse
        | .ok inArm =>
            match Arms.linearUses blocks key rest with
            | .error misuse => .error misuse
            | .ok others =>
                match misuseAmong linear inArm inputs with
                | some found => .error ⟨blocks, some key, found.1, found.2, false⟩
                | none => .ok (inArm.drop inputs.toList :: others)
end

/-- The value of a linear type at which the decision of linear use fails, for a body and the
names of the inputs of its definition (whose context is its inputs, `Ctx.empty.extend inputs`):
the first value of linear type that is not used once, with where; nothing when every one is
used once. The inputs are read as one binding, as the context reads them. -/
def Term.misuse {ins : List D.Ty} (inputs : Names ins) {Γ : Ctx D.Ty} {outs : List D.Ty}
    (t : Term D Γ outs) : Option Misuse :=
  match Term.linearUses linear [] t with
  | .error misuse => some misuse
  | .ok kept =>
      (misuseAmong linear kept inputs).map fun found => ⟨[], none, found.1, found.2, false⟩

/-- Every value of a linear type among the inputs of a body is used once, and so is every one
bound inside it; the regions of a choice and the arms of a case analysis use each value of a
linear type from around them equally often, and a loop body uses none from around it. -/
def Term.UsedOnce {ins : List D.Ty} (inputs : Names ins) {Γ : Ctx D.Ty} {outs : List D.Ty}
    (t : Term D Γ outs) : Prop :=
  t.misuse linear inputs = none

/-- Whether every value of a linear type is used once in a body. -/
instance Term.decideUsedOnce {ins : List D.Ty} (inputs : Names ins) {Γ : Ctx D.Ty}
    {outs : List D.Ty} (t : Term D Γ outs) : Decidable (t.UsedOnce linear inputs) :=
  inferInstanceAs (Decidable (t.misuse linear inputs = none))

end

end Zkc.Core
