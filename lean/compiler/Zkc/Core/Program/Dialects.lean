module

public import Zkc.Core.Program.Term
public import Zkc.Core.Program.Located
public import Zkc.Core.Program.Shape

@[expose] public section

/-!
The three dialects: the local one (a function), the protocol one (all roles; located
types) and the role one (one role; the same located types, read as what the role holds). A
context of a protocol and of a role program has the same names at the same located types
(`Ctx (LTy V)`). A term carries the proof of each "held by at least", so projection is total.
A callee is named by its place among the headers (`Member`), and a component, a field or an
alternative by its place among the types.
-/

namespace Zkc.Core

/-! ## Headers -/

/-- What an application needs of a function. -/
structure FnHeader (V : Vocabulary) where
  key : Key
  ins : List V.Ty
  outs : List V.Ty
  /-- Whether the function can stop with a reason. -/
  canStop : Bool
  /-- The native kernel that may stand for the body, under the assumption that it computes
  the body. The function always has its body. -/
  kernel : Option Key

/-- What an application needs of a protocol: its ports and results, located in its own
roles, and its shape. -/
structure ProtocolHeader (V : Vocabulary) where
  key : Key
  roles : Nat
  ins : List (LTy V)
  outs : List (LTy V)
  shape : Shape V

/-- The record of a run of the protocol. -/
abbrev ProtocolHeader.record {V : Vocabulary} (hdr : ProtocolHeader V) : Fields V :=
  hdr.shape.fields

structure Headers (V : Vocabulary) where
  fns : List (FnHeader V)
  protocols : List (ProtocolHeader V)

/-! ## The local dialect -/

def Tys.toList {K : Type} : Tys K → List (Ty K)
  | .nil => []
  | .cons head rest => head :: rest.toList

/-- The size of a concatenation: the sum of the sizes when both sequences have one. -/
def concatSize : Option Nat → Option Nat → Option Nat
  | some first, some second => some (first + second)
  | _, _ => none

/-- The operations that the core owns: a closed list. Their meaning is the core's, and no model
chooses it. Seven have a domain and stop `undefined` outside it. An operation that would copy
a value or drop a part of one (a reading, a length, a slice, a filling) is not typed at a
linear type, nor is giving a sequence a size, whose domain is its length. -/
inductive OwnedOp (V : Vocabulary) : List V.Ty → List V.Ty → Type where
  -- Naturals
  | natAdd : OwnedOp V [.nat, .nat] [.nat]
  /-- Its domain: the second is at most the first. -/
  | natSub : OwnedOp V [.nat, .nat] [.nat]
  | natMul : OwnedOp V [.nat, .nat] [.nat]
  /-- The quotient, rounded down. Its domain: the second is at least one. -/
  | natDiv : OwnedOp V [.nat, .nat] [.nat]
  /-- The remainder. Its domain: the second is at least one. -/
  | natRem : OwnedOp V [.nat, .nat] [.nat]
  /-- The power; a number to the power zero is one. -/
  | natPow : OwnedOp V [.nat, .nat] [.nat]
  | natEqual : OwnedOp V [.nat, .nat] [.bool]
  /-- The first is less than the second. -/
  | natLess : OwnedOp V [.nat, .nat] [.bool]
  -- Truth values
  /-- The conjunction; both operands are evaluated. -/
  | boolAnd : OwnedOp V [.bool, .bool] [.bool]
  /-- The disjunction; both operands are evaluated. -/
  | boolOr : OwnedOp V [.bool, .bool] [.bool]
  | boolNot : OwnedOp V [.bool] [.bool]
  | boolEqual : OwnedOp V [.bool, .bool] [.bool]
  -- Sequences
  | seqLength (item : V.Ty) (size : Option Nat) (free : Ty.isLinear V item = false) :
      OwnedOp V [.seq item size] [.nat]
  /-- The item at a position, counted from zero. Its domain: the position is below the
  length. -/
  | seqAt (item : V.Ty) (size : Option Nat) (free : Ty.isLinear V item = false) :
      OwnedOp V [.seq item size, .nat] [item]
  /-- The items from a position up to another, the second excluded. Its domain: the first is
  at most the second, the second at most the length, and their difference is the size of the
  result when it has one. -/
  | seqSlice (item : V.Ty) (size result : Option Nat) (free : Ty.isLinear V item = false) :
      OwnedOp V [.seq item size, .nat, .nat] [.seq item result]
  /-- The items of the first, then those of the second. -/
  | seqConcat (item : V.Ty) (first second : Option Nat) :
      OwnedOp V [.seq item first, .seq item second] [.seq item (concatSize first second)]
  /-- A written number of copies of a value. -/
  | seqFill (item : V.Ty) (count : Nat) (free : Ty.isLinear V item = false) :
      OwnedOp V [item] [.seq item (some count)]
  -- Refining: the value is the operand's, and its type says more
  /-- Its domain: the length is the size. -/
  | seqSized (item : V.Ty) (size : Nat) (free : Ty.isLinear V item = false) :
      OwnedOp V [.seq item none] [.seq item (some size)]
  /-- Its domain: the number is below the bound. -/
  | natBelow (bound : Nat) : OwnedOp V [.nat] [.fin bound]
  -- Widening: the value is the operand's, and its type says less
  | seqUnsized (item : V.Ty) (size : Nat) : OwnedOp V [.seq item (some size)] [.seq item none]
  | finToNat (bound : Nat) : OwnedOp V [.fin bound] [.nat]
  | finWiden (bound wider : Nat) (le : bound ≤ wider) : OwnedOp V [.fin bound] [.fin wider]
  -- Data
  /-- A sequence of a written number of items. -/
  | makeSeq (item : V.Ty) (count : Nat) :
      OwnedOp V (List.replicate count item) [.seq item (some count)]
  | makeTuple (items : Tys V.TypeKey) : OwnedOp V items.toList [.tuple items]
  | makeRecord (key : Key) (linear : Bool) (fields : Tys V.TypeKey) :
      OwnedOp V fields.toList [.record key linear fields]
  /-- One component of a tuple that has no linear component. -/
  | getTuple (items : Tys V.TypeKey) {τ : V.Ty} (position : Member items.toList τ)
      (free : Tys.anyLinear V items = false) : OwnedOp V [.tuple items] [τ]
  /-- One field of a record that is not linear and has no linear field. -/
  | getRecord (key : Key) (fields : Tys V.TypeKey) {τ : V.Ty}
      (position : Member fields.toList τ) (free : Tys.anyLinear V fields = false) :
      OwnedOp V [.record key false fields] [τ]
  /-- Every component of a tuple: how a tuple with a linear component is used. -/
  | takeTuple (items : Tys V.TypeKey) : OwnedOp V [.tuple items] items.toList
  /-- Every field of a record: how a linear record is used. -/
  | takeRecord (key : Key) (linear : Bool) (fields : Tys V.TypeKey) :
      OwnedOp V [.record key linear fields] fields.toList
  /-- A value as the alternative at a position of a variant: the position is that of an
  alternative of the value's type. -/
  | variant (key : Key) (alternatives : Tys V.TypeKey) {τ : V.Ty}
      (position : Member alternatives.toList τ) : OwnedOp V [τ] [.variant key alternatives]

inductive LocalOp (V : Vocabulary) (fns : List (FnHeader V)) : List V.Ty → List V.Ty → Type where
  /-- A row of the vocabulary. -/
  | row (key : V.RowKey) (signature : RowSignature V.TypeKey V.RowKey)
      (known : V.row key = some signature) : LocalOp V fns signature.ins signature.outs
  | owned {ins outs} (o : OwnedOp V ins outs) : LocalOp V fns ins outs
  /-- A literal: data that reads as a value of the type. -/
  | literal (τ : V.Ty) (data : List Nat) (reads : V.Reads τ data) : LocalOp V fns [] [τ]
  | call {hdr} (callee : Member fns hdr) : LocalOp V fns hdr.ins hdr.outs

@[reducible] def localDialect (V : Vocabulary) (fns : List (FnHeader V)) : Dialect where
  Ty := V.Ty
  Op := LocalOp V fns
  Who := Unit
  Condition _ t := t = .bool
  Alternatives _ t payloads := ∃ key alternatives, t = .variant key alternatives ∧
    payloads = alternatives.toList
  Count _ t := t = .nat
  index _ := .nat
  Attempt _ := False
  Gives _ _ := True
  collected size t := .seq t size

/-! ## The protocol dialect -/

/-- The inputs and the result of what the world gives are those of its kind. -/
def GivenKind.Typed {V : Vocabulary} : GivenKind V → List V.Ty → V.Ty → Prop
  | .coin law, ins, τ => ∃ s, V.law law = some s ∧ s.ins = ins ∧ s.out = τ
  | .request _, ins, _ => ins.length = 1

/-- Each operand may be used at its port. -/
def Fits {V : Vocabulary} : List (LTy V) → List (LTy V) → Prop
  | [], [] => True
  | a :: as, b :: bs => a.Covers b ∧ Fits as bs
  | _, _ => False

inductive ProtocolOp (V : Vocabulary) (hs : Headers V) : List (LTy V) → List (LTy V) → Type where
  /-- The roles `R` compute a local operation on values that each of them holds. -/
  | compute {ins outs} (R : Holders) (o : LocalOp V hs.fns ins outs) (operands : List (LTy V))
      (types : operands.map (·.ty) = ins)
      (held : ∀ a, a ∈ operands → ∀ r, r ∈ R → r ∈ a.holders) :
      ProtocolOp V hs operands (outs.map fun τ => ⟨τ, R⟩)
  /-- A holder gives the value: the result is the value, held by the getters as well. -/
  | flow {τ H} (kind : FlowKind) (giver : Role) (getters : List Role)
      (holds : giver ∈ H) (apart : giver ∉ getters) :
      ProtocolOp V hs [⟨τ, H⟩] [⟨τ, Holders.ofList (getters ++ H)⟩]
  /-- The world gives a value to the owner and to those that hear it. -/
  | given (kind : GivenKind V) (owner : Role) (hearers : List Role)
      (operands : List (LTy V)) (τ : V.Ty) (typed : kind.Typed (operands.map (·.ty)) τ)
      (held : ∀ a, a ∈ operands → owner ∈ a.holders) (apart : owner ∉ hearers) :
      ProtocolOp V hs operands [⟨τ, Holders.ofList (owner :: hearers)⟩]
  /-- The roles `R` among the holders keep the value; nobody acts. -/
  | narrow {τ H} (R : Holders) (among : ∀ r, r ∈ R → r ∈ H) :
      ProtocolOp V hs [⟨τ, H⟩] [⟨τ, R⟩]
  /-- The caller's roles run an earlier definition: the callee's role `j` is played by the
  caller's role `roles[j]`. -/
  | apply {hdr} (callee : Member hs.protocols hdr) (roles : List Role) (distinct : roles.Nodup)
      (covers : roles.length = hdr.roles) (operands : List (LTy V))
      (fits : Fits operands (hdr.ins.map (LTy.map (RoleMap.ofList roles distinct).to))) :
      ProtocolOp V hs operands (hdr.outs.map (LTy.map (RoleMap.ofList roles distinct).to))

@[reducible] def protocolDialect (V : Vocabulary) (hs : Headers V) : Dialect where
  Ty := LTy V
  Op := ProtocolOp V hs
  Who := Holders
  Condition ps t := t.ty = .bool ∧ (∀ r, r ∈ ps → r ∈ t.holders) ∧ ps ≠ []
  Alternatives ps t payloads := ∃ key alternatives, t.ty = .variant key alternatives ∧
    payloads = alternatives.toList.map (fun τ => ⟨τ, ps⟩) ∧ (∀ r, r ∈ ps → r ∈ t.holders) ∧
    ps ≠ []
  Count ps t := t.ty = .nat ∧ (∀ r, r ∈ ps → r ∈ t.holders) ∧ ps ≠ []
  index ps := LTy.index ps
  Attempt ps := ∃ owner, ps = [owner]
  Gives ps a := ∀ r, r ∈ a.holders → r ∈ ps
  collected := LTy.collected

/-! ## Who acts in a region, and the shape of a term -/

/-- Every role that acts in the operation is one of `parts`. A computation counts: it can
stop, and a role that stops must be there to stop. -/
def ProtocolOp.Within {V : Vocabulary} {hs : Headers V} {ins outs : List (LTy V)}
    (parts : List Role) : ProtocolOp V hs ins outs → Prop
  | .compute R _ _ _ _ => ∀ r, r ∈ R → r ∈ parts
  | .flow _ giver getters _ _ => giver ∈ parts ∧ ∀ r, r ∈ getters → r ∈ parts
  | .given _ owner hearers _ _ _ _ _ => owner ∈ parts ∧ ∀ r, r ∈ hearers → r ∈ parts
  | .narrow _ _ => True
  | .apply _ roles _ _ _ _ => ∀ r, r ∈ roles → r ∈ parts

mutual
  /-- Every role that acts in the region is one of `parts`. -/
  def Within {V : Vocabulary} {hs : Headers V} (parts : List Role) :
      {Γ : Ctx (LTy V)} → {outs : List (LTy V)} → Term (protocolDialect V hs) Γ outs → Prop
    | _, _, .ret _ => True
    | _, _, .op _ o _ _ rest => ProtocolOp.Within parts o ∧ Within parts rest
    | _, _, .guard _ ps _ _ _ rest => (∀ r, r ∈ ps → r ∈ parts) ∧ Within parts rest
    | _, _, .choose _ ps _ _ _ onTrue onFalse _ rest =>
        (∀ r, r ∈ ps → r ∈ parts) ∧ Within parts onTrue ∧ Within parts onFalse ∧
          Within parts rest
    | _, _, .cases _ ps _ _ _ arms _ rest =>
        (∀ r, r ∈ ps → r ∈ parts) ∧ WithinArms parts arms ∧ Within parts rest
    | _, _, .loop _ ps _ _ _ _ body _ rest =>
        (∀ r, r ∈ ps → r ∈ parts) ∧ Within parts body ∧ Within parts rest
    | _, _, .block _ _ body _ rest => Within parts body ∧ Within parts rest
    | _, _, .attempt _ w _ _ body _ rest =>
        (∀ r, r ∈ w → r ∈ parts) ∧ Within parts body ∧ Within parts rest
  def WithinArms {V : Vocabulary} {hs : Headers V} (parts : List Role) :
      {Γ : Ctx (LTy V)} → {mid payloads : List (LTy V)} →
        Arms (protocolDialect V hs) Γ mid payloads → Prop
    | _, _, _, .nil => True
    | _, _, _, .cons _ arm rest => Within parts arm ∧ WithinArms parts rest
end

mutual
  /-- Nobody but those who perform a choice or a loop acts in its regions. A role outside
  them has no part in the regions, so its program passes over them. Every role may act in the
  body of an attempt, and runs it. -/
  def Enclosed {V : Vocabulary} {hs : Headers V} :
      {Γ : Ctx (LTy V)} → {outs : List (LTy V)} → Term (protocolDialect V hs) Γ outs → Prop
    | _, _, .ret _ => True
    | _, _, .op _ _ _ _ rest => Enclosed rest
    | _, _, .guard _ _ _ _ _ rest => Enclosed rest
    | _, _, .choose _ ps _ _ _ onTrue onFalse _ rest =>
        Within ps onTrue ∧ Within ps onFalse ∧ Enclosed onTrue ∧ Enclosed onFalse ∧
          Enclosed rest
    | _, _, .cases _ ps _ _ _ arms _ rest =>
        WithinArms ps arms ∧ EnclosedArms arms ∧ Enclosed rest
    | _, _, .loop _ ps _ _ _ _ body _ rest => Within ps body ∧ Enclosed body ∧ Enclosed rest
    | _, _, .block _ _ body _ rest => Enclosed body ∧ Enclosed rest
    | _, _, .attempt _ _ _ _ body _ rest => Enclosed body ∧ Enclosed rest
  def EnclosedArms {V : Vocabulary} {hs : Headers V} :
      {Γ : Ctx (LTy V)} → {mid payloads : List (LTy V)} →
        Arms (protocolDialect V hs) Γ mid payloads → Prop
    | _, _, _, .nil => True
    | _, _, _, .cons _ arm rest => Enclosed arm ∧ EnclosedArms rest
end

/-- The part of the shape that one operation is. -/
def ProtocolOp.shape {V : Vocabulary} {hs : Headers V} {ins outs : List (LTy V)} (key : Key) :
    ProtocolOp V hs ins outs → Shape V → Shape V
  | .compute _ _ _ _ _, rest => rest
  | .flow (τ := τ) kind giver getters _ _, rest => .event key (.flow kind giver getters) τ rest
  | .given kind owner hearers _ τ _ _ _, rest => .event key (.given kind owner hearers) τ rest
  | .narrow _ _, rest => rest
  | .apply (hdr := hdr) _ roles _ _ _ _, rest => .apply key hdr.key roles hdr.shape rest

mutual
  /-- The shape of a term: its events by key, with loops, choices, applications and blocks
  kept. -/
  def shapeOf {V : Vocabulary} {hs : Headers V} :
      {Γ : Ctx (LTy V)} → {outs : List (LTy V)} → Term (protocolDialect V hs) Γ outs → Shape V
    | _, _, .ret _ => .nil
    | _, _, .op key o _ _ rest => ProtocolOp.shape key o (shapeOf rest)
    | _, _, .guard key ps _ _ why rest => .guard key ps why (shapeOf rest)
    | _, _, .choose key ps _ _ _ onTrue onFalse _ rest =>
        .choice key ps (.cons (shapeOf onTrue) (.cons (shapeOf onFalse) .nil)) (shapeOf rest)
    | _, _, .cases key ps _ _ _ arms _ rest => .choice key ps (shapesOf arms) (shapeOf rest)
    | _, _, .loop key ps _ _ _ _ body _ rest => .loop key ps (shapeOf body) (shapeOf rest)
    | _, _, .block key number body _ rest => .block key number (shapeOf body) (shapeOf rest)
    | _, _, .attempt key w _ _ body _ rest => .attempt key w (shapeOf body) (shapeOf rest)
  def shapesOf {V : Vocabulary} {hs : Headers V} :
      {Γ : Ctx (LTy V)} → {mid payloads : List (LTy V)} →
        Arms (protocolDialect V hs) Γ mid payloads → Shapes V
    | _, _, _, .nil => .nil
    | _, _, _, .cons _ arm rest => .cons (shapeOf arm) (shapesOf rest)
end

/-! ## The role dialect -/

inductive RoleOp (V : Vocabulary) (hs : Headers V) (r : Role) :
    List (LTy V) → List (LTy V) → Type where
  | compute {ins outs} (R : Holders) (o : LocalOp V hs.fns ins outs) (operands : List (LTy V))
      (types : operands.map (·.ty) = ins) (mine : r ∈ R)
      (here : ∀ a, a ∈ operands → r ∈ a.holders) :
      RoleOp V hs r operands (outs.map fun τ => ⟨τ, R⟩)
  /-- Values that the role does not hold. -/
  | absent (items : List (LTy V)) (out : ∀ a, a ∈ items → r ∉ a.holders) :
      RoleOp V hs r [] items
  | give {τ H} (kind : FlowKind) (getters : List Role) (here : r ∈ H) :
      RoleOp V hs r [⟨τ, H⟩] [⟨τ, Holders.ofList (getters ++ H)⟩]
  | get (τ : V.Ty) (H : Holders) (kind : FlowKind) (giver : Role)
      (getters : List Role) (mine : r ∈ getters) :
      RoleOp V hs r [] [⟨τ, Holders.ofList (getters ++ H)⟩]
  /-- A value whose holders change without the role: the role has it afterwards as it had
  it before. -/
  | keep {τ H} (H' : Holders) (same : r ∈ H ↔ r ∈ H') :
      RoleOp V hs r [⟨τ, H⟩] [⟨τ, H'⟩]
  | own (kind : GivenKind V) (hearers : List Role) (operands : List (LTy V))
      (τ : V.Ty) (typed : kind.Typed (operands.map (·.ty)) τ)
      (here : ∀ a, a ∈ operands → r ∈ a.holders) :
      RoleOp V hs r operands [⟨τ, Holders.ofList (r :: hearers)⟩]
  | hear (kind : GivenKind V) (owner : Role) (hearers : List Role) (τ : V.Ty)
      (mine : r ∈ hearers) : RoleOp V hs r [] [⟨τ, Holders.ofList (owner :: hearers)⟩]
  /-- The role's part of an application: the program of the role that it plays in the
  callee, which does nothing when it plays none of the callee's roles. -/
  | apply {hdr} (callee : Member hs.protocols hdr) (roles : List Role) (distinct : roles.Nodup)
      (covers : roles.length = hdr.roles) (operands : List (LTy V))
      (fits : Fits operands (hdr.ins.map (LTy.map (RoleMap.ofList roles distinct).to))) :
      RoleOp V hs r operands (hdr.outs.map (LTy.map (RoleMap.ofList roles distinct).to))

@[reducible] def roleDialect (V : Vocabulary) (hs : Headers V) (r : Role) : Dialect where
  Ty := LTy V
  Op := RoleOp V hs r
  Who := Holders
  Condition w t := t.ty = .bool ∧ r ∈ t.holders ∧ r ∈ w
  Alternatives ps t payloads := ∃ key alternatives, t.ty = .variant key alternatives ∧
    payloads = alternatives.toList.map (fun τ => ⟨τ, ps⟩) ∧ r ∈ t.holders ∧ r ∈ ps
  Count w t := t.ty = .nat ∧ r ∈ t.holders ∧ r ∈ w
  index ps := LTy.index ps
  Attempt _ := True
  Gives _ _ := True
  collected := LTy.collected


/-- The function that a local operation calls. -/
def LocalOp.calls {V : Vocabulary} {fns : List (FnHeader V)} {ins res : List V.Ty} :
    LocalOp V fns ins res → List Key
  | .call (hdr := hdr) _ => [hdr.key]
  | _ => []

/-- The definitions that an operation of a protocol calls or applies. -/
def ProtocolOp.calls {V : Vocabulary} {hs : Headers V} {ins res : List (LTy V)} :
    ProtocolOp V hs ins res → List Key
  | .compute _ o _ _ _ => o.calls
  | .apply (hdr := hdr) _ _ _ _ _ _ => [hdr.key]
  | _ => []

end Zkc.Core
