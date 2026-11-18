module

public import Zkc.Core.Program.Erase
public import Zkc.Core.Meaning.Role
public import Zkc.Core.Facts.Contracts.LocalOperations

@[expose] public section


namespace Zkc.Core.BodyAnalysis
variable {V : Vocabulary}

/-- Every argument of an operation of a role that is data. -/
inductive RoleCode (V : Vocabulary) where
  | compute (R : Holders) (o : LocalRaw V)
  | absent (items : List (LTy V))
  | give (kind : FlowKind) (getters : List Role)
  | get (τ : V.Ty) (H : Holders) (kind : FlowKind) (giver : Role) (getters : List Role)
  | keep (H' : Holders)
  | own (kind : GivenKind V) (hearers : List Role) (τ : V.Ty)
  | hear (kind : GivenKind V) (owner : Role) (hearers : List Role) (τ : V.Ty)
  | apply (callee : Nat) (roles : List Role)
deriving DecidableEq

variable {hs : Headers V} {r : Role}

/-- The code of an operation of a role: every argument that is data. -/
def roleCode {ins res : List (LTy V)} : RoleOp V hs r ins res → RoleCode V
  | .compute R o _ _ _ _ => .compute R o.print
  | .absent items _ => .absent items
  | .give kind getters _ => .give kind getters
  | .get τ H kind giver getters _ => .get τ H kind giver getters
  | .keep H' _ => .keep H'
  | .own kind hearers _ τ _ _ => .own kind hearers τ
  | .hear kind owner hearers τ _ => .hear kind owner hearers τ
  | .apply callee roles _ _ _ _ => .apply callee.index roles

variable (r) in
/-- Following for the role dialect: types and performers by equality, operations by their codes. -/
def roleChecks : SkelRules (roleDialect V hs r) where
  sameTy := inferInstance
  sameWho := inferInstance
  sameOp := fun o o' => decide (roleCode o = roleCode o')

/-- The written form of a role's operation: the event part and its resulting located type (`RoleRaw`). -/
def roleWritten {ins res : List (LTy V)} : RoleOp V hs r ins res → RoleRaw V
  | .compute R o _ _ _ _ => .compute R o.print
  | .absent items _ => .absent items
  | .give (τ := τ) (H := H) kind getters _ =>
      .effect (.give kind getters) ⟨τ, Holders.ofList (getters ++ H)⟩
  | .get τ H kind giver getters _ => .effect (.get kind giver) ⟨τ, Holders.ofList (getters ++ H)⟩
  | .keep H' _ => .keep H'
  | .own kind hearers _ τ _ _ => .effect (.own kind hearers) ⟨τ, Holders.ofList (r :: hearers)⟩
  | .hear kind owner hearers τ _ => .effect (.hear kind owner) ⟨τ, Holders.ofList (owner :: hearers)⟩
  | .apply (hdr := hdr) _ roles _ _ _ _ => .apply hdr.key roles

/-- Whether a role's operation is shared: a computation that cannot stop with a reason, what a
role has of values that it does not hold, and a change of holders. -/
def roleShared {ins res : List (LTy V)} : RoleOp V hs r ins res → Bool
  | .compute _ o _ _ _ _ => !o.canStop
  | .absent .. => true
  | .keep .. => true
  | _ => false

/-- The output arity of a role instruction in its header context. An application uses
the signature of the uniquely named protocol even when it is kept as an ordered effect. -/
def roleResultCount (hs : Headers V) : RoleRaw V → Nat
  | .compute _ op => localResultCount hs.fns op
  | .absent types => types.length
  | .keep _ | .effect .. => 1
  | .apply key _ =>
    match Member.withKey (·.key) key hs.protocols with
    | [⟨hdr,_⟩] => hdr.outs.length
    | _ => 0

/-- The written forms with a local, event-free operational interpretation at a role. -/
def roleValueForm {ins outs : List (LTy V)} : RoleOp V hs r ins outs → Option (RoleRaw V)
  | .compute holders op .. => some (.compute holders op.print)
  | .absent types _ => some (.absent types)
  | .keep holders _ => some (.keep holders)
  | _ => none

/-- Pure role computations use the result of the actual typed operation at every occurrence. -/
def RoleReturns (M : Model V) (r : Role) (fns : FnTable M hs.fns) (roles : RTable M hs.protocols)
    (raw : RoleRaw V) (inputs outputs : List (roleSem M r fns roles).Dyn) : Prop :=
  let sem := roleSem M r fns roles
  ∃ (ins outs : List (LTy V)) (op : RoleOp V hs r ins outs) (args : HList sem.Val ins) (result : HList sem.Val outs),
    roleValueForm op = some raw ∧ sem.dyns args = inputs ∧ sem.dyns result = outputs ∧
    ∀ key path, sem.op key op path args = .done result

end Zkc.Core.BodyAnalysis
