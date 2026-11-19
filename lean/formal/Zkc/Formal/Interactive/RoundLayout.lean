module

public import Zkc.Formal.Interactive.ReductionRound
public import Zkc.Core.Evidence.StraightLineReadback
public import Zkc.Core.Facts.Contracts.RoleOperationLaws

@[expose] public section
namespace Zkc.Formal.Interactive.Sumcheck.ReductionRound
open Core
variable {V : Vocabulary}

def singleResult (fns : List (FnHeader V)) (raw : LocalRaw V) (ins : List V.Ty) :
    Option ((t : V.Ty) × LocalOp V fns ins [t]) := do
  let .ok ⟨[t],op⟩ := LocalOp.read fns raw ins | none
  return ⟨t,op⟩

def atType (fns : List (FnHeader V)) (raw : LocalRaw V) (ins : List V.Ty) (t : V.Ty) :
    Option (LocalOp V fns ins [t]) := do
  let ⟨out,op⟩ ← singleResult fns raw ins
  if same : out = t then return same ▸ op else none

structure Operations (V : Vocabulary) where
  message : LocalRaw V
  boundary : LocalRaw V
  bindState : LocalRaw V
  evaluate : LocalRaw V

def Operations.members (raw : Operations V) (hs : Headers V) (state t : V.Ty) :
    Option ((msg : V.Ty) × (residual : V.Ty) × Members hs t msg state residual) := do
  let ⟨msg,sendValue⟩ ← singleResult hs.fns raw.message [state]
  let ⟨residual,bindState⟩ ← singleResult hs.fns raw.bindState [state,t]
  return ⟨msg,residual,sendValue,bindState,← atType hs.fns raw.boundary [msg] t,← atType hs.fns raw.evaluate [msg,t] t⟩

/-- Resolve each operand when its instruction executes, before installing the results. -/
inductive Origin where
  | input (name : Name)
  | result (site : Key) (index : Nat := 0)
deriving DecidableEq

structure RoundOp (V : Vocabulary) where
  key : Key
  code : ProtocolRaw V
  args : List Origin

structure RoundUses (V : Vocabulary) where
  bindings : List (Name × Origin) := []
  ops : List (RoundOp V) := []
  guards : List (Key × Origin) := []

def RoundUses.resolve (uses : RoundUses V) (name : Name) : Origin :=
  (uses.bindings.lookup name).getD (.input name)

def RoundUses.read (steps : List (Instruction (ProtocolRaw V) (List Role))) : Option (RoundUses V) :=
  steps.foldlM (init := {}) fun uses step => do
    match step with
    | .op key results code args =>
      let bindings := results.zipIdx.foldl (init := uses.bindings) fun bs (name, i) =>
        (name, Origin.result key i) :: bs
      return {uses with bindings, ops := ⟨key,code,args.map uses.resolve⟩ :: uses.ops}
    | .guard key [1] name .reject => return {uses with guards := (key,uses.resolve name) :: uses.guards}
    | _ => none

/-- The keys in the order expected by the typed reference body. Each key belongs to the
operation found at its use or effect marker in the actual block. -/
structure RoundLayout (V : Vocabulary) where
  operations : Operations V
  keys : List Key

def RoundLayout.sites (layout : RoundLayout V) (i : Nat) : Key := layout.keys[i]?.getD ⟨i⟩

def RoundUses.producer (uses : RoundUses V) (origin : Origin) : Option (RoundOp V) := do
  let .result key 0 := origin | none
  uses.ops.find? (·.key == key)

/-- Find the narrowed output whose input was computed from these operands. The enclosing
term supplies the actual exits. A steps-only caller can also recover unambiguous members. -/
def RoundUses.updateOutput (uses : RoundUses V) (roles : List Role) (args : List Origin)
    (exit : Option Origin) : Option (Key × LocalRaw V × Key) := do
  let [update] := uses.ops.filterMap (fun narrow => do
    guard (exit.all (· == .result narrow.key))
    let .narrow holders := narrow.code | none
    guard (holders == roles)
    let [value] := narrow.args | none
    let op ← uses.producer value
    let .compute holders raw := op.code | none
    guard (holders == roles && op.args == args)
    return (op.key,raw,narrow.key)) | none
  return update

def RoundLayout.read (steps : List (Instruction (ProtocolRaw V) (List Role)))
    (exit : Option (List Name) := none) : Option (RoundLayout V) := do
  let uses ← RoundUses.read steps
  let keys := uses.ops.map (·.key) ++ uses.guards.map (·.1)
  guard keys.Nodup
  let [sent] := uses.ops.filter (fun op => op.code matches .event (.flow .message 0 [1]) _) | none
  let [value] := sent.args | none
  let message ← uses.producer value
  let .compute [0] messageOp := message.code | none
  let [state] := message.args | none
  let [(guardKey,test)] := uses.guards | none
  let equal ← uses.producer test
  let [_,rhs] := equal.args | none
  let boundary ← uses.producer rhs
  let .compute [1] boundaryOp := boundary.code | none
  guard (boundary.args == [.result sent.key])
  let [draw] := uses.ops.filter (fun op => op.code matches .event (.given (.coin _) 1 [0]) _) | none
  let returns := exit.map (List.map uses.resolve)
  let (st,claim,coin) ← match returns with
    | some [st,claim,coin] => some (some st,some claim,some coin)
    | none => some (none,none,none)
    | _ => none
  let (bindKey,bindOp,stateOut) ← uses.updateOutput [0] [state,.result draw.key] st
  let (evalKey,evalOp,claimOut) ← uses.updateOutput [0,1] [.result sent.key,.result draw.key] claim
  let [coinOut] := uses.ops.filter (fun op => coin.all (· == .result op.key) &&
    op.code == .narrow [0,1] && op.args == [.result draw.key]) | none
  return ⟨⟨messageOp,boundaryOp,bindOp,evalOp⟩, [message.key,sent.key,boundary.key,equal.key,
    guardKey,draw.key,bindKey,evalKey,coinOut.key,stateOut,claimOut]⟩

def Operations.read (steps : List (Instruction (ProtocolRaw V) (List Role))) : Option (Operations V) :=
  (RoundLayout.read steps).map (·.operations)

variable {hs : Headers V} {r : Role}

def IsRoleSem (sem : Semantics (roleDialect V hs r)) : Prop :=
  ∃ (M : Model V) (fns : FnTable M hs.fns) (roles : RTable M hs.protocols), sem = roleSem M r fns roles

abbrev RoleSame {Γ Δ outs} (map : StraightLine.NamesMap) (a : Term (roleDialect V hs r) Γ outs)
    (b : Term (roleDialect V hs r) Δ outs) := StraightLine.SameIn IsRoleSem map a b

/-- A structural certificate is also valid under the role interpretation. -/
instance {Γ Δ outs map} {a : Term (roleDialect V hs r) Γ outs} {b : Term (roleDialect V hs r) Δ outs} :
    Coe (StraightLine.Same map a b) (RoleSame map a b) where
  coe same := fun sem _ => same sem

def skipAbsent (kept : List Key) {Δ mid} (key : Key) (i : Instr (roleDialect V hs r) Δ mid) :
    Option (PLift (StraightLine.ReturnsDirectly IsRoleSem key i)) :=
  match i with
  | .op (.absent _ out) _ => if key ∈ kept then none else
      some ⟨by rintro _ ⟨M,fns,roles,rfl⟩ path env; exact ⟨nothings M out,rfl⟩⟩
  | _ => none

abbrev emptyPoint (t : V.Ty) : V.Ty := .seq t (some 0)

/-- A round can start in an arbitrary outer SSA context. The verifier observes the
running claim supplied by that context. The other inputs to the reference round are unused. -/
structure Located {Γ : Ctx (LTy V)} {mid : List (LTy V)} (state : V.Ty) {t : V.Ty} (events : Events t)
    (running : Var Γ ⟨t,[0,1]⟩) (actual : Term (protocolDialect V hs) Γ mid)
    (point : V.Ty := emptyPoint t) where
  msg : V.Ty
  residual : V.Ty
  members : Members hs t msg state residual
  sites : Nat → Key
  types : mid = outputs residual t
  same : RoleSame [(2,running.name)] (project 1 (body members events point sites)) (project 1 (types ▸ actual))

def readCompared (distinct : (hs.fns.map (·.key)).Nodup) {Γ : Ctx (LTy V)} {mid : List (LTy V)}
    (state point : V.Ty) {t : V.Ty} (events : Events t) (running : Var Γ ⟨t,[0,1]⟩)
    (actual : Term (protocolDialect V hs) Γ mid) : Option (Located state events running actual point) := do
  let rules := protocolRules hs
  let (steps,exit) := eraseBody rules.printOp rules.printWho actual
  let layout ← RoundLayout.read steps (some exit)
  let ⟨msg,residual,members⟩ ← layout.operations.members hs state t
  if types : mid = outputs residual t then
    let ⟨same⟩ ← StraightLine.compareIn (BodyAnalysis.roleChecks 1) (BodyAnalysis.roleChecks_lawful distinct)
      IsRoleSem (skipAbsent layout.keys) [(2,running.name)] (project 1 (body members events point layout.sites))
      (project 1 (types ▸ actual))
    return ⟨msg,residual,members,layout.sites,types,same⟩
  else none

end Zkc.Formal.Interactive.Sumcheck.ReductionRound
