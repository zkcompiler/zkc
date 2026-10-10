import Examples.TablePhysical.Storage
import Zkc.Realization.RegionSimulation

/-! A physical interpretation of the finite table client. Explicit preparation
choices change scalar values to store-relative references. The same compact
region grammar retains control and captures; invocation uses the selected
logical operation contract after reading its actual physical operands.
-/

set_option autoImplicit false
namespace TablePhysical
open TableProtocol Zkc.Source Zkc.Realization

inductive Operation where
  | invoke (operation : Protocol.Operation)
  | prepare (mode : Mode) (domain : Domain) (rank : Nat)
  deriving DecidableEq, Repr

def Operation.logical : Operation → Protocol.Operation
  | .invoke op => op
  | .prepare _ d n => .base (.evaluate d n)

abbrev language : Language where
  Ty := Ty
  Op := Operation
  arguments op := Protocol.arguments op.logical
  result op := Protocol.result op.logical
  condition := .boolean

abbrev logicalMeaning : Interpretation language Protocol.protocolInterface where
  Value := TableProtocol.Value
  condition := id
  operation op args := Protocol.meaning.operation op.logical args

/-- Erase only physical operation choices; retain every operand and control node. -/
def erase {Γ : List Ty} {ty : Ty} : Region language Γ ty → Region Protocol.language Γ ty
  | .ret v => .ret v
  | .stop why => .stop why
  | .letOp op args next => .letOp op.logical args (erase next)
  | .branch condition yes no => .branch condition (erase yes) (erase no)
  | .iterate count initial body next => .iterate count initial (erase body) (erase next)
  | .bind body next => .bind (erase body) (erase next)

theorem denote_erase {Γ : List language.Ty} {ty : language.Ty} (program : Region language Γ ty)
    (env : Environment TableProtocol.Value Γ) :
    (erase program).denote Protocol.meaning env = program.denote logicalMeaning env := by
  induction program with
  | ret _ => rfl
  | stop _ => rfl
  | letOp op args next ih => simp only [erase, Region.denote, ih]
  | branch condition yes no yesIH noIH => simp only [erase, Region.denote, yesIH, noIH]
  | iterate count initial body next bodyIH nextIH =>
    simp only [erase, Region.denote, bodyIH, nextIH]
  | bind body next bodyIH nextIH => simp only [erase, Region.denote, bodyIH, nextIH]

structure State (S : Type := Protocol.State) where
  logical : S
  store : Store := empty
  evaluations : Nat := 0

def decodeValues (store : Store) {Γ : List Ty} : Values Value Γ → Option (Values TableProtocol.Value Γ)
  | .nil => some .nil
  | .cons (ty := ty) x rest => do
    let value ← decode store ty x
    let tail ← decodeValues store rest
    return .cons value tail

def readCosts (store : Store) {Γ : List Ty} : Values Value Γ → Nat
  | .nil => 0
  | .cons (ty := ty) x rest => readCost store ty x + readCosts store rest

def embedOutcome (ty : Ty) : PIR.Outcome (TableProtocol.Value ty) → PIR.Outcome (Value ty)
  | .returned x => .returned (embed ty x)
  | .stopped why => .stopped why

def evaluationCost (op : Protocol.Operation) (outcome : PIR.Outcome (TableProtocol.Value (Protocol.result op))) : Nat :=
  match op, outcome with
  | .base (.evaluate _ _), .returned _ => 1
  | _, _ => 0

def invoke {S E : Type} (logicalHandler : PIR.Handler Protocol.protocolInterface S E)
    (op : Protocol.Operation) (args : Values Value (Protocol.arguments op))
    (state : State S) : PIR.Execution (State S) E (Value (Protocol.result op)) :=
  match decodeValues state.store args with
  | none => ⟨.stopped .refused, state, []⟩
  | some logicalArgs =>
    let out := (Protocol.meaning.operation op logicalArgs).run logicalHandler state.logical
    ⟨embedOutcome _ out.outcome,
      { state with
        logical := out.state
        evaluations := state.evaluations + readCosts state.store args + evaluationCost op out.outcome }, out.events⟩

def prepare {S E : Type} (mode : Mode) (d : Domain) (n : Nat)
    (view : Zkc.Polynomial.Table.Residual (Field d) n) (tail : List (Field d))
    (state : State S) : PIR.Execution (State S) E (Scalar d) :=
  if shape : (view.coordinates ++ tail).length = n then
    ⟨.returned (.reference (state.store d).length),
      { state with
        store := publish state.store d (cell mode view tail shape)
        evaluations := state.evaluations + preparationCost mode }, []⟩
  else ⟨.stopped .refused, state, []⟩

structure Request where
  operation : Operation
  arguments : Values Value (language.arguments operation)

abbrev interface : PIR.Signature := ⟨Request, fun request => Value (language.result request.operation)⟩

def handler {S E : Type} (logicalHandler : PIR.Handler Protocol.protocolInterface S E) :
    PIR.Handler interface (State S) E
  | ⟨.invoke op, args⟩, state => invoke logicalHandler op args state
  | ⟨.prepare mode d n, .cons view (.cons tail .nil)⟩, state => prepare mode d n view tail state

abbrev meaning : Interpretation language interface where
  Value := Value
  condition := id
  operation op args := .call ⟨op, args⟩ .done

def representation {S : Type} : Representation TableProtocol.Value Value S (State S) where
  states source target := source = target.logical
  value ty a _ b state := decode state.store ty b = some a

end TablePhysical
