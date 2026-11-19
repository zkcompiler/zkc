module

public import Zkc.Formal.Interactive.GateSequence
public import Zkc.Formal.Interactive.HonestReduction
public import Zkc.Frontend.Emit.Bindings

@[expose] public section
namespace Zkc.Formal.Written.SumcheckRows
open Core Frontend.Emit Interactive.Sumcheck

/-- Scalar operations, the challenge law and sized table rows at the exact keys selected
by the source Sumcheck compiler. These keys are shared by recognition and model proofs. -/
def sourceRows (b : Bindings) : ScalarRows b.vocabulary where
  scalar := .inl (.field .bls12381Fr)
  free := rfl
  one := rfl
  add := .inl (.field .add .bls12381Fr .all)
  sub := .inl (.field .sub .bls12381Fr .all)
  mul := .inl (.field .mul .bls12381Fr .all)
  addType := rfl
  subType := rfl
  mulType := rfl

def sourceEvents (b : Bindings) : ReductionRound.Events (sourceRows b).scalarTy :=
  ⟨.inl (.field .equal .bls12381Fr .all),rfl,.uniform (.nominal (.field .bls12381Fr)),⟨_,rfl,rfl,rfl⟩⟩

def vectorRows (b : Bindings) (n : Nat) : TableRestriction.Rows (sourceRows b).scalarTy n where
  add := .inl (.seq .add (.atom (.field .bls12381Fr)) (some (2^n)))
  sub := .inl (.seq .sub (.atom (.field .bls12381Fr)) (some (2^n)))
  scale := .inl (.seq .scale (.atom (.field .bls12381Fr)) (some (2^n)))
  addType := rfl
  subType := rfl
  scaleType := rfl

def sumRow (b : Bindings) (n : Nat) : HonestPairs.SumRow (sourceRows b) n :=
  ⟨.inl (.seq .sum (.atom (.field .bls12381Fr)) (some (2^n))),rfl⟩

open Frontend ReductionRound

section
variable {b : Bindings} {hs : Headers b.vocabulary} {Γ : Ctx (LTy b.vocabulary)}
    {outs : List (LTy b.vocabulary)} {st : b.vocabulary.Ty} {running : Var Γ (shared (sourceRows b).scalarTy)}
    {term : Term (protocolDialect b.vocabulary hs) Γ outs} {n : Nat}

/-- An executable gate primitive and the verified member implementations that use it. -/
structure GateMembers (name : PrimitiveName) (defs : Defs b.vocabulary hs)
    (rounds : Sequence hs (sourceEvents b) st running term n) : Type where
  bound : b.vocabulary.row (.inr name) = some (Gate.signature (sourceRows b))
  members : rounds.AllMembers (fun ops => Gate.Laws (sourceRows b) (.inr name) bound defs ops)

def gateSignature (b : Bindings) (name : PrimitiveName) :
    Option (PLift (b.vocabulary.row (.inr name) = some (Gate.signature (sourceRows b)))) := do
  if sig : b.signature name = some ⟨[Gate.message (sourceRows b),(sourceRows b).scalarTy],[(sourceRows b).scalarTy]⟩ then
    return ⟨by change ((b.signature name).map _).map _ = _; rw [sig]; rfl⟩
  else none

structure GateMember (name : PrimitiveName) (defs : Defs b.vocabulary hs) {msg st out}
    (ops : Members hs (sourceRows b).scalarTy msg st out) : Prop where
  bound : b.vocabulary.row (.inr name) = some (Gate.signature (sourceRows b))
  law : Gate.Laws (sourceRows b) (.inr name) bound defs ops

def checkGateFamily (name : Nat → PrimitiveName) (defs : Defs b.vocabulary hs) (unique : (hs.fns.map (·.key)).Nodup)
    (rounds : Sequence hs (sourceEvents b) st running term n) :=
  rounds.checkMembersAt (fun d {_ _ _} ops => GateMember (name d) defs ops) fun d _ _ {_ _ _} ops => do
    let ⟨sig⟩ ← gateSignature b (name d)
    let ⟨law⟩ ← Gate.check (sourceRows b) (.inr (name d)) sig defs unique ops
    return ⟨sig, law⟩

def checkGateMembers (name : PrimitiveName) (defs : Defs b.vocabulary hs) (unique : (hs.fns.map (·.key)).Nodup)
    (rounds : Sequence hs (sourceEvents b) st running term n) : Option (GateMembers name defs rounds) := do
  let ⟨bound⟩ ← gateSignature b name
  let ⟨members⟩ ← rounds.checkMembers _ (Gate.check (sourceRows b) _ bound defs unique)
  return ⟨bound,members⟩

end

end Zkc.Formal.Written.SumcheckRows
