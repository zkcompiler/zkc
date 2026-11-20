module

public import Zkc.Formal.Interactive.GateSequence
public import Zkc.Formal.Interactive.HonestReduction
public import Zkc.Vocabulary.Project

@[expose] public section
namespace Zkc.Formal.Written.SumcheckRows
open Core Zkc.Vocabulary.Project Interactive.Sumcheck

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

open ReductionRound

section
variable {b : Bindings} {hs : Headers b.vocabulary} {Γ : Ctx (LTy b.vocabulary)}
    {outs : List (LTy b.vocabulary)} {st : b.vocabulary.Ty} {running : Var Γ (shared (sourceRows b).scalarTy)}
    {term : Term (protocolDialect b.vocabulary hs) Γ outs} {n : Nat}

/-- An executable gate primitive and the verified member implementations that use it. -/
structure GateMembers (name : PrimitiveName) (defs : Defs b.vocabulary hs)
    (rounds : Sequence hs (sourceEvents b) st running term n) : Type where
  bound : b.vocabulary.row (.inr name) = some (Gate.signature (sourceRows b))
  members : rounds.AllMembers (fun ops => Gate.Laws (sourceRows b) (.inr name) bound defs ops)

def checkGateMembers (name : PrimitiveName) (defs : Defs b.vocabulary hs) (unique : (hs.fns.map (·.key)).Nodup)
    (rounds : Sequence hs (sourceEvents b) st running term n) : Option (GateMembers name defs rounds) := do
  let rows := sourceRows b
  if sig : b.signature name = some ⟨[Gate.message rows,rows.scalarTy],[rows.scalarTy]⟩ then
    have bound : b.vocabulary.row (.inr name) = some (Gate.signature rows) := by
      change ((b.signature name).map _).map _ = _
      rw [sig]
      rfl
    let ⟨members⟩ ← rounds.checkMembers _ (Gate.check rows _ bound defs unique)
    return ⟨bound,members⟩
  else none
end

end Zkc.Formal.Written.SumcheckRows
