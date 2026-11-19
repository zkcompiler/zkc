module

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

end Zkc.Formal.Written.SumcheckRows
