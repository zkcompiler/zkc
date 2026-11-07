module

public import Zkc.Source.DeriveRegion
public import Zkc.Source.Structured.DomainEvaluation

@[expose] public section

/-! Derive source arithmetic over abstract word functions, then instantiate
them with the executable unsigned semantics. Keeping the functions abstract
during composition avoids kernel evaluation of symbolic modulo-2^64 terms. -/
set_option autoImplicit false
namespace Zkc.Source.Structured.WordDerivation
variable {model : DomainModel} {I : PIR.Signature} {observation : SiteObservations I}
  {table : Evaluation.MeaningsOn model.toCarriers I} {f : Nat → Nat → Nat}

theorem add (represented : wrappingAdd = f) (x y : Nat) :
    (Evaluation.meaningOn model observation table).OperationLaw (fun op ↦ .call op .done)
      .indexWrappingAdd (.cons x (.cons y .nil)) .nil (.done (.cons (f x y) .nil)) := by
  cases represented
  exact RegionMeaning.OperationLaw.identity _ _ _ rfl

theorem sub (represented : wrappingSubtract = f) (x y : Nat) :
    (Evaluation.meaningOn model observation table).OperationLaw (fun op ↦ .call op .done)
      .indexWrappingSubtract (.cons x (.cons y .nil)) .nil (.done (.cons (f x y) .nil)) := by
  cases represented
  exact RegionMeaning.OperationLaw.identity _ _ _ rfl

theorem band (represented : bitAnd = f) (x y : Nat) :
    (Evaluation.meaningOn model observation table).OperationLaw (fun op ↦ .call op .done)
      .indexBitAnd (.cons x (.cons y .nil)) .nil (.done (.cons (f x y) .nil)) := by
  cases represented
  exact RegionMeaning.OperationLaw.identity _ _ _ rfl

theorem shr (represented : logicalShiftRight = f) (x y : Nat) :
    (Evaluation.meaningOn model observation table).OperationLaw (fun op ↦ .call op .done)
      .indexLogicalShiftRight (.cons x (.cons y .nil)) .nil (.done (.cons (f x y) .nil)) := by
  cases represented
  exact RegionMeaning.OperationLaw.identity _ _ _ rfl

/-- Use the ordinary region constructor with symbolic word operations.
Other operations use their existing meanings. The theorem obtained after
specialization is about the original process and the actual machine words. -/
syntax "derive_word_process" : tactic
macro_rules
  | `(tactic| derive_word_process) => `(tactic|
      (generalize hAdd : wrappingAdd = addWord, hSub : wrappingSubtract = subWord,
         hAnd : bitAnd = andWord, hShr : logicalShiftRight = shiftWord
       as_aux_lemma =>
         derive_process using
           (first
            | apply WordDerivation.add hAdd
            | apply WordDerivation.sub hSub
            | apply WordDerivation.band hAnd
            | apply WordDerivation.shr hShr)))

end Zkc.Source.Structured.WordDerivation
