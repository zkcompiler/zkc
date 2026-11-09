module

public import Zkc.Protocol.Semantics.System

/-! Process-indexed quantitative reasoning through the single upstream specification fold. -/

public section
open PIR PFunctor MeasureTheory ProbabilityTheory

namespace ProtocolProof

/-- A local transformer sees every outcome and the complete reached state and event prefix. -/
@[expose, implicit_reducible] def OperationSpec (I : Signature) (S L : Type) :=
  OpSpec (Internal.effects I) ((S × List L) → ENNReal)

/-- Monotonicity is the existing upstream order on continuation potentials. -/
@[expose] def OperationSpec.Monotone {I : Signature} {S L : Type}
    (spec : OperationSpec I S L) : Prop := OpSpec.Monotone spec

/-- The sole quantitative interpretation is the upstream fold of the failure-aware encoding. -/
@[expose] noncomputable def wpFold {I : Signature} {S L A : Type}
    (spec : OperationSpec I S L) (program : Process I A)
    (post : Outcome A → (S × List L) → ENNReal) : (S × List L) → ENNReal :=
  FreeM.wpFold spec (Internal.encode program) post

/-- Exact expectations of complete primitive replies and accumulated state. -/
@[expose] noncomputable def opExpectation {I : Signature} {S L : Type}
    [∀ op, MeasurableSpace (I.Reply op)] [MeasurableSpace S] [MeasurableSpace L]
    (handler : (op : I.Op) → Kernel (S × List L)
      (Outcome (I.Reply op) × (S × List L))) : OperationSpec I S L :=
  Internal.opExpectation handler

theorem opExpectation_monotone {I : Signature} {S L : Type}
    [∀ op, MeasurableSpace (I.Reply op)] [MeasurableSpace S] [MeasurableSpace L]
    (handler : (op : I.Op) → Kernel (S × List L)
      (Outcome (I.Reply op) × (S × List L))) : (opExpectation handler).Monotone :=
  Internal.opExpectation_monotone (P := Internal.effects I) handler

@[simp] theorem wpFold_done {I : Signature} {S L A : Type}
    (spec : OperationSpec I S L) (value : A) (post : Outcome A → (S × List L) → ENNReal) :
    wpFold spec (.done value) post = post (.returned value) := rfl

@[simp] theorem wpFold_halt {I : Signature} {S L A : Type}
    (spec : OperationSpec I S L) (reason : Stop) (post : Outcome A → (S × List L) → ENNReal) :
    wpFold spec (.halt reason) post = post (.stopped reason) := rfl

@[simp] theorem wpFold_operation {I : Signature} {S L : Type}
    (spec : OperationSpec I S L) (operation : I.Op)
    (post : Outcome (I.Reply operation) → (S × List L) → ENNReal) :
    wpFold spec (.call operation .done) post = spec operation post := by
  unfold wpFold
  rw [Internal.encode_operation]
  rfl

theorem wpFold_bind {I : Signature} {S L A B : Type} (spec : OperationSpec I S L)
    (program : Process I A) (next : A → Process I B)
    (post : Outcome B → (S × List L) → ENNReal) :
    wpFold spec (program.bind next) post = wpFold spec program (fun outcome ↦
      match outcome with
      | .returned value => wpFold spec (next value) post
      | .stopped reason => post (.stopped reason)) := by
  unfold wpFold
  rw [Internal.encode_bind]
  unfold Internal.outcomeBind
  refine (FreeM.wpFold_bind' (P := Internal.effects I) spec
    (Internal.encode program) (fun answer ↦ match answer with
      | .returned value => Internal.encode (next value)
      | .stopped reason => FreeM.pure (.stopped reason)) post).trans ?_
  congr 1
  funext outcome
  cases outcome <;> rfl

@[simp] theorem wpFold_call {I : Signature} {S L A : Type} (spec : OperationSpec I S L)
    (operation : I.Op) (next : I.Reply operation → Process I A)
    (post : Outcome A → (S × List L) → ENNReal) :
    wpFold spec (.call operation next) post = spec operation (fun outcome ↦
      match outcome with
      | .returned value => wpFold spec (next value) post
      | .stopped reason => post (.stopped reason)) := by
  unfold wpFold
  rw [Internal.encode]
  refine (FreeM.wpFold_liftBind (P := Internal.effects I) spec operation
    (fun outcome ↦ match outcome with
      | .returned value => Internal.encode (next value)
      | .stopped reason => FreeM.pure (.stopped reason)) post).trans ?_
  congr 1
  funext outcome
  cases outcome <;> rfl

/-- Returning rewards can ignore stops only by explicitly assigning them zero. -/
@[expose] def returnedReward {A S L : Type} (post : A → S → ENNReal) :
    Outcome A → (S × List L) → ENNReal
  | .returned value, current => post value current.1
  | .stopped _, _ => 0

end ProtocolProof
