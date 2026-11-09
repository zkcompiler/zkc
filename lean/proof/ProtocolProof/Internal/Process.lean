module

public import ProtocolProof.Semantics.Execution
public import ProtocolProof.Internal.System

/-! Failure-aware interpretation into the existing upstream FreeM backend. -/

public section
open PIR PFunctor MeasureTheory ProbabilityTheory

namespace ProtocolProof.Internal

@[expose, implicit_reducible] def effects (I : Signature) : PFunctor where
  A := I.Op
  B operation := Outcome (I.Reply operation)

instance {I : Signature} [∀ op, MeasurableSpace (I.Reply op)] :
    (op : (effects I).A) → MeasurableSpace ((effects I).B op) :=
  fun op ↦ inferInstanceAs (MeasurableSpace (Outcome (I.Reply op)))
@[expose] instance {I : Signature} [∀ op, Countable (I.Reply op)] :
    (op : (effects I).A) → Countable ((effects I).B op) :=
  fun op ↦ inferInstanceAs (Countable (Outcome (I.Reply op)))
@[expose] instance {I : Signature} [∀ op, MeasurableSpace (I.Reply op)]
    [∀ op, MeasurableSingletonClass (I.Reply op)] :
    (op : (effects I).A) → MeasurableSingletonClass ((effects I).B op) :=
  fun op ↦ inferInstanceAs (MeasurableSingletonClass (Outcome (I.Reply op)))

@[expose] def encode {I : Signature} {A : Type} : Process I A → FreeM (effects I) (Outcome A)
  | .done value => .pure (.returned value)
  | .halt reason => .pure (.stopped reason)
  | .call operation next => .liftBind operation fun answer ↦
      match answer with
      | .returned value => encode (next value)
      | .stopped reason => .pure (.stopped reason)

@[expose] def outcomeBind {I : Signature} {A B : Type}
    (program : FreeM (effects I) (Outcome A))
    (next : A → FreeM (effects I) (Outcome B)) : FreeM (effects I) (Outcome B) :=
  program >>= fun answer ↦ match answer with
    | .returned value => next value
    | .stopped reason => pure (.stopped reason)

theorem encode_bind {I : Signature} {A B : Type}
    (program : Process I A) (next : A → Process I B) :
    encode (program.bind next) = outcomeBind (encode program) (fun value ↦ encode (next value)) := by
  induction program with
  | done value => rfl
  | halt reason => rfl
  | call operation tail ih =>
      simp only [Process.bind, encode, outcomeBind, bind, FreeM.bind]
      congr 1
      funext answer
      cases answer with
      | returned value => exact ih value
      | stopped reason => rfl

@[expose] def monadHandler {m : Type → Type} [Monad m] {I : Signature} {S L : Type}
    (handler : MonadHandler m I S L) (operation : I.Op) :
    StateT (S × List L) m (Outcome (I.Reply operation)) := fun current ↦ do
  let result ← handler operation current.1
  pure (result.outcome, (result.state, current.2 ++ result.events))

/-- The interpretation preserves the complete shared monadic execution in every lawful monad. -/
theorem complete_execution {m : Type → Type} [Monad m] [LawfulMonad m]
    {I : Signature} {S L A : Type} (handler : MonadHandler m I S L)
    (program : Process I A) (state : S) (priorEvents : List L) :
    ((encode program).liftM (monadHandler handler)) (state, priorEvents) =
      (do
        let result ← program.runM handler state
        pure (result.outcome, (result.state, priorEvents ++ result.events))) := by
  induction program generalizing state priorEvents with
  | done value => simp only [encode, Process.runM, pure_bind, List.append_nil]; rfl
  | halt reason => simp only [encode, Process.runM, pure_bind, List.append_nil]; rfl
  | call operation next ih =>
      simp only [encode, FreeM.liftM, bind, StateT.bind, monadHandler, Process.runM,
        bind_assoc, pure_bind]
      congr 1
      funext result
      cases result with
      | mk outcome reached events =>
          cases outcome with
          | stopped reason => simp only [Execution.followM, pure_bind]; rfl
          | returned value =>
              simp only [Execution.followM, bind_assoc, pure_bind]
              rw [ih]
              simp only [List.append_assoc]

end ProtocolProof.Internal

namespace ProtocolProof.Internal
open PIR PFunctor

/-- An isolated public call has exactly the backend outcome-valued primitive meaning. -/
theorem encode_operation {I : Signature} (operation : I.Op) :
    encode (.call operation .done) = (FreeM.lift operation : FreeM (effects I) _) := by
  simp only [encode, FreeM.lift]
  congr 1
  funext answer
  cases answer <;> rfl

end ProtocolProof.Internal
