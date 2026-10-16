module

public import Zkc.Semantics.Execution
public import Zkc.Semantics.MonadExecution

@[expose] public section

/-! Program-producing interpretations of finite protocol operations.

An operation may expand into an entire lower-level process. Interpretation
preserves stopping and sequencing; its laws make staged lowerings compositional.
An interpretation is not itself a cryptographic security reduction.
-/

set_option autoImplicit false

namespace PIR

variable {I J K : Signature} {A B C S E : Type}

/-- An interpretation preserves the logical reply type of each source operation. -/
abbrev OperationInterpretation (I J : Signature) :=
  (op : I.Op) → Proc J (I.Reply op)

namespace Proc

theorem bind_assoc (source : Proc I A) (next : A → Proc I B)
    (last : B → Proc I C) :
    (source.bind next).bind last = source.bind (fun value => (next value).bind last) := by
  induction source with
  | done value => rfl
  | halt why => rfl
  | call op tail ih =>
    simp only [bind]
    congr 1
    funext reply
    exact ih reply

@[simp] theorem bind_done (source : Proc I A) : source.bind .done = source := by
  induction source with
  | done value => rfl
  | halt why => rfl
  | call op tail ih =>
    simp only [bind]
    congr 1
    funext reply
    exact ih reply

def interpret (operations : OperationInterpretation I J) : Proc I A → Proc J A
  | .done value => .done value
  | .halt why => .halt why
  | .call op next => (operations op).bind (fun reply => (next reply).interpret operations)

theorem interpret_bind (operations : OperationInterpretation I J)
    (source : Proc I A) (next : A → Proc I B) :
    (source.bind next).interpret operations =
      (source.interpret operations).bind (fun value => (next value).interpret operations) := by
  induction source with
  | done value => rfl
  | halt why => rfl
  | call op tail ih =>
    simp only [bind, interpret, bind_assoc]
    congr 1
    funext reply
    exact ih reply

@[simp] theorem interpret_identity (source : Proc I A) :
    source.interpret (fun op => .call op .done) = source := by
  induction source with
  | done value => rfl
  | halt why => rfl
  | call op next ih =>
    simp only [interpret, bind]
    congr 1
    funext reply
    exact ih reply

theorem interpret_comp (first : OperationInterpretation I J)
    (second : OperationInterpretation J K) (source : Proc I A) :
    (source.interpret first).interpret second =
      source.interpret (fun op => (first op).interpret second) := by
  induction source with
  | done value => rfl
  | halt why => rfl
  | call op next ih =>
    simp only [interpret, interpret_bind]
    congr 1
    funext reply
    exact ih reply

/-- Lowering and then executing agrees with executing the composed handler,
including all stopped post-states and the ordered events of expanded calls. -/
theorem run_interpret (operations : OperationInterpretation I J)
    (backend : Handler J S E) (source : Proc I A) (state : S) :
    (source.interpret operations).run backend state =
      source.run (fun op s => (operations op).run backend s) state := by
  induction source generalizing state with
  | done value => rfl
  | halt why => rfl
  | call op next ih =>
    simp only [interpret, run_bind, run]
    congr 1
    funext reply last
    exact ih reply last

/-- Monadic staging preserves the entire inner execution, including stopping
state and event prefixes. Outer effects retain their selected monad semantics;
this theorem asserts neither normalization nor recovery from outer errors. -/
theorem runM_interpret {m : Type → Type} [Monad m] [LawfulMonad m]
    (operations : OperationInterpretation I J) (backend : MonadHandler m J S E)
    (source : Proc I A) (state : S) :
    (source.interpret operations).runM backend state =
      source.runM (fun op s => (operations op).runM backend s) state := by
  induction source generalizing state with
  | done value => rfl
  | halt why => rfl
  | call op next ih =>
    simp only [interpret, runM_bind, runM]
    congr 1
    funext result
    rcases result with ⟨outcome, residual, events⟩
    cases outcome with
    | stopped why => rfl
    | returned value =>
      simp only [Execution.followM]
      rw [ih]

/-- A distributional provider-state interpretation composes with program
interpretation using the existing local state law. Contexts receive replies,
not the hidden state sampled by `expandState`. -/
theorem runM_interpret_expand {m : Type → Type} [Monad m] [LawfulMonad m]
    {T : Type} (operations : OperationInterpretation I J) (expandState : S → m T)
    (sourceHandler : MonadHandler m I S E) (backend : MonadHandler m J T E)
    (law : ∀ op s, (expandState s >>= (operations op).runM backend) =
      (sourceHandler op s >>= Execution.expand expandState))
    (source : Proc I A) (state : S) :
    (expandState state >>= (source.interpret operations).runM backend) =
      (source.runM sourceHandler state >>= Execution.expand expandState) := by
  have same : (source.interpret operations).runM backend =
      source.runM (fun op s => (operations op).runM backend s) :=
    funext (runM_interpret operations backend source)
  rw [same]
  exact runM_expand expandState sourceHandler _ law source state

/-- A checked component may choose a different private state representation.
The per-operation simulation is an explicit premise; structural interface
conformance alone does not prove it. All stops, residual states and observable
events are compared by the existing execution relation. -/
theorem run_interpret_related {T F O : Type}
    (operations : OperationInterpretation I J)
    (sourceHandler : Handler I S E) (targetHandler : Handler J T F)
    (relation : S → T → Prop) (left : E → List O) (right : F → List O)
    (law : ∀ op s t, relation s t →
      Related relation left right (sourceHandler op s)
        ((operations op).run targetHandler t))
    (source : Proc I A) (s : S) (t : T) (initial : relation s t) :
    Related relation left right (source.run sourceHandler s)
      ((source.interpret operations).run targetHandler t) := by
  rw [run_interpret]
  exact run_related relation left right sourceHandler
    (fun op state => (operations op).run targetHandler state)
    law source s t initial

/-- Separate construction of a prefix and suffix passes the actual residual
state to the suffix, including provider state and transcript history. -/
theorem run_interpret_bind (operations : OperationInterpretation I J)
    (backend : Handler J S E) (source : Proc I A) (next : A → Proc I B) (state : S) :
    ((source.bind next).interpret operations).run backend state =
      ((source.interpret operations).run backend state).follow
        (fun value residual => ((next value).interpret operations).run backend residual) := by
  rw [interpret_bind, run_bind]

/-- Interchanging staging routes requires agreement of their actual operation
expansions. Composition associativity does not supply this square. -/
theorem interpret_interchange (first : OperationInterpretation I J)
    (second : OperationInterpretation J K) (direct : OperationInterpretation I K)
    (square : ∀ op, (first op).interpret second = direct op) (source : Proc I A) :
    (source.interpret first).interpret second = source.interpret direct := by
  rw [interpret_comp]
  congr 1
  funext op
  exact square op

/-- A model-specific equation survives staging only if the actual composite
handler satisfies the model's premises. No law follows from an interface alone. -/
theorem interpret_model_law (models : Handler I S E → Prop)
    (before after : Proc I A)
    (law : ∀ handler, models handler → ∀ state,
      before.run handler state = after.run handler state)
    (operations : OperationInterpretation I J) (backend : Handler J S E)
    (admissible : models (fun op s => (operations op).run backend s)) (state : S) :
    (before.interpret operations).run backend state =
      (after.interpret operations).run backend state := by
  rw [run_interpret, run_interpret]
  exact law _ admissible state

end Proc
end PIR
