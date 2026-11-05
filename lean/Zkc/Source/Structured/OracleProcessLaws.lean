module

public import Zkc.Source.Structured.OracleProcess

@[expose] public section

/-! Structural totality of the outer presentation, without restricting source outcomes or
assuming a probability distribution is lossless. All monad effects still come from `runM`.
-/

set_option autoImplicit false
namespace Zkc.Source.Structured.OracleProcess
variable {I J : PIR.Signature} {S T E F A B : Type}

/-- Source stops are returned records; the presentation has no outer halt constructor. -/
def NonStopping : PIR.Process I A → Prop
  | .done _ => True
  | .halt _ => False
  | .call _ next => ∀ reply, NonStopping (next reply)

theorem nonStopping_bind (process : PIR.Process I A) (next : A → PIR.Process I B)
    (first : NonStopping process) (tail : ∀ value, NonStopping (next value)) :
    NonStopping (process.bind next) := by
  induction process with
  | done value => exact tail value
  | halt reason => exact first.elim
  | call operation continuation ih => exact fun reply ↦ ih reply (first reply)

theorem nonStopping_map (change : A → B) (process : PIR.Process I A)
    (law : NonStopping process) : NonStopping (mapResult change process) :=
  nonStopping_bind process _ law (fun _ ↦ trivial)

theorem nonStopping_sequence (first : PIR.Execution S E A)
    (next : A → S → PIR.Process J (PIR.Execution S E B))
    (law : ∀ value state, NonStopping (next value state)) : NonStopping (sequence first next) := by
  cases first with
  | mk outcome state events =>
    cases outcome with
    | stopped reason => trivial
    | returned value => exact nonStopping_map _ _ (law value state)

theorem nonStopping_present (operations : (operation : I.Op) → S →
    PIR.Process J (PIR.Execution S E (I.Reply operation)))
    (law : ∀ operation state, NonStopping (operations operation state))
    (process : PIR.Process I A) (state : S) : NonStopping (present operations process state) := by
  induction process generalizing state with
  | done => trivial
  | halt => trivial
  | call operation continuation ih =>
    exact nonStopping_bind _ _ (law operation state) fun result ↦ nonStopping_sequence result _ ih

variable {m : Type → Type} [Monad m] [LawfulMonad m]

theorem runM_effect_call (external : PIR.MonadHandler m I S E)
    (request : (Effect I S E).Op) (next : (Effect I S E).Reply request →
      PIR.Process (Effect I S E) A) :
    (PIR.Process.call request next).runM (handlerM external) () =
      (external request.1 request.2 >>= fun reply ↦ (next reply).runM (handlerM external) ()) := by
  simp [PIR.Process.runM, handlerM, envelope, PIR.Execution.followM]

/-- Any postprocessing that agrees on returned records agrees for this outer process.
This is an equality in the entire monad, including any outer failure or missing mass. -/
theorem runM_postcongr (external : PIR.MonadHandler m I S E)
    (process : PIR.Process (Effect I S E) A) (total : NonStopping process)
    (left right : PIR.Execution Unit Empty A → m B)
    (agree : ∀ value, left (envelope value) = right (envelope value)) :
    (process.runM (handlerM external) () >>= left) =
      (process.runM (handlerM external) () >>= right) := by
  induction process with
  | done value => simpa only [PIR.Process.runM, pure_bind, envelope] using agree value
  | halt reason => exact total.elim
  | call operation continuation ih =>
    rw [runM_effect_call]
    simp only [bind_assoc]
    congr 1
    funext reply
    exact ih reply (total reply)

/-- Extraction's fallback cannot affect any result, for arbitrary lawful monadic providers. -/
theorem executeM_initial_irrelevant (external : PIR.MonadHandler m I S E)
    (process : PIR.Process (Effect I S E) (PIR.Execution T F A))
    (total : NonStopping process) (left right : T) :
    executeM external process left = executeM external process right := by
  apply runM_postcongr external process total
  intro value
  rfl

/-- Re-enveloping the extracted result recovers the generic `runM` execution exactly. -/
theorem executeM_envelope (external : PIR.MonadHandler m I S E)
    (process : PIR.Process (Effect I S E) (PIR.Execution T F A))
    (total : NonStopping process) (initial : T) :
    (executeM external process initial >>= fun result ↦ pure (envelope result)) =
      process.runM (handlerM external) () := by
  unfold executeM
  simp only [bind_assoc, pure_bind]
  calc
    _ = (process.runM (handlerM external) () >>= pure) := by
      apply runM_postcongr external process total
      intro value
      rfl
    _ = _ := bind_pure _

/-- A returned source record needs no provider interaction. -/
theorem executeM_done (external : PIR.MonadHandler m I S E)
    (result : PIR.Execution T F A) (initial : T) :
    executeM external (.done result) initial = pure result := by
  simp only [executeM, PIR.Process.runM, pure_bind]

/-- Sequence returned source records through their free presentation. Only the outer
presentation must be nonstopping; a source record may contain any stop and poststate. -/
theorem executeM_bind (external : PIR.MonadHandler m I S E)
    (process : PIR.Process (Effect I S E) (PIR.Execution T F A))
    (next : PIR.Execution T F A → PIR.Process (Effect I S E) (PIR.Execution T F B))
    (total : NonStopping process) (initial : T) :
    executeM external (process.bind next) initial =
      (executeM external process initial >>= fun result ↦ executeM external (next result) initial) := by
  unfold executeM
  rw [PIR.runM_bind]
  simp only [bind_assoc, pure_bind]
  apply runM_postcongr external process total
  intro result
  simp [envelope, PIR.Execution.followM]

/-- A pure change of source execution records commutes with provider interpretation. -/
theorem executeM_map (external : PIR.MonadHandler m I S E)
    (process : PIR.Process (Effect I S E) (PIR.Execution T F A))
    (change : PIR.Execution T F A → PIR.Execution T F B)
    (total : NonStopping process) (initial : T) :
    executeM external (mapResult change process) initial =
      (executeM external process initial >>= fun result ↦ pure (change result)) := by
  rw [mapResult, executeM_bind external process _ total]
  simp only [executeM_done]

/-- Source sequencing retains a stopped prefix and combines successful prefixes exactly. -/
theorem executeM_sequence (external : PIR.MonadHandler m I S E)
    (first : PIR.Execution T F A)
    (next : A → T → PIR.Process (Effect I S E) (PIR.Execution T F B))
    (total : ∀ value state, NonStopping (next value state)) (initial : T) :
    executeM external (sequence first next) initial =
      first.followM (fun value state ↦ executeM external (next value state) state) := by
  cases first with
  | mk outcome state events =>
    cases outcome with
    | stopped reason => simp only [sequence, executeM_done, PIR.Execution.followM]
    | returned value =>
      change executeM external
        (mapResult (fun result ↦ ⟨result.outcome, result.state, events ++ result.events⟩)
          (next value state)) initial = _
      rw [executeM_map external _ _ (total value state),
        executeM_initial_irrelevant external _ (total value state) initial state]
      rfl

/-- Execute a source presentation one action at a time on its original signature.
This exposes the existing state-relational handler laws even when the provider state
changes representation. It preserves the entire outer monad and every inner stop. -/
theorem executeM_present (external : PIR.MonadHandler m I S E)
    (operations : (operation : J.Op) → T →
      PIR.Process (Effect I S E) (PIR.Execution T F (J.Reply operation)))
    (total : ∀ operation state, NonStopping (operations operation state))
    (process : PIR.Process J A) (initial : T) :
    executeM external (present operations process initial) initial =
      process.runM (fun operation state ↦ executeM external (operations operation state) state)
        initial := by
  induction process generalizing initial with
  | done value => simp only [present, executeM_done, PIR.Process.runM]
  | halt reason => simp only [present, executeM_done, PIR.Process.runM]
  | call operation next ih =>
    simp only [present, PIR.Process.runM]
    rw [executeM_bind external _ _ (total operation initial)]
    congr 1
    funext result
    rw [executeM_sequence external _ _
      (fun value state ↦ nonStopping_present operations total (next value) state)]
    congr 1
    funext value state
    exact ih value state

/-- Target-effect interpretations compose by the existing generic Process theorem. -/
theorem runM_interpret (operations : PIR.OperationInterpretation I J)
    (backend : PIR.MonadHandler m J S E) (process : PIR.Process I A) (state : S) :
    (process.interpret operations).runM backend state =
      process.runM (fun operation current ↦ (operations operation).runM backend current) state :=
  PIR.runM_interpret operations backend process state

end Zkc.Source.Structured.OracleProcess
