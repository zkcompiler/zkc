module

public import Zkc.Construction.OriginalLaws
public import Zkc.Construction.DomainBinding
public import Zkc.Semantics.Yields

@[expose] public section

/-! A structural certificate connecting an original-derived process to an
actual nominal artifact process. Checkpoints are explicit frame obligations;
all other operations, replies and stops agree. A producer's extra false guard
cannot be hidden by a structural artifact-admission check.
-/
set_option autoImplicit false
namespace Zkc.Construction.Original
open Zkc.Source
variable {carriers : Structured.Carriers} {A B : Type}

/-- At a checkpoint the certificate must justify the entire physical frame
against this exact source continuation. The caller fixes this live-value
relation before deriving the certificate. -/
inductive Simulation
    (returns : A → B → Prop)
    (live : PIR.Process (Domain.effects carriers) A → Domain.Environment carriers → Prop) :
    PIR.Process (Domain.effects carriers) A → PIR.Process (Domain.effects carriers) B → Type where
  | done {a : A} {b : B} (related : returns a b) : Simulation returns live (.done a) (.done b)
  | halt (reason : PIR.Stop) : Simulation returns live (.halt reason) (.halt reason)
  | call (operation : (Domain.effects carriers).Op)
      {left : (Domain.effects carriers).Reply operation → PIR.Process (Domain.effects carriers) A}
      {right : (Domain.effects carriers).Reply operation → PIR.Process (Domain.effects carriers) B}
      (next : ∀ reply, Simulation returns live (left reply) (right reply)) :
      Simulation returns live (.call operation left) (.call operation right)
  | checkpoint {source : PIR.Process (Domain.effects carriers) A}
      {target : PIR.Process (Domain.effects carriers) B} (frame : Domain.Environment carriers)
      (related : live source frame) (next : Simulation returns live source target) :
      Simulation returns live source (.call (.checkpoint frame) fun _ => target)

/-- Project just the administrative checkpoint operations. This is a process
projection theorem, not a claim that runtime frames can be discarded. -/
def forgetCheckpoints : PIR.OperationInterpretation (Domain.effects carriers) (Domain.effects carriers)
  | .checkpoint _ => .done ()
  | operation => .call operation .done

/-- For equal result carriers, the complete non-administrative process agrees.
The independent `live` evidence remains available in the certificate. -/
theorem Simulation.forget {live : PIR.Process (Domain.effects carriers) A → Domain.Environment carriers → Prop}
    {source target : PIR.Process (Domain.effects carriers) A}
    (derivation : Simulation Eq live source target) :
    target.interpret forgetCheckpoints = source.interpret forgetCheckpoints := by
  induction derivation with
  | done related => cases related; rfl
  | halt => rfl
  | call operation next ih =>
      simp only [PIR.Process.interpret]
      congr 1
      funext reply
      exact ih reply
  | checkpoint frame related next ih =>
      simpa only [PIR.Process.interpret, forgetCheckpoints, PIR.Process.bind] using ih

/-- Compose source and artifact suffixes with all actual returned values. A
stopped prefix requires no continuation certificate. Live obligations in the
composite are supplied at the exact continued source process. -/
noncomputable def Simulation.bind {C D : Type}
    {firstRelation : A → B → Prop} {returnRelation : C → D → Prop}
    {source : PIR.Process (Domain.effects carriers) A}
    {target : PIR.Process (Domain.effects carriers) B}
    {sourceNext : A → PIR.Process (Domain.effects carriers) C}
    {targetNext : B → PIR.Process (Domain.effects carriers) D}
    {firstLive : PIR.Process (Domain.effects carriers) A → Domain.Environment carriers → Prop}
    {nextLive : PIR.Process (Domain.effects carriers) C → Domain.Environment carriers → Prop}
    (head : Simulation firstRelation firstLive source target)
    (frames : ∀ process frame, firstLive process frame → nextLive (process.bind sourceNext) frame)
    (tail : ∀ a b, firstRelation a b →
      Simulation returnRelation nextLive (sourceNext a) (targetNext b)) :
    Simulation returnRelation nextLive (source.bind sourceNext) (target.bind targetNext) := by
  induction head with
  | done related => exact tail _ _ related
  | halt reason => exact .halt reason
  | call operation next ih => exact .call operation ih
  | checkpoint frame related next ih => exact .checkpoint frame (frames _ _ related) ih

/-- Structural loop composition: each callback works for every related carried
state and every reply, and the frame law accounts for its continued suffix. -/
noncomputable def Simulation.finite {Item : Type}
    {relation : A → B → Prop}
    {live : PIR.Process (Domain.effects carriers) A → Domain.Environment carriers → Prop}
    (left : A → Item → PIR.Process (Domain.effects carriers) A)
    (right : B → Item → PIR.Process (Domain.effects carriers) B)
    (body : ∀ a b item, relation a b → Simulation relation live (left a item) (right b item))
    (frames : ∀ process items frame, live process frame →
      live (process.bind (Finite.fold left items)) frame)
    (items : List Item) (a : A) (b : B) (related : relation a b) :
    Simulation relation live (Finite.fold left items a) (Finite.fold right items b) := by
  induction items generalizing a b with
  | nil => exact .done related
  | cons item rest ih =>
      exact (body a b item related).bind (fun process frame => frames process rest frame)
        (fun a b related => ih a b related)

/-- The existing constructed loop is exactly a finite fold of the body and
its checked yield. This exposes its failure branches without a new evaluator. -/
theorem iterate_eq_fold
    (body : Domain.Environment carriers → PIR.Process (Domain.effects carriers) (Domain.Environment carriers))
    (outer : Domain.Environment carriers) (yielded : List Nat) (declared : List ValueSort)
    (indices : List Nat) (initial : Domain.Environment carriers) :
    Domain.iterate body outer yielded declared indices initial =
      Finite.fold (fun carried index =>
        (body (outer ++ .data (.index index) :: carried)).bind fun final =>
          match Domain.read final yielded with
          | none => .halt .refused
          | some next => if Domain.sortsMatch declared next then .done next else .halt .refused)
        indices initial := by
  induction indices generalizing initial with
  | nil => rfl
  | cons index rest ih =>
      simp only [Domain.iterate, Finite.fold, PIR.Process.bind_assoc]
      congr 1
      funext final
      cases found : Domain.read final yielded with
      | none => rfl
      | some next =>
          by_cases matched : Domain.sortsMatch declared next = true
          · simpa only [matched, ↓reduceIte, PIR.Process.bind] using ih next
          · simp only [matched, Bool.false_eq_true, ↓reduceIte, PIR.Process.bind]

/-- A callback certificate includes the actual compiled body and yield checks.
No hypothesis limits provider replies to successful or honest executions. -/
noncomputable def Simulation.iterate
    {relation : A → Domain.Environment carriers → Prop}
    {live : PIR.Process (Domain.effects carriers) A → Domain.Environment carriers → Prop}
    (left : A → Nat → PIR.Process (Domain.effects carriers) A)
    (body : Domain.Environment carriers → PIR.Process (Domain.effects carriers) (Domain.Environment carriers))
    (outer : Domain.Environment carriers) (yielded : List Nat) (declared : List ValueSort)
    (law : ∀ a carried index, relation a carried → Simulation relation live (left a index)
      ((body (outer ++ .data (.index index) :: carried)).bind fun final =>
        match Domain.read final yielded with
        | none => .halt .refused
        | some next => if Domain.sortsMatch declared next then .done next else .halt .refused))
    (frames : ∀ process items frame, live process frame →
      live (process.bind (Finite.fold left items)) frame)
    (indices : List Nat) (a : A) (carried : Domain.Environment carriers) (related : relation a carried) :
    Simulation relation live (Finite.fold left indices a)
      (Domain.iterate body outer yielded declared indices carried) := by
  rw [iterate_eq_fold]
  exact Simulation.finite left _ law frames indices a carried related

/-- This refusal is semantic: no certificate can connect a returned original
process to an artifact that rejects, even if checkProducer accepts its syntax. -/
theorem Simulation.done_not_halt
    {returns : A → B → Prop}
    {live : PIR.Process (Domain.effects carriers) A → Domain.Environment carriers → Prop}
    (value : A) (reason : PIR.Stop) :
    IsEmpty (Simulation returns live (.done value) (.halt reason)) := by
  constructor
  intro derivation
  cases derivation

/-- The certificate constructs an instrumented original view. It retains the
complete original return and the complete artifact return together. All added
checkpoints carry the certificate's explicit live-frame obligation. -/
def Simulation.paired {returns : A → B → Prop}
    {live : PIR.Process (Domain.effects carriers) A → Domain.Environment carriers → Prop}
    {source : PIR.Process (Domain.effects carriers) A} {target : PIR.Process (Domain.effects carriers) B} :
    Simulation returns live source target → PIR.Process (Domain.effects carriers) (A × B)
  | .done (a := a) (b := b) _ => .done (a, b)
  | .halt reason => .halt reason
  | .call operation next => .call operation fun reply => (next reply).paired
  | .checkpoint frame _ next => .call (.checkpoint frame) fun _ => next.paired

/-- All replies preserve the full return relation, not just a selected Boolean.
A stop has no return obligation and remains present in both projections. -/
theorem Simulation.paired_yields {returns : A → B → Prop}
    {live : PIR.Process (Domain.effects carriers) A → Domain.Environment carriers → Prop}
    {source : PIR.Process (Domain.effects carriers) A} {target : PIR.Process (Domain.effects carriers) B}
    (derivation : Simulation returns live source target) :
    PIR.Yields (fun pair => returns pair.1 pair.2) derivation.paired := by
  induction derivation with
  | done related => exact related
  | halt => trivial
  | call operation next ih => exact ih
  | checkpoint frame related next ih => exact fun _ => ih

/-- The target projection is exact, including every checkpoint and final frame.
The equation is derived structurally, not supplied as a certificate field. -/
theorem Simulation.target {returns : A → B → Prop}
    {live : PIR.Process (Domain.effects carriers) A → Domain.Environment carriers → Prop}
    {source : PIR.Process (Domain.effects carriers) A} {target : PIR.Process (Domain.effects carriers) B}
    (derivation : Simulation returns live source target) :
    derivation.paired.bind (fun pair => .done pair.2) = target := by
  induction derivation with
  | done => rfl
  | halt => rfl
  | call operation next ih =>
      simp only [paired, PIR.Process.bind]
      congr 1
      funext reply
      exact ih reply
  | checkpoint frame related next ih =>
      simp only [paired, PIR.Process.bind, ih]

/-- Projecting the original ABI and forgetting only the explicitly certified
physical checkpoints recovers the original construction fold. -/
theorem Simulation.source {returns : A → B → Prop}
    {live : PIR.Process (Domain.effects carriers) A → Domain.Environment carriers → Prop}
    {source : PIR.Process (Domain.effects carriers) A} {target : PIR.Process (Domain.effects carriers) B}
    (derivation : Simulation returns live source target) :
    (derivation.paired.bind (fun pair => .done pair.1)).interpret forgetCheckpoints =
      source.interpret forgetCheckpoints := by
  induction derivation with
  | done => rfl
  | halt => rfl
  | call operation next ih =>
      simp only [paired, PIR.Process.bind, PIR.Process.interpret]
      congr 1
      funext reply
      exact ih reply
  | checkpoint frame related next ih =>
      simpa only [paired, PIR.Process.bind, PIR.Process.interpret, forgetCheckpoints] using ih

/-- Removing return values still preserves the full interaction shape. This
necessary condition can refute an artifact that adds a rejection after a
successful source prefix, independently of its artifact-admission result. -/
theorem Simulation.shape {returns : A → B → Prop}
    {live : PIR.Process (Domain.effects carriers) A → Domain.Environment carriers → Prop}
    {source : PIR.Process (Domain.effects carriers) A} {target : PIR.Process (Domain.effects carriers) B}
    (derivation : Simulation returns live source target) :
    (target.bind (fun _ => .done ())).interpret forgetCheckpoints =
      (source.bind (fun _ => .done ())).interpret forgetCheckpoints := by
  induction derivation with
  | done => rfl
  | halt => rfl
  | call operation next ih =>
      simp only [PIR.Process.bind, PIR.Process.interpret]
      congr 1
      funext reply
      exact ih reply
  | checkpoint frame related next ih =>
      simpa only [PIR.Process.bind, PIR.Process.interpret, forgetCheckpoints] using ih

/-- Generic execution projection leaves the entire runtime state and ordered
observation prefix untouched, including on stopped computations. -/
def mapExecution {R E C D : Type} (mapping : C → D) (execution : PIR.Execution R E C) :
    PIR.Execution R E D :=
  ⟨match execution.outcome with
    | .returned value => .returned (mapping value)
    | .stopped reason => .stopped reason, execution.state, execution.events⟩

theorem runM_map {I : PIR.Signature} {R E C D : Type}
    {m : Type → Type} [Monad m] [LawfulMonad m]
    (process : PIR.Process I C) (mapping : C → D) (handler : PIR.MonadHandler m I R E) (state : R) :
    (process.bind (fun value => .done (mapping value))).runM handler state =
      (do let execution ← process.runM handler state; pure (mapExecution mapping execution)) := by
  rw [PIR.runM_bind]
  congr 1
  funext execution
  cases execution with
  | mk outcome final events =>
      cases outcome <;> simp [PIR.Execution.followM, PIR.Process.runM, mapExecution]

/-- Exact execution transport in every lawful monad. In a producer/validator
instantiation `R` is the existing RuntimeState, so no proof buffer, oracle or
private-service post-state is projected away. The paired source view also
retains the full original ABI. -/
theorem Simulation.runM {returns : A → B → Prop}
    {live : PIR.Process (Domain.effects carriers) A → Domain.Environment carriers → Prop}
    {source : PIR.Process (Domain.effects carriers) A} {target : PIR.Process (Domain.effects carriers) B}
    (derivation : Simulation returns live source target)
    {m : Type → Type} [Monad m] [LawfulMonad m] {R E : Type}
    (handler : PIR.MonadHandler m (Domain.effects carriers) R E) (state : R) :
    target.runM handler state =
      (do let execution ← derivation.paired.runM handler state
          pure (mapExecution Prod.snd execution)) := by
  exact (congrArg (fun process => process.runM handler state) derivation.target).symm.trans
    (runM_map _ _ _ _)

end Zkc.Construction.Original
