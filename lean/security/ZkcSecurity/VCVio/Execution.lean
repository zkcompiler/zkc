module

public import Zkc.Semantics.MonadExecution
public import VCVio.OracleComp.EvalDist.Measure
public import VCVio.OracleComp.Constructions.SampleableType.NativeMeasure

@[expose] public section


namespace ZkcSecurity.VCVio.Execution

open OracleComp OracleSpec
open MeasureTheory
open scoped ENNReal

variable {F S E K A B : Type} {I : PIR.Signature}

abbrev Phase (S E K : Type) := S → ProbComp (PIR.Execution S E K)

def result (a : K) (s : S) : PIR.Execution S E K := ⟨.returned a, s, []⟩

/-- The bare participant profile has no public-abort work. -/
def noOp : Phase S E Unit := fun s => pure (result () s)

def mapPhase (f : A → B) (p : Phase S E A) : Phase S E B := fun s => do
  let e ← p s
  e.followM fun a s => pure (result (f a) s)

@[simp] theorem follow_result (a : A) (s : S)
    (k : A → S → ProbComp (PIR.Execution S E B)) :
    (result a s).followM k = k a s := by simp [result, PIR.Execution.followM]

theorem follow_mapPhase (f : A → B) (p : Phase S E A) (s : S)
    (k : B → S → ProbComp (PIR.Execution S E F)) :
    (do let e ← mapPhase f p s; e.followM k) =
      (do let e ← p s; e.followM (fun a s => k (f a) s)) := by
  simp [mapPhase, bind_assoc, PIR.followM_assoc]

theorem runM_bind_function (h : PIR.MonadHandler ProbComp I S E)
    (p : PIR.Process I A) (k : A → PIR.Process I B) :
    (p.bind k).runM h = (fun s => do
      let e ← p.runM h s
      e.followM fun a s => (k a).runM h s) := by
  funext s
  exact PIR.runM_bind h p k s

/-- An exact local law over residual state and events, not a reply-only law.
    Each fresh draw occurs after successful preparation. No port-name inference. -/
def freshQuery [SampleableType F] (before : Phase S E Unit)
    (after : F → Phase S E Unit) : Phase S E F := fun s => do
  let ready ← before s
  ready.followM fun _ s => do
    let r ← ($ᵗ F)
    let queried ← after r s
    queried.followM fun _ s => pure (result r s)

/-- Transport value-returning work through the existing bind. Stops, state and
ordered events belong to the phase; a successful value selects the continuation. -/
theorem runM_bind_transport {I : PIR.Signature} {S E A B : Type}
    (h : PIR.MonadHandler ProbComp I S E) (p : PIR.Process I A)
    (k : A → PIR.Process I B) (step : Phase S E A) (next : A → Phase S E B)
    (stepLaw : ∀ s, p.runM h s = step s)
    (nextLaw : ∀ a s, (k a).runM h s = next a s) (s : S) :
    (p.bind k).runM h s = (do let e ← step s; e.followM next) := by
  rw [PIR.runM_bind, stepLaw]
  have hn : (fun a => (k a).runM h) = next := funext fun a => funext (nextLaw a)
  rw [hn]

/-- No determinism restriction: every probabilistic stopped record, including
    its residual state and events, survives any existing Process continuation. -/
theorem stopped_distribution {A B : Type} (p : PIR.Process I A) (k : A → PIR.Process I B)
    (h : PIR.MonadHandler ProbComp I S E) (s : S)
    (distribution : ProbComp (PIR.Stop × S × List E))
    (localStop : p.runM h s = (do
      let (why, t, events) ← distribution
      pure ⟨.stopped why, t, events⟩)) :
    (p.bind k).runM h s = (do
      let (why, t, events) ← distribution
      pure ⟨.stopped why, t, events⟩) := by
  rw [PIR.runM_bind, localStop]
  simp [PIR.Execution.followM]

/-- Trusted work may emit events or stop before returning its determined value.
The continuation consumes that value only on successful completion. -/
theorem runM_bind_determined (h : PIR.MonadHandler ProbComp I S E)
    (p : PIR.Process I A) (work : Phase S E Unit) (value : A)
    (stepLaw : ∀ s, p.runM h s = mapPhase (fun _ => value) work s)
    (next : A → PIR.Process I B) (s : S) :
    (p.bind next).runM h s = (do
      let e ← work s
      e.followM fun _ s => (next value).runM h s) := by
  rw [runM_bind_transport h p next _ _ stepLaw (fun _ _ => rfl), follow_mapPhase]

/-- A handler-independent Process equation discharges the local runM value law,
including checker work that stops or records observations. -/
theorem runM_determined_of_proc (h : PIR.MonadHandler ProbComp I S E)
    (p : PIR.Process I A) (work : PIR.Process I Unit) (value : A)
    (equation : p = work.bind (fun _ => .done value)) (s : S) :
    p.runM h s = (do
      let e ← work.runM h s
      e.followM fun _ s => pure (result value s)) := by
  rw [equation, PIR.runM_bind]
  rfl

noncomputable def mass (game : ProbComp Prop) : ENNReal := 𝒟[game] {True}

theorem mass_bind_mono {A : Type} (m : ProbComp A) (f g : A → ProbComp Prop)
    (h : ∀ a, mass (f a) ≤ mass (g a)) : mass (m >>= f) ≤ mass (m >>= g) := by
  exact OracleComp.evalDist_bind_apply_mono_of_support m f g (MeasurableSet.singleton True)
    (fun a _ => h a)

@[simp] theorem mass_false : mass (pure False) = 0 := by
  simp [mass]

/-- Equality of the complete output distributions with all sets observable.
For Execution outputs this includes outcome, private state and ordered events. -/
def SameDist {A : Type} (left right : ProbComp A) : Prop :=
  letI : MeasurableSpace A := ⊤
  𝒟[left] = 𝒟[right]

theorem SameDist.refl {A : Type} (p : ProbComp A) : SameDist p p := rfl

theorem SameDist.symm {A : Type} {p q : ProbComp A} (same : SameDist p q) :
    SameDist q p := Eq.symm same

theorem SameDist.trans {A : Type} {p q r : ProbComp A}
    (left : SameDist p q) (right : SameDist q r) : SameDist p r := Eq.trans left right

/-- Specific to the pinned uniform oracle: every structurally reachable output
has positive singleton mass. This is not asserted for arbitrary oracle measures. -/
theorem SameDist.support_eq {A : Type} {p q : ProbComp A} (same : SameDist p q) :
    support p = support q := by
  let : MeasurableSpace A := ⊤
  ext a
  rw [mem_support_iff_evalDist_singleton_pos, mem_support_iff_evalDist_singleton_pos]
  rw [show 𝒟[p] = 𝒟[q] from same]

/-- Full local distributions can be substituted before any measured continuation. -/
theorem SameDist.bind_left {A B : Type} [MeasurableSpace B]
    {left right : ProbComp A} (same : SameDist left right) (next : A → ProbComp B) :
    𝒟[left >>= next] = 𝒟[right >>= next] := by
  let : MeasurableSpace A := ⊤
  rw [evalDist_bind_of_discrete, evalDist_bind_of_discrete]
  exact congrArg (fun μ => μ.bind (fun a => 𝒟[next a])) same

/-- Reachability only asks about returned values. Stopped records are preserved
by followM without entering the replaced operation. -/
def Reaches {S E A : Type} (prior : ProbComp (PIR.Execution S E A))
    (invariant : A → S → Prop) : Prop :=
  ∀ e ∈ support prior, ∀ a, e.outcome = .returned a → invariant a e.state

theorem SameDist.reaches_iff {S E A : Type}
    {left right : ProbComp (PIR.Execution S E A)} (same : SameDist left right)
    (invariant : A → S → Prop) : Reaches left invariant ↔ Reaches right invariant := by
  unfold Reaches
  rw [same.support_eq]

/-- Replace a whole remaining suffix using only laws at returned reachable
states. Every stopped prefix and the ordered event concatenation are retained. -/
theorem follow_congr_of_reaches {S E A B : Type}
    (prior : ProbComp (PIR.Execution S E A)) (invariant : A → S → Prop)
    (left right : A → Phase S E B) (reachable : Reaches prior invariant)
    (localLaw : ∀ a s, invariant a s → SameDist (left a s) (right a s)) :
    SameDist (prior >>= fun e => e.followM left) (prior >>= fun e => e.followM right) := by
  let : MeasurableSpace (PIR.Execution S E B) := ⊤
  apply OracleComp.evalDist_bind_congr_of_support
  intro e he
  cases out : e.outcome with
  | stopped why => simp only [PIR.Execution.followM, out]
  | returned a =>
    simp only [PIR.Execution.followM, out]
    exact (localLaw a e.state (reachable e he a out)).bind_left _

/-- Prefix and suffix replacement compose; support transfer supplies the
invariant for the second prefix. This is the induction step for finite hybrids. -/
theorem SameDist.follow_congr {S E A B : Type}
    {prior other : ProbComp (PIR.Execution S E A)} (same : SameDist prior other)
    (invariant : A → S → Prop) (left right : A → Phase S E B)
    (reachable : Reaches prior invariant)
    (localLaw : ∀ a s, invariant a s → SameDist (left a s) (right a s)) :
    SameDist (prior >>= fun e => e.followM left) (other >>= fun e => e.followM right) := by
  let : MeasurableSpace (PIR.Execution S E B) := ⊤
  exact (same.bind_left (fun e => e.followM left)).trans
    (follow_congr_of_reaches other invariant left right
      ((same.reaches_iff invariant).mp reachable) localLaw)

/-- Per-operation distribution laws lift through every value-adaptive process.
The complete outcome, residual state and ordered events are preserved. Internal
oracle queries of a handler are not counted by this observation. -/
theorem runM_sameDist (left right : PIR.MonadHandler ProbComp I S E)
    (localLaw : ∀ action state, SameDist (left action state) (right action state))
    (process : PIR.Process I A) (state : S) :
    SameDist (process.runM left state) (process.runM right state) := by
  induction process generalizing state with
  | done value => exact SameDist.refl _
  | halt why => exact SameDist.refl _
  | call action continuation ih =>
    change SameDist
      (left action state >>= fun e => e.followM (fun reply s => (continuation reply).runM left s))
      (right action state >>= fun e => e.followM (fun reply s => (continuation reply).runM right s))
    exact SameDist.follow_congr (localLaw action state) (fun _ _ => True) _ _
      (by intro e he value returned; trivial)
      (fun reply s _ => ih reply s)

/-- Prefix-local replacement of a phase through a full state/event continuation.
No law is required on stopped branches or states outside the prefix support. -/
theorem replace_after_prefix {S E A B C : Type} [MeasurableSpace C]
    (prior : ProbComp (PIR.Execution S E A)) (invariant : A → S → Prop)
    (left right : A → Phase S E B)
    (next : A → PIR.Execution S E B → ProbComp C)
    (onStop : PIR.Stop → S → List E → ProbComp C)
    (reachable : Reaches prior invariant)
    (localLaw : ∀ a s, invariant a s → SameDist (left a s) (right a s)) :
    𝒟[prior >>= fun e => match e.outcome with
      | .stopped why => onStop why e.state e.events
      | .returned a => left a e.state >>= fun q =>
          next a ⟨q.outcome, q.state, e.events ++ q.events⟩] =
    𝒟[prior >>= fun e => match e.outcome with
      | .stopped why => onStop why e.state e.events
      | .returned a => right a e.state >>= fun q =>
          next a ⟨q.outcome, q.state, e.events ++ q.events⟩] := by
  apply OracleComp.evalDist_bind_congr_of_support
  intro e he
  cases out : e.outcome with
  | stopped why => rfl
  | returned a =>
    exact (localLaw a e.state (reachable e he a out)).bind_left _

/-- The useful full-execution instance retains both prefixes and suffix events. -/
theorem replace_follow_prefix {S E A B C : Type}
    (prior : ProbComp (PIR.Execution S E A)) (invariant : A → S → Prop)
    (left right : A → Phase S E B) (next : A → B → Phase S E C)
    (reachable : Reaches prior invariant)
    (localLaw : ∀ a s, invariant a s → SameDist (left a s) (right a s)) :
    SameDist
      (prior >>= fun e => e.followM (fun a s => left a s >>= fun q => q.followM (next a)))
      (prior >>= fun e => e.followM (fun a s => right a s >>= fun q => q.followM (next a))) := by
  let : MeasurableSpace (PIR.Execution S E C) := ⊤
  apply follow_congr_of_reaches prior invariant _ _ reachable
  intro a s hs
  exact (localLaw a s hs).bind_left _

/-- A local preservation proof propagates reachability through a prefix extension. -/
theorem reaches_follow {S E A B : Type}
    (prior : ProbComp (PIR.Execution S E A)) (next : A → Phase S E B)
    (invariant : A → S → Prop) (after : B → S → Prop)
    (reachable : Reaches prior invariant)
    (preserves : ∀ a s, invariant a s → Reaches (next a s) after) :
    Reaches (prior >>= fun e => e.followM next) after := by
  intro e he b out
  obtain ⟨p, hp, he⟩ := MonadAttach.mem_support_bind.mp he
  cases pout : p.outcome with
  | stopped why =>
    simp only [PIR.Execution.followM, pout, support_pure, Set.mem_singleton_iff] at he
    subst e
    cases out
  | returned a =>
    simp only [PIR.Execution.followM, pout] at he
    obtain ⟨q, hq, he⟩ := MonadAttach.mem_support_bind.mp he
    simp only [support_pure, Set.mem_singleton_iff] at he
    subst e
    exact preserves a p.state (reachable p hp a pout) q hq b out


/-- Stops are nonaccepting; returned values are observed without normalization. -/
def returnedSatisfies {S E A : Type} (predicate : A → Prop) (e : PIR.Execution S E A) : Prop :=
  match e.outcome with
  | .stopped _ => False
  | .returned a => predicate a

def acceptance (h : PIR.MonadHandler ProbComp I S E) (p : PIR.Process I A)
    (s : S) (predicate : A → Prop) : ProbComp Prop := do
  let e ← p.runM h s
  pure (returnedSatisfies predicate e)

def attachWork (p : PIR.Process I A) (work : A → PIR.Process I Unit) : PIR.Process I A :=
  p.bind fun a => (work a).bind fun _ => .done a

def checked (h : PIR.MonadHandler ProbComp I S E) (p : PIR.Process I A)
    (checker : A → PIR.Process I Bool) (s : S) : ProbComp Prop := do
  let e ← (p.bind checker).runM h s
  pure (e.outcome = .returned true)

/-- A local checker equation composes through any prefix, preserving stopping
work and all observations. No equality of complete games is a premise. -/
theorem checked_eq (h : PIR.MonadHandler ProbComp I S E) (p : PIR.Process I A)
    (work : A → PIR.Process I Unit) (checker : A → PIR.Process I Bool)
    (value : A → Bool) (s : S)
    (checkLaw : ∀ a s, (checker a).runM h s = (do
      let e ← (work a).runM h s
      e.followM fun _ s => pure (result (value a) s))) :
    checked h p checker s = acceptance h (attachWork p work) s (fun a => value a = true) := by
  simp only [checked, acceptance, attachWork, PIR.runM_bind, bind_assoc]
  apply bind_congr
  intro e
  cases e with | mk out s events =>
    cases out with
    | stopped why => simp [PIR.Execution.followM, returnedSatisfies]
    | returned a =>
      simp only [PIR.Execution.followM, bind_assoc, pure_bind, checkLaw, runM_bind_function]
      apply bind_congr
      intro checked
      cases checked with | mk out s es =>
        cases out <;> simp [PIR.Process.runM, result, returnedSatisfies]

theorem acceptance_mono (h : PIR.MonadHandler ProbComp I S E)
    (p : PIR.Process I A) (s : S) (left right : A → Prop)
    (implies : ∀ a, left a → right a) :
    mass (acceptance h p s left) ≤ mass (acceptance h p s right) := by
  apply OracleComp.prEvent_mono_of_support
  intro e _
  cases e with | mk out state events =>
    cases out with
    | stopped why => simp [returnedSatisfies]
    | returned a => exact implies a

/-- Conservative trusted checkers need acceptance implication, not equality. -/
theorem checked_le (h : PIR.MonadHandler ProbComp I S E) (p : PIR.Process I A)
    (work : A → PIR.Process I Unit) (checker : A → PIR.Process I Bool)
    (value : A → Bool) (s : S)
    (checkLaw : ∀ a s, (checker a).runM h s = (do
      let e ← (work a).runM h s
      e.followM fun _ s => pure (result (value a) s)))
    (predicate : A → Prop) (mathematics : ∀ a, value a = true → predicate a) :
    mass (checked h p checker s) ≤ mass (acceptance h (attachWork p work) s predicate) := by
  rw [checked_eq h p work checker value s checkLaw]
  exact acceptance_mono h _ s _ predicate mathematics

/-- Process-level checker equations are sufficient for the local execution law. -/
theorem checked_le_of_proc (h : PIR.MonadHandler ProbComp I S E) (p : PIR.Process I A)
    (work : A → PIR.Process I Unit) (checker : A → PIR.Process I Bool)
    (value : A → Bool) (s : S)
    (checkLaw : ∀ a, checker a = (work a).bind (fun _ => .done (value a)))
    (predicate : A → Prop) (mathematics : ∀ a, value a = true → predicate a) :
    mass (checked h p checker s) ≤ mass (acceptance h (attachWork p work) s predicate) :=
  checked_le h p work checker value s
    (fun a s => runM_determined_of_proc h _ _ _ (checkLaw a) s) predicate mathematics

end ZkcSecurity.VCVio.Execution
