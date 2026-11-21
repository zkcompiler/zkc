module

public import Zkc.Core.Process.Same
public import Zkc.Core.Meaning.Fold

@[expose] public section
set_option autoImplicit false

namespace Zkc.Core
variable {S : Sig} {H A B L : Type}

/-- How a property combines the possible continuations at one effect. -/
structure ProcessJudgment (S : Sig) (L : Type) where
  node : (op : S.Op) → (S.Reply op → L) → L

def Process.interpret (j : ProcessJudgment S L) (done : A → L) (halt : H → L) : Process S H A → L
  | .done a => done a
  | .halt h => halt h
  | .call op k => j.node op fun v => (k v).interpret j done halt

theorem Process.interpret_bind (j : ProcessJudgment S L) (done : B → L) (halt : H → L)
    (k : A → Process S H B) (p : Process S H A) :
    (p.bind k).interpret j done halt = p.interpret j (fun a => (k a).interpret j done halt) halt := by
  induction p with
  | done | halt => rfl
  | call op next ih =>
    exact congrArg (j.node op) (funext ih)

/-- Predicate judgments support weakening when each effect respects implication. -/
def ProcessJudgment.Monotone {T : Type} (j : ProcessJudgment S (T → Prop)) : Prop :=
  ∀ op (p q : S.Reply op → T → Prop), (∀ v t, p v t → q v t) → ∀ t, j.node op p t → j.node op q t

theorem Process.interpret_mono {T : Type} {j : ProcessJudgment S (T → Prop)} (mono : j.Monotone)
    {p q : A → T → Prop} {h k : H → T → Prop} (done : ∀ a t, p a t → q a t)
    (halt : ∀ e t, h e t → k e t) (program : Process S H A) :
    ∀ t, program.interpret j p h t → program.interpret j q k t := by
  induction program with
  | done a => exact done a
  | halt e => exact halt e
  | call op next ih => exact mono op _ _ ih

/-- A proof of the indexed body extends to any number of iterations and any initial
position within the stated limit. The judgment determines what the invariant carries. -/
theorem Process.interpret_iterate {T : Type} {j : ProcessJudgment S (T → Prop)} (mono : j.Monotone)
    (step : Nat → A → Process S H A) (inv : Nat → A → T → Prop) (halt : H → T → Prop) (limit : Nat)
    (body : ∀ i a t, i < limit → inv i a t → (step i a).interpret j (inv (i+1)) halt t)
    (count start : Nat) (a : A) (state : T) (within : start + count ≤ limit) (initial : inv start a state) :
    (Process.iterate count step start a).interpret j (inv (start+count)) halt state := by
  induction count generalizing start a state with
  | zero => exact initial
  | succ n ih =>
    rw [Process.iterate, Process.interpret_bind]
    apply Process.interpret_mono mono (fun a' t h => ?_) (fun _ _ h => h) _ state
      (body start a state (by omega) initial)
    have tail := ih (start+1) a' t (by omega) h
    simpa only [Nat.add_right_comm start 1 n, Nat.add_succ, Nat.add_zero] using tail

/-- Every instruction composes with its continuation in exactly the same way for traces,
all-path properties, resources and stateful observations. -/
theorem Term.interpret_step {D : Dialect} (sem : Semantics D) {Γ : Ctx D.Ty} {outs mid : List D.Ty}
    (key : Key) (i : Instr D Γ mid) (ns : Names mid) (rest : Term D (Γ.extend ns) outs)
    (path : List Frame) (env : Env sem.Val Γ) (j : ProcessJudgment sem.S L) (done : HList sem.Val outs → L)
    (halt : sem.H → L) :
    ((Term.step key i ns rest).denote sem path env).interpret j done halt =
      (i.denote sem key path env).interpret j (fun vs => (rest.denote sem path (env.extend ns vs)).interpret j done halt) halt := by
  rw [Term.denote_step, Process.interpret_bind]

/-- **The rule of a loop**, for every dialect and every judgment: a step that is a loop is judged
as the iteration of its body from the initial carried values and nothing collected, followed by
the rest on what the iteration returns. With `Process.interpret_iterate` the body is judged once,
at a symbolic iteration number, under an invariant. -/
theorem Term.interpret_loop {D : Dialect} (sem : Semantics D) {Γ : Ctx D.Ty}
    {outs carried each : List D.Ty} (key : Key) (w : D.Who) (times : Times D w Γ)
    (gives : ∀ a, a ∈ carried ++ each → D.Gives w a) (initial : HList (Var Γ) carried)
    (inputs : Names (D.index w :: carried)) (body : Term D (Γ.extend inputs) (carried ++ each))
    (results : Names (carried ++ each.map (D.collected times.size)))
    (rest : Term D (Γ.extend results) outs) (path : List Frame) (env : Env sem.Val Γ)
    (j : ProcessJudgment sem.S L) (done : HList sem.Val outs → L) (halt : sem.H → L) :
    ((Term.step key (.loop w times gives initial inputs body) results rest).denote sem path
        env).interpret j done halt =
      (Process.iterate (sem.times times env)
          (sem.loopStep w inputs (fun path' env' => body.denote sem path' env') key path env)
          0 (env.all initial, HList.empties each)).interpret j
        (fun state => (rest.denote sem path (env.extend results
          (state.1.append (sem.collected times.size state.2)))).interpret j done halt) halt :=
  (Term.interpret_step sem key _ results rest path env j done halt).trans
    (Process.interpret_bind j _ halt _ _)

/-- **One iteration of a loop**: the body at the frame of the iteration, with the iteration
number and the carried values bound to its inputs, then what the iteration hands on. -/
theorem Semantics.interpret_loopStep {D : Dialect} (sem : Semantics D) {Γ : Ctx D.Ty}
    {carried each : List D.Ty} (w : D.Who) (inputs : Names (D.index w :: carried))
    (run : List Frame → Env sem.Val (Γ.extend inputs) →
      Process sem.S sem.H (HList sem.Val (carried ++ each)))
    (key : Key) (path : List Frame) (env : Env sem.Val Γ) (i : Nat)
    (state : sem.LoopState carried each) (j : ProcessJudgment sem.S L)
    (done : sem.LoopState carried each → L) (halt : sem.H → L) :
    (sem.loopStep w inputs run key path env i state).interpret j done halt =
      (run (path ++ [.iteration key i]) (env.extend inputs
          (.cons (sem.index w i) state.1))).interpret j
        (fun out => done ((HList.split carried out).1, state.2.push (HList.split carried out).2))
        halt :=
  Process.interpret_bind j _ halt _ _

/-- The judgment of a process without effects: there is no effect to judge, and the process is
judged by how it ends. The judgment of a function's process, which makes the walk of a role's
program the walk of a function's. -/
def ProcessJudgment.silent : ProcessJudgment NoSig (Unit → Prop) where
  node op _ _ := nomatch op

theorem ProcessJudgment.silent_monotone : ProcessJudgment.silent.Monotone := fun op => nomatch op

def ProcessJudgment.every (allowed : ∀ op, S.Reply op → Prop) : ProcessJudgment S Prop where
  node op next := ∀ v, allowed op v → next v

theorem Process.every_iff_interpret (allowed : ∀ op, S.Reply op → Prop) (p : Process S H A)
    (done : A → Prop) (halt : H → Prop) :
    p.Every allowed done halt ↔ p.interpret (.every allowed) done halt := by
  induction p with
  | done | halt => rfl
  | call op k ih =>
    change (∀ v, allowed op v → _) ↔ ∀ v, allowed op v → _
    exact ⟨fun h v ok => (ih v).mp (h v ok), fun h v ok => (ih v).mpr (h v ok)⟩

def ProcessJudgment.possible (allowed : ∀ op, S.Reply op → Prop) : ProcessJudgment S Prop where
  node op next := ∃ v, allowed op v ∧ next v

theorem Process.canReturn_iff_interpret (allowed : ∀ op, S.Reply op → Prop) (p : Process S H A) (a : A) :
    p.CanReturn allowed a ↔ p.interpret (.possible allowed) (· = a) (fun _ => False) := by
  induction p with
  | done x => constructor <;> rintro h <;> cases h <;> constructor
  | halt h => constructor <;> intro h <;> cases h
  | call op k ih =>
    constructor
    · intro h
      cases h with | call _ v ok tail => exact ⟨v, ok, (ih v).mp tail⟩
    · rintro ⟨v, ok, tail⟩
      exact .call op v ok ((ih v).mpr tail)

abbrev EffectTrace (S : Sig) := List ((op : S.Op) × S.Reply op)

/-- Match both the operation (including its payload) and its dependent reply. -/
def ProcessJudgment.trace (S : Sig) : ProcessJudgment S (EffectTrace S → Prop) where
  node op next trace := ∃ v tail, trace = ⟨op, v⟩ :: tail ∧ next v tail

end Zkc.Core
