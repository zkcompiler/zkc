import Zkc.Semantics.Boundary

set_option autoImplicit false
namespace PIR.Continuation
variable {I : Signature} {A B S E Key : Type}

/-- This value is supplied by a verifier interpretation, not inferred from
    Proc.done or from a successful host-language call. -/
inductive Terminal (A : Type) where
  | accepted : A → Terminal A
  | rejected
  deriving DecidableEq, Repr

def after (p : Proc I (Terminal A)) (arm : A → Proc I B) : Proc I B :=
  p.bind (fun | .accepted a => arm a | .rejected => .halt .reject)

theorem rejected_no_arm (p : Proc I (Terminal A)) (arm : A → Proc I B)
    (h : Handler I S E) (s : S) (no : (p.run h s).outcome = .returned .rejected) :
    (after p arm).run h s = ⟨.stopped .reject,(p.run h s).state,(p.run h s).events⟩ := by
  simp [after,run_bind,Execution.follow,no,Proc.run]

theorem stopped_no_arm (p : Proc I (Terminal A)) (arm : A → Proc I B)
    (h : Handler I S E) (s : S) (why : Stop)
    (no : (p.run h s).outcome = .stopped why) :
    (after p arm).run h s = ⟨.stopped why,(p.run h s).state,(p.run h s).events⟩ := by
  simp [after,run_bind,Execution.follow,no]

theorem accepted_retains_prefix (p : Proc I (Terminal A)) (arm : A → Proc I B)
    (h : Handler I S E) (s : S) (a : A)
    (yes : (p.run h s).outcome = .returned (.accepted a)) :
    (after p arm).run h s =
      ⟨((arm a).run h (p.run h s).state).outcome,
       ((arm a).run h (p.run h s).state).state,
       (p.run h s).events ++ ((arm a).run h (p.run h s).state).events⟩ := by
  simp [after,run_bind,Execution.follow,yes]

/-- Acceptance alone does not erase the continuation's interaction obligations. -/
theorem formed (P : Interaction I) (p : Proc I (Terminal A)) (arm : A → Proc I B)
    (post : Terminal A → P.Phase → Prop) (phase : P.Phase)
    (hp : Conforms P p phase) (exits : Boundary.Returns P post p phase)
    (ha : ∀ a phase, post (.accepted a) phase → Conforms P (arm a) phase) :
    Conforms P (after p arm) phase := by
  apply Boundary.conforms_bind P p _ post phase hp exits
  intro result phase valid
  cases result with
  | accepted a => exact ha a phase valid
  | rejected => trivial

/-- A single outstanding, already-authorized handoff. Key stands for the exact
    source run/site, capture binding, consumer and target occurrence. It is not
    a digest-based authorization scheme or an issuance theorem. -/
def take [DecidableEq Key] (expected : Key) :
    Option (Key × A) → Execution (Option (Key × A)) Unit A
  | none => ⟨.stopped .refused,none,[]⟩
  | some (key,a) => if key = expected then ⟨.returned a,none,[]⟩
      else ⟨.stopped .refused,some (key,a),[]⟩

theorem wrong_target [DecidableEq Key] (key expected : Key) (a : A)
    (different : key ≠ expected) :
    take expected (some (key,a)) = ⟨.stopped .refused,some (key,a),[]⟩ := by
  simp [take,different]

theorem replay_refused [DecidableEq Key] (key : Key) (a : A) :
    take key (take key (some (key,a))).state =
      (⟨.stopped .refused,none,[]⟩ : Execution (Option (Key × A)) Unit A) := by
  simp [take]

/-- Consumption occurs before the continuation; its terminal failure cannot
    refund the ticket. This theorem fixes the selected atomic arm policy. -/
theorem failing_arm_consumes [DecidableEq Key] (key : Key) (a : A) (why : Stop) :
    (take key (some (key,a))).follow
      (fun _ state => (⟨.stopped why,state,[]⟩ : Execution (Option (Key × A)) Unit B)) =
      ⟨.stopped why,none,[]⟩ := by
  simp [take,Execution.follow]

end PIR.Continuation
