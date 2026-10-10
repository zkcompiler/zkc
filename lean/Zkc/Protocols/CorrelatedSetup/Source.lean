import Zkc.Source.Expressions
import Zkc.Protocols.CorrelatedSetup.ServiceCache

set_option autoImplicit false

namespace Zkc.Protocols.CorrelatedSetup.Source
open Zkc.Source.Expressions
open Zkc.Protocols.CorrelatedSetup Zkc.Probability.AdaptiveTape Zkc.Protocols.CorrelatedSetup.Service
variable {F : Type} [CommRing F] [DecidableEq F]

/-- Slot meanings are the explicit model binding, not inferred from a label.
    0..2: publication, 3: history length, 4: last visible U, 5: verifier Delta.
    6: prover witness, 7: prover cache, 8+: unavailable current-response input. -/
def lastU (h : History F) : F := match h.events.getLast? with
  | some (.response _ u _ _) => u
  | _ => 0

def inputs (s : Setup F) (w : Witness F) (p : Triple F) (h : History F) : Nat → F
  | 0 => p.1
  | 1 => p.2.1
  | 2 => p.2.2
  | 3 => h.events.length
  | 4 => lastU h
  | 5 => s.delta
  | 6 => w.x
  | 7 => (byPrefix s w p).1
  | _ => 0

def controllerScope : List Nat := [0,1,2,3,4,5]

omit [DecidableEq F] in
theorem inputs_agree (s : Setup F) (w v : Witness F) (p : Triple F) (h : History F) :
    ∀ a ∈ controllerScope, inputs s w p h a = inputs s v p h a := by
  intro a ha
  simp [controllerScope] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

structure Program where
  stop : Expr Nat
  star : Expr Nat
  challenge : Expr Nat
  cut : Expr Nat
  deriving DecidableEq, Repr

def Program.Good (c : Program) : Prop :=
  check controllerScope c.stop = true ∧ check controllerScope c.star = true ∧
    check controllerScope c.challenge = true ∧ check controllerScope c.cut = true

instance (c : Program) : Decidable c.Good := inferInstanceAs (Decidable (_ ∧ _))

def Program.denote (c : Program) (s : Setup F) (w : Witness F) : Controller F :=
  fun p h =>
    let env := inputs s w p h
    if c.stop.eval env = 0 then none else
      some ⟨c.star.eval env,c.challenge.eval env,decide (c.cut.eval env ≠ 0)⟩

/-- A checked FIXED program elaborates to the same complete controller for
    both witnesses, discharging Zkc.Probability.AdaptiveTape's premise in this source fragment. -/
theorem same_controller (c : Program) (good : c.Good) (s : Setup F) (w v : Witness F) :
    c.denote s w = c.denote s v := by
  funext p h
  have h0 := checked_agreement _ c.stop _ _ good.1 (inputs_agree s w v p h)
  have h1 := checked_agreement _ c.star _ _ good.2.1 (inputs_agree s w v p h)
  have h2 := checked_agreement _ c.challenge _ _ good.2.2.1 (inputs_agree s w v p h)
  have h3 := checked_agreement _ c.cut _ _ good.2.2.2 (inputs_agree s w v p h)
  simp only [Program.denote,h0,h1,h2,h3]

theorem source_witness_mass [Fintype F] (c : Program) (good : c.Good)
    (s : Setup F) (w v : Witness F) (n : Nat) (out : Triple F × History F) :
    (Fintype.card {r : Triple F × Tape F n // compiled s w (c.denote s w) n r = out} : ℚ) /
      Fintype.card (Triple F × Tape F n) =
    (Fintype.card {r : Triple F × Tape F n // compiled s v (c.denote s v) n r = out} : ℚ) /
      Fintype.card (Triple F × Tape F n) := by
  simp only [compiled_correct,same_controller c good s w v]
  exact witness_mass s w v _ n out

/-- Prover-local producer syntax is distinct from the verifier's input map.
    Here slots 0,1 are x,y and 2,3,4 are authenticated mx,my,mz. -/
def coefficient0 : Expr Nat := .mul (.var 2) (.var 3)
def coefficient1 : Expr Nat := .sub
  (.add (.mul (.var 0) (.var 3)) (.mul (.var 1) (.var 2))) (.var 4)

def coefficientInputs (w : Witness F) (m : Triple F) : Nat → F
  | 0 => w.x
  | 1 => w.y
  | 2 => m.1
  | 3 => m.2.1
  | 4 => m.2.2
  | _ => 0

theorem coefficient_source (w : Witness F) (m : Triple F) :
    (coefficient0.eval (coefficientInputs w m),coefficient1.eval (coefficientInputs w m)) =
      coefficients w m := by rfl

def sourceCache (s : Setup F) (w : Witness F) (p : Triple F) : CoefficientCache s w p where
  value := (coefficient0.eval (coefficientInputs w (tags s (publicationsOf w p))),
    coefficient1.eval (coefficientInputs w (tags s (publicationsOf w p))))
  valid := coefficient_source w _

theorem source_cache_run (s : Setup F) (w : Witness F) (c : Controller F)
    (p : Triple F) (n : Nat) (h : History F) (r : Tape F n) :
    run (cachedStep s w c p (sourceCache s w p).value) n h r =
      run (realStep s w c p) n h r :=
  cached_continuation_correct s w c p (sourceCache s w p) n h r

def sourceCompiled (c : Program) (s : Setup F) (w : Witness F) (n : Nat)
    (r : Triple F × Tape F n) : Triple F × History F :=
  let p := publicationsOf w r.1
  let cache := sourceCache s w p
  (p,run (cachedStep s w (c.denote s w) p cache.value) n empty r.2)

theorem source_compiled_correct (c : Program) (s : Setup F) (w : Witness F)
    (n : Nat) (r : Triple F × Tape F n) :
    sourceCompiled c s w n r = compiled s w (c.denote s w) n r := by
  rw [compiled_correct]
  apply Prod.ext
  · rfl
  · exact source_cache_run s w (c.denote s w) _ n empty r.2

theorem source_compiled_witness_mass [Fintype F] (c : Program) (good : c.Good)
    (s : Setup F) (w v : Witness F) (n : Nat) (out : Triple F × History F) :
    (Fintype.card {r : Triple F × Tape F n // sourceCompiled c s w n r = out} : ℚ) /
      Fintype.card (Triple F × Tape F n) =
    (Fintype.card {r : Triple F × Tape F n // sourceCompiled c s v n r = out} : ℚ) /
      Fintype.card (Triple F × Tape F n) := by
  simp only [source_compiled_correct]
  exact source_witness_mass c good s w v n out

/-- Adaptive requests can depend on retained U and choose stop/cut via guards.
    This example uses only a projection of history, not all Zkc.Probability.AdaptiveTape controllers. -/
def adaptive : Program :=
  ⟨.ifz (.sub (.var 3) (.lit 2)) (.lit 0) (.lit 1),
    .add (.lit 2) (.var 4),.add (.var 0) (.var 3),.var 4⟩

theorem adaptive_checked : adaptive.Good := by decide

def hiddenCapture : Closure Nat :=
  ⟨1,.var ⟨0,by decide⟩,fun _ => .var 6⟩

theorem hidden_capture_rejected : check controllerScope hiddenCapture.expand = false := by decide
theorem implicit_flow_rejected :
    check controllerScope (.ifz (.var 6) (.lit 0) (.lit 1)) = false := by decide
theorem future_rejected : check controllerScope (.var 8) = false := by decide

/-- Conservative dependency analysis deliberately rejects cancellation. -/
theorem cancellation_rejected : check controllerScope (.sub (.var 6) (.var 6)) = false := by decide
theorem cancellation_constant (env : Nat → F) :
    (Expr.sub (.var 6) (.var 6)).eval env = 0 := by simp [Expr.eval]

/-- Both individually accepted; selecting code from a secret is outside the
    fixed-code theorem. This controls staging, not just variable capture. -/
def specialized (n : Nat) : Program := ⟨.lit 1,.lit 2,.lit n,.lit 0⟩
theorem specialized_checked (n : Nat) : (specialized n).Good := by simp [specialized,Program.Good,check,Expr.deps]
theorem private_codegen_changes_request :
    (specialized 1).denote testSetup witnessOne commonPrefix empty ≠
      (specialized 2).denote testSetup witnessTwo commonPrefix empty := by decide

theorem misbound_public_slot_changes_value :
    (Expr.var (0 : Nat)).eval (fun _ => (1 : ZMod 7)) ≠
      (Expr.var (0 : Nat)).eval (fun _ => (2 : ZMod 7)) := by decide

end Zkc.Protocols.CorrelatedSetup.Source
