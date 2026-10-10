import Zkc.Probability.AdaptiveTape
import Zkc.Protocols.CorrelatedSetup.Composition


set_option autoImplicit false
namespace Zkc.Protocols.CorrelatedSetup.Service
open Zkc.Probability.AdaptiveTape
open Zkc.Protocols.CorrelatedSetup
variable {F : Type} [CommRing F]

structure Request (F : Type) where
  star : F
  challenge : F
  cutAfterU : Bool
  deriving DecidableEq

inductive Event (F : Type) where
  | response (request : Request F) (u : F) (v tag : Option F)
  | stopped
  deriving DecidableEq

structure History (F : Type) where
  events : List (Event F)
  halted : Bool
  deriving DecidableEq

def empty : History F := ⟨[],false⟩
abbrev Controller (F : Type) := Triple F → History F → Option (Request F)

def appendResponse (h : History F) (req : Request F) (uv : F × F) (tag : F) : History F :=
  ⟨h.events ++ [.response req uv.1 (if req.cutAfterU then none else some uv.2)
      (if req.cutAfterU then none else some tag)],false⟩

def advance (controller : Controller F) (p : Triple F)
    (response : Request F → F → F × F) (tag : F) (h : History F) (r : F) : History F :=
  if h.halted then h else match controller p h with
  | none => ⟨h.events ++ [.stopped],true⟩
  | some req => appendResponse h req (response req r) tag

def actualResponse (s : Setup F) (a : F × F) (req : Request F) (r : F) : F × F :=
  localResponse a (req.star-s.delta*r,r) req.challenge

def simulatedResponse (s : Setup F) (p : Triple F) (req : Request F) (v : F) : F × F :=
  (req.challenge*gate s p+req.star-v*s.delta,v)

def realStep (s : Setup F) (w : Witness F) (controller : Controller F) (p : Triple F) :=
  advance controller p (actualResponse s (byPrefix s w p))
    (tags s (publicationsOf w p)).2.2

def simStep (s : Setup F) (controller : Controller F) (p : Triple F) :=
  advance controller p (simulatedResponse s p) ((keys s p).2.2-s.delta)

def addEquiv (a : F) : F ≃ F where
  toFun r := r+a
  invFun r := r-a
  left_inv r := by simp
  right_inv r := by simp

def change (s : Setup F) (w : Witness F) (controller : Controller F)
    (p : Triple F) (h : History F) : F ≃ F :=
  if h.halted then Equiv.refl F else match controller p h with
  | none => Equiv.refl F
  | some req => addEquiv (req.challenge*(byPrefix s w p).2)

theorem response_coupling (s : Setup F) (w : Witness F) (p : Triple F)
    (req : Request F) (r : F) :
    actualResponse s (byPrefix s w p) req r =
      simulatedResponse s p req (r+req.challenge*(byPrefix s w p).2) :=
  response_reconstruct s w p req.challenge req.star r

theorem step_coupling (s : Setup F) (w : Witness F) (controller : Controller F)
    (p : Triple F) (h : History F) (r : F) :
    realStep s w controller p h r =
      simStep s controller p h (change s w controller p h r) := by
  by_cases halted : h.halted = true
  · simp [realStep,simStep,advance,halted]
  · cases hc : controller p h with
    | none => simp [realStep,simStep,advance,halted,hc]
    | some req =>
      simp [realStep,simStep,advance,halted,hc,change,addEquiv,response_coupling,output_identity]

/-- Conditioned on a common publication, repeated fresh VOPE responses. -/
theorem continuation_coupling (s : Setup F) (w : Witness F) (controller : Controller F)
    (p : Triple F) (n : Nat) (h : History F) (r : Tape F n) :
    run (realStep s w controller p) n h r =
      run (simStep s controller p) n h
        (coins (simStep s controller p) (change s w controller p) n h r) :=
  adaptive_coupling _ _ _ (step_coupling s w controller p) n h r

def wholeCoins (s : Setup F) (w : Witness F) (controller : Controller F) (n : Nat) :
    Triple F × Tape F n ≃ Triple F × Tape F n :=
  skew (prefixEquiv w) (fun p => coins (simStep s controller p) (change s w controller p) n empty)

def real (s : Setup F) (w : Witness F) (controller : Controller F) (n : Nat)
    (r : Triple F × Tape F n) : Triple F × History F :=
  let p := publicationsOf w r.1
  (p,run (realStep s w controller p) n empty r.2)

def simulated (s : Setup F) (controller : Controller F) (n : Nat)
    (r : Triple F × Tape F n) : Triple F × History F :=
  (r.1,run (simStep s controller r.1) n empty r.2)

theorem whole_coupling (s : Setup F) (w : Witness F) (controller : Controller F)
    (n : Nat) (r : Triple F × Tape F n) :
    real s w controller n r = simulated s controller n (wholeCoins s w controller n r) := by
  apply Prod.ext
  · rfl
  · exact continuation_coupling s w controller (publicationsOf w r.1) n empty r.2

theorem whole_mass [Fintype F] [DecidableEq F]
    (s : Setup F) (w : Witness F) (controller : Controller F)
    (n : Nat) (out : Triple F × History F) :
    (Fintype.card {r : Triple F × Tape F n // real s w controller n r = out} : ℚ) /
      Fintype.card (Triple F × Tape F n) =
    (Fintype.card {r : Triple F × Tape F n // simulated s controller n r = out} : ℚ) /
      Fintype.card (Triple F × Tape F n) := by
  rw [Fintype.card_congr (Zkc.Probability.Observation.fiberEquiv (wholeCoins s w controller n)
    (real s w controller n) (simulated s controller n) (whole_coupling s w controller n) out)]

theorem witness_mass [Fintype F] [DecidableEq F]
    (s : Setup F) (w v : Witness F) (controller : Controller F)
    (n : Nat) (out : Triple F × History F) :
    (Fintype.card {r : Triple F × Tape F n // real s w controller n r = out} : ℚ) /
      Fintype.card (Triple F × Tape F n) =
    (Fintype.card {r : Triple F × Tape F n // real s v controller n r = out} : ℚ) /
      Fintype.card (Triple F × Tape F n) := by
  rw [whole_mass s w,whole_mass s v]

end Zkc.Protocols.CorrelatedSetup.Service
