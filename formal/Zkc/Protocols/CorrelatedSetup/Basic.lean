import Zkc.Probability.FramedMask
import Zkc.Probability.AffineMask
import Zkc.Protocols.CorrelatedSetup.Authentication
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.LinearCombination


set_option autoImplicit false
namespace Zkc.Protocols.CorrelatedSetup
variable {F : Type} [CommRing F]

abbrev Triple (F : Type) := F × F × F

structure Witness (F : Type) [CommRing F] where
  x : F
  y : F
  valid : x * y = 1

-- Figure 3's malicious-verifier branch: all these values may be chosen by V.
-- Delta is persistent; it is not restricted to be nonzero.
structure Setup (F : Type) where
  delta : F
  kx : F
  ky : F
  kz : F
  star : F
  deriving DecidableEq

def publicationsOf (w : Witness F) (r : Triple F) : Triple F :=
  (w.x-r.1, w.y-r.2.1, 1-r.2.2)

def prefixEquiv (w : Witness F) : Triple F ≃ Triple F where
  toFun := publicationsOf w
  invFun := publicationsOf w
  left_inv r := by rcases r with ⟨a,b,c⟩; simp [publicationsOf]
  right_inv r := by rcases r with ⟨a,b,c⟩; simp [publicationsOf]

def tags (s : Setup F) (r : Triple F) : Triple F :=
  (s.kx-s.delta*r.1, s.ky-s.delta*r.2.1, s.kz-s.delta*r.2.2)

def keys (s : Setup F) (p : Triple F) : Triple F :=
  (s.kx+s.delta*p.1, s.ky+s.delta*p.2.1, s.kz+s.delta*p.2.2)

-- Prover-local algebra: this function takes no verifier key or verifier tags.
def coefficients (w : Witness F) (m : Triple F) : F × F :=
  (m.1*m.2.1, w.x*m.2.1+w.y*m.1-m.2.2)

def localResponse (a mask : F × F) (chi : F) : F × F :=
  (chi*a.1+mask.1, chi*a.2+mask.2)

def gate (s : Setup F) (p : Triple F) : F :=
  let k := keys s p
  k.1*k.2.1-k.2.2*s.delta

def byPrefix (s : Setup F) (w : Witness F) (p : Triple F) : F × F :=
  coefficients w (tags s (publicationsOf w p))

theorem gate_identity (s : Setup F) (w : Witness F) (p : Triple F) :
    gate s p = (byPrefix s w p).1 + (byPrefix s w p).2*s.delta := by
  dsimp [gate,keys,byPrefix,coefficients,tags,publicationsOf]
  linear_combination s.delta^2 * w.valid

theorem output_identity (s : Setup F) (w : Witness F) (p : Triple F) :
    (tags s (publicationsOf w p)).2.2 = (keys s p).2.2-s.delta := by
  simp only [tags,publicationsOf,keys]
  ring

-- Figure 3 VOPE(1), honest P: a1 is uniform; a0 is determined by B* and Delta.
def vope (s : Setup F) (r : F) : F × F := (s.star-s.delta*r,r)

def maskMap (delta : F) : (F × F) →+ F where
  toFun r := r.1+delta*r.2
  map_zero' := by simp
  map_add' a b := by simp; ring

theorem vope_law (s : Setup F) (r : F) : maskMap s.delta (vope s r) = s.star := by
  simp [maskMap,vope]

def providerFiber (s : Setup F) : F ≃ {r : F × F // maskMap s.delta r = s.star} where
  toFun r := ⟨vope s r,vope_law s r⟩
  invFun r := r.val.2
  left_inv _ := rfl
  right_inv r := by
    apply Subtype.ext
    apply Prod.ext
    · have h := r.property
      dsimp [maskMap] at h
      dsimp [vope]
      linear_combination -h
    · rfl

def responseOffset (s : Setup F) (w : Witness F) (p : Triple F) (chi : F) : F × F :=
  (chi*(byPrefix s w p).1,chi*(byPrefix s w p).2)

theorem offset_map (s : Setup F) (w : Witness F) (p : Triple F) (chi : F) :
    maskMap s.delta (responseOffset s w p chi) = chi*gate s p := by
  rw [gate_identity s w p]
  dsimp [maskMap,responseOffset]
  ring

-- Zkc.Probability.FramedMask's conditional affine theorem now has the actual VOPE history map,
-- actual online offsets, and every verifier-chosen Delta including zero.
theorem conditional_response_mass [Fintype F] [DecidableEq F]
    (s : Setup F) (w v : Witness F) (p : Triple F) (chi : F) (out : F × F) :
    Zkc.Probability.FramedMask.conditionalMass (AddMonoidHom.id (F × F)) (maskMap s.delta) s.star
      (responseOffset s w p chi) out =
    Zkc.Probability.FramedMask.conditionalMass (AddMonoidHom.id (F × F)) (maskMap s.delta) s.star
      (responseOffset s v p chi) out := by
  apply Zkc.Probability.FramedMask.conditional_mass_preserved _ _ _ _ _
    (responseOffset s w p chi-responseOffset s v p chi)
  · simp only [map_sub,offset_map,sub_self]
  · rfl

-- A triangular bijection, with no linearity requirement on the first-coordinate
-- dependent offset. This connects source input masks to visible coordinates.
def shear {X : Type} (f : X → F) : (X × F) ≃ (X × F) where
  toFun r := (r.1,r.2+f r.1)
  invFun r := (r.1,r.2-f r.1)
  left_inv r := by simp
  right_inv r := by simp

structure View (F : Type) where
  publications : Triple F
  challenge : F
  response : F × F
  outputTag : F
  deriving DecidableEq

def source (s : Setup F) (chi : Triple F → F) (w : Witness F)
    (r : Triple F × F) : View F :=
  let p := publicationsOf w r.1
  let m := tags s r.1
  ⟨p,chi p,localResponse (coefficients w m) (vope s r.2) (chi p),m.2.2⟩

def simulator (s : Setup F) (chi : Triple F → F) (r : Triple F × F) : View F :=
  ⟨r.1,chi r.1,(chi r.1*gate s r.1+s.star-r.2*s.delta,r.2),
    (keys s r.1).2.2-s.delta⟩

def sourceCoins (s : Setup F) (chi : Triple F → F) (w : Witness F) :
    (Triple F × F) ≃ (Triple F × F) :=
  (Equiv.prodCongr (prefixEquiv w) (Equiv.refl F)).trans
    (shear (fun p => chi p*(byPrefix s w p).2))

theorem sourceCoins_apply (s : Setup F) (chi : Triple F → F) (w : Witness F)
    (r : Triple F × F) : sourceCoins s chi w r =
    (publicationsOf w r.1,r.2+chi (publicationsOf w r.1)*
      (byPrefix s w (publicationsOf w r.1)).2) := rfl

theorem source_coupling (s : Setup F) (chi : Triple F → F) (w : Witness F)
    (r : Triple F × F) : source s chi w r = simulator s chi (sourceCoins s chi w r) := by
  have hp : publicationsOf w (publicationsOf w r.1) = r.1 := (prefixEquiv w).left_inv r.1
  have hg := gate_identity s w (publicationsOf w r.1)
  have ho := output_identity s w (publicationsOf w r.1)
  simp only [byPrefix,hp] at hg
  simp only [hp] at ho
  rw [sourceCoins_apply]
  dsimp only [source,simulator,localResponse,vope]
  simp only [byPrefix,hp]
  rw [ho]
  congr 1
  · apply Prod.ext
    · rw [hg]; ring
    · ring

theorem source_mass [Fintype F] [DecidableEq F]
    (s : Setup F) (chi : Triple F → F) (w : Witness F) (out : View F) :
    (Fintype.card {r : Triple F × F // source s chi w r = out} : ℚ) /
      Fintype.card (Triple F × F) =
    (Fintype.card {r : Triple F × F // simulator s chi r = out} : ℚ) /
      Fintype.card (Triple F × F) := by
  rw [Fintype.card_congr (Zkc.Probability.Observation.fiberEquiv (sourceCoins s chi w)
    (source s chi w) (simulator s chi) (source_coupling s chi w) out)]

end Zkc.Protocols.CorrelatedSetup
