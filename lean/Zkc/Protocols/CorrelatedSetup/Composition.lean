import Zkc.Protocols.CorrelatedSetup.Basic


set_option autoImplicit false
namespace Zkc.Protocols.CorrelatedSetup
variable {F H : Type} [CommRing F]

theorem sourceCoins_fst (s : Setup F) (chi : Triple F → F) (w : Witness F)
    (r : Triple F × F) : (sourceCoins s chi w r).1 = publicationsOf w r.1 := rfl

theorem response_reconstruct (s : Setup F) (w : Witness F) (p : Triple F)
    (chi star r : F) :
    localResponse (byPrefix s w p) (star-s.delta*r,r) chi =
      (chi*gate s p+star-(r+chi*(byPrefix s w p).2)*s.delta,
        r+chi*(byPrefix s w p).2) := by
  rw [gate_identity s w p]
  apply Prod.ext <;> dsimp [localResponse] <;> ring

-- The first response may be only partially delivered. The observer is a
-- deterministic function of its full verifier view, never of hidden P state.
-- The second B* and challenge may depend on that retained history.
-- Authenticated wires and Delta persist; only the second VOPE coin is fresh.
def retrySource (s : Setup F) (chi : Triple F → F) (observe : View F → H)
    (next : H → F × F) (w : Witness F) (r : (Triple F × F) × F) : H × View F :=
  let first := source s chi w r.1
  let h := observe first
  let n := next h
  let m := tags s r.1.1
  (h,⟨first.publications,n.2,
    localResponse (coefficients w m) (n.1-s.delta*r.2,r.2) n.2,m.2.2⟩)

def retrySimulator (s : Setup F) (chi : Triple F → F) (observe : View F → H)
    (next : H → F × F) (r : (Triple F × F) × F) : H × View F :=
  let first := simulator s chi r.1
  let h := observe first
  let n := next h
  (h,⟨first.publications,n.2,
    (n.2*gate s first.publications+n.1-r.2*s.delta,r.2),
    (keys s first.publications).2.2-s.delta⟩)

def retryCoins (s : Setup F) (chi : Triple F → F) (observe : View F → H)
    (next : H → F × F) (w : Witness F) :
    ((Triple F × F) × F) ≃ ((Triple F × F) × F) :=
  (Equiv.prodCongr (sourceCoins s chi w) (Equiv.refl F)).trans
    (shear (fun a => (next (observe (simulator s chi a))).2*(byPrefix s w a.1).2))

theorem retryCoins_apply (s : Setup F) (chi : Triple F → F) (observe : View F → H)
    (next : H → F × F) (w : Witness F) (r : (Triple F × F) × F) :
    retryCoins s chi observe next w r =
    (sourceCoins s chi w r.1,r.2+(next (observe (simulator s chi (sourceCoins s chi w r.1)))).2*
      (byPrefix s w (sourceCoins s chi w r.1).1).2) := rfl

theorem retry_coupling (s : Setup F) (chi : Triple F → F) (observe : View F → H)
    (next : H → F × F) (w : Witness F) (r : (Triple F × F) × F) :
    retrySource s chi observe next w r =
      retrySimulator s chi observe next (retryCoins s chi observe next w r) := by
  have first := source_coupling s chi w r.1
  have hp : publicationsOf w (publicationsOf w r.1.1) = r.1.1 :=
    (prefixEquiv w).left_inv r.1.1
  have hr := response_reconstruct s w (publicationsOf w r.1.1)
    (next (observe (source s chi w r.1))).2
    (next (observe (source s chi w r.1))).1 r.2
  have ho := output_identity s w (publicationsOf w r.1.1)
  simp only [byPrefix,hp] at hr
  simp only [hp] at ho
  rw [retryCoins_apply]
  dsimp only [retrySource,retrySimulator]
  simp only [← first]
  change (observe (source s chi w r.1), _) = (observe (source s chi w r.1), _)
  apply Prod.ext
  · rfl
  · change (⟨publicationsOf w r.1.1,_,_,_⟩ : View F) = ⟨publicationsOf w r.1.1,_,_,_⟩
    simp only [sourceCoins_fst,byPrefix,hp]
    rw [hr,ho]
    rfl

theorem retry_mass [Fintype F] [DecidableEq F] [DecidableEq H]
    (s : Setup F) (chi : Triple F → F) (observe : View F → H)
    (next : H → F × F) (w : Witness F) (out : H × View F) :
    (Fintype.card {r : (Triple F × F) × F // retrySource s chi observe next w r = out} : ℚ) /
      Fintype.card ((Triple F × F) × F) =
    (Fintype.card {r : (Triple F × F) × F // retrySimulator s chi observe next r = out} : ℚ) /
      Fintype.card ((Triple F × F) × F) := by
  rw [Fintype.card_congr (Zkc.Probability.Observation.fiberEquiv (retryCoins s chi observe next w)
    (retrySource s chi observe next w) (retrySimulator s chi observe next)
    (retry_coupling s chi observe next w) out)]

-- A concrete partial-output history includes publications, challenge and U.
-- It omits the undelivered V and tag. Abort is the service's fixed exit marker.
def afterU (v : View F) : Triple F × F × F :=
  (v.publications,v.challenge,v.response.1)

-- Whole key/mask replacement is not necessary for this privacy statement:
-- response coefficients are pure and can be retained alongside their wires.
theorem pure_coefficients_shared (a firstMask secondMask : F × F) (c d : F) :
    (localResponse a firstMask c,localResponse a secondMask d) =
    let saved := a
    (localResponse saved firstMask c,localResponse saved secondMask d) := rfl

end Zkc.Protocols.CorrelatedSetup
