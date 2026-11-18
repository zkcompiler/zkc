module

public import Zkc.Core.Facts.Contracts.ProjectedTransport

@[expose] public section

namespace Zkc.Core.BodyAnalysis.RoleContracts

theorem every_map {S : Sig} {H A B : Type} (P : ∀ op, S.Reply op → Prop) (f : A → B)
    (D : B → Prop) (Q : H → Prop) :
    ∀ p : Process S H A, (p.map f).Every P D Q ↔ p.Every P (fun a => D (f a)) Q
  | .done _ => Iff.rfl
  | .halt _ => Iff.rfl
  | .call _ k => forall_congr' fun reply => imp_congr_right fun _ => every_map P f D Q (k reply)

section
variable {V : Vocabulary} (M : Model V)

/-- Renaming the peers of a role's process keeps what holds on every path of permitted replies:
whether a reply is permitted does not read who the peers are. -/
theorem every_mapR {B : Type} (ρ : Role → Role) (D : B → Prop) (Q : Stop → Prop) :
    ∀ p : Program M B, (mapR M ρ p).Every (Permitted M) D Q ↔ p.Every (Permitted M) D Q
  | .done _ => Iff.rfl
  | .halt _ => Iff.rfl
  | .call (.give ..) k => forall_congr' fun u => imp_congr_right fun _ => every_mapR ρ D Q (k u)
  | .call (.get ..) k => forall_congr' fun u => imp_congr_right fun _ => every_mapR ρ D Q (k u)
  | .call (.own ..) k => forall_congr' fun u => imp_congr_right fun _ => every_mapR ρ D Q (k u)
  | .call (.hear ..) k => forall_congr' fun u => imp_congr_right fun _ => every_mapR ρ D Q (k u)
  | .call (.begin ..) k => forall_congr' fun u => imp_congr_right fun _ => every_mapR ρ D Q (k u)
  | .call (.settle ..) k => forall_congr' fun u => imp_congr_right fun _ => every_mapR ρ D Q (k u)

/-! ## Validity across operations -/

theorem reveal_carry {r : Role} {τ : V.Ty} {H H' : Holders} (same : r ∈ H ↔ r ∈ H')
    (v : RV M r ⟨τ, H⟩) (h' : r ∈ H') :
    reveal M (a := ⟨τ, H'⟩) h' (carry M same v) = reveal M (a := ⟨τ, H⟩) (same.mpr h') v := by
  simp only [reveal, carry, cast_cast]

theorem valid_carry {r : Role} {τ : V.Ty} {H H' : Holders} (same : r ∈ H ↔ r ∈ H')
    (v : RV M r ⟨τ, H⟩) : RoleValueValid M r ⟨⟨τ, H'⟩, carry M same v⟩ ↔ RoleValueValid M r ⟨⟨τ, H⟩, v⟩ := by
  change (∀ h, M.Valid τ (reveal M h (carry M same v))) ↔
    ∀ h, M.Valid τ (reveal M h v)
  constructor
  · intro hv h
    have := hv (same.mp h)
    rwa [reveal_carry] at this
  · intro hv h'
    rw [reveal_carry]
    exact hv _

theorem coverRV_valid {r : Role} {a b : LTy V} (h : a.Covers b) (v : RV M r a)
    (valid : RV.Valid M r a v) : RV.Valid M r b (coverRV M h v) := by
  unfold coverRV
  split
  · next hb =>
      refine (valid_hide M r (a := b) hb _).mpr ?_
      exact (valid_cast (M := M) h.1 _).mpr (valid (h.2 r hb))
  · next hb => exact valid_out M r hb _

theorem fitAllRV_valid {r : Role} : ∀ {as bs : List (LTy V)} (fits : Fits as bs)
    (vs : HList (RV M r) as), vs.All (RV.Valid M r) → (fitAllRV M fits vs).All (RV.Valid M r)
  | [], [], _, .nil, _ => trivial
  | _ :: _, _ :: _, fits, .cons v rest, valid =>
      ⟨coverRV_valid M fits.1 v valid.1, fitAllRV_valid fits.2 rest valid.2⟩
  | [], _ :: _, fits, _, _ => nomatch fits
  | _ :: _, [], fits, _, _ => nomatch fits

theorem enterAll_valid (ρ : RoleMap) (r : Role) : ∀ {items : List (LTy V)}
    (vs : HList (RV M r) (items.map (LTy.map ρ.to))), vs.All (RV.Valid M r) →
    (enterAll M ρ r vs).All (RV.Valid M (ρ.back r))
  | [], .nil, _ => trivial
  | a :: _, .cons v rest, valid => by
      refine ⟨?_, enterAll_valid ρ r rest valid.2⟩
      show RV.Valid M (ρ.back r) a (enter M ρ r a v)
      unfold enter
      split
      · next h =>
          exact (valid_hide M (ρ.back r) (a := a) h _).mpr (valid.1 (ρ.mem_map.mpr h))
      · next h => exact valid_out M (ρ.back r) h _

theorem leaveAll_valid (ρ : RoleMap) (r : Role) : ∀ {items : List (LTy V)}
    (vs : HList (RV M (ρ.back r)) items), vs.All (RV.Valid M (ρ.back r)) →
    (leaveAll M ρ r vs).All (RV.Valid M r)
  | [], .nil, _ => trivial
  | a :: _, .cons v rest, valid => by
      refine ⟨?_, leaveAll_valid ρ r rest valid.2⟩
      show RV.Valid M r (a.map ρ.to) (leave M ρ r a v)
      unfold leave
      split
      · next h =>
          exact (valid_hide M r (a := a.map ρ.to) (ρ.mem_map.mpr h) _).mpr (valid.1 h)
      · next h => exact valid_out M r (a := a.map ρ.to) (fun m => h (ρ.mem_map.mp m)) _

end

section
variable {V : Vocabulary} (M : Model V) {hs : Headers V} (r : Role)
  (fnTable : FnTable M hs.fns) (rTable : RTable M hs.protocols)

theorem role_settle : ∀ (w : Holders) (key : Key) (path : List Frame),
    ((roleSem M r fnTable rTable).settle w key path).Every (Permitted M) (fun _ => True)
      (fun stop => ¬ stop = Stop.undefined) := by
  intro w key path
  show Process.Every _ _ _ (if r ∈ w then _ else _)
  split
  · intro _ _
    trivial
  · trivial

theorem role_begin : ∀ (w : Holders) (key : Key) (path : List Frame),
    ((roleSem M r fnTable rTable).begin w key path).Every (Permitted M)
      (fun n => RoleValueValid M r ⟨LTy.index w, n⟩) (fun stop => ¬ stop = Stop.undefined) := by
  intro w key path
  show Process.Every _ _ _ (if r ∈ w then _ else _)
  split
  · next h =>
      intro n _
      exact (valid_hide M r (a := LTy.index w) h n).mpr trivial
  · next h => exact valid_out M r (a := LTy.index w) h _

theorem role_collect : ∀ (size : Option Nat) (a : LTy V) (vs : List (RV M r a)),
    (∀ n, size = some n → vs.length = n) → (∀ v, v ∈ vs → RoleValueValid M r ⟨a, v⟩) →
    RoleValueValid M r ⟨LTy.collected size a, (roleSem M r fnTable rTable).collect size a vs⟩ := by
  intro size a vs length valid
  show RoleValueValid M r ⟨LTy.collected size a, collectRV M r size a vs⟩
  unfold collectRV
  split
  · next h =>
      refine (valid_hide M r (a := LTy.collected size a) h _).mpr ⟨fun x m => ?_, ?_⟩
      · obtain ⟨v, mv, rfl⟩ := List.mem_map.mp m
        exact valid v mv h
      · intro n e
        rw [List.length_map]
        exact length n e
  · next h => exact valid_out M r (a := LTy.collected size a) h _

/-- A cast of the alternative of a variant along an equality of its payload types keeps what holds
of its payload. -/
theorem pick_cast {W : LTy V → Type} {ps qs : List (LTy V)} (h : ps = qs) (p : Pick W ps)
    (P : ∀ a, W a → Prop) : (cast (congrArg (Pick W) h) p).All P ↔ p.All P := by
  subst h
  rfl

/-- The alternative of a valid value of a variant whose payloads the role holds has a valid
payload. -/
theorem pickAt_valid (ps : Holders) (hps : r ∈ ps) :
    ∀ (alts : Tys V.TypeKey) (c : alts.Choice M.toCarriers), Tys.ValidChoice M.toCarriers alts c →
      (Tys.pickAt M ps (W := RV M r) (fun τ u => hide M r ⟨τ, ps⟩ u) alts c).All
        (fun a x => RoleValueValid M r ⟨a, x⟩)
  | .nil, c, _ => nomatch c
  | .cons head _, .inl v, h => (valid_hide M r (a := ⟨head, ps⟩) hps v).mpr h
  | .cons _ rest, .inr c, h => pickAt_valid ps hps rest c h

/-- The branch of a held variant exposes a valid payload at the choice performers. -/
theorem role_pick : ∀ {w : Holders} {t : LTy V} {payloads : List (LTy V)}
    (ok : (roleDialect V hs r).Alternatives w t payloads) (v : RV M r t), RoleValueValid M r ⟨t, v⟩ →
    PickValid (roleSem M r fnTable rTable) (RoleValueValid M r)
      ((roleSem M r fnTable rTable).pick ok v) := by
  intro w t payloads ok v valid
  have ht : r ∈ t.holders := by obtain ⟨_, _, _, _, ht, _⟩ := ok; exact ht
  have hw : r ∈ w := by obtain ⟨_, _, _, _, _, hw⟩ := ok; exact hw
  show Pick.All _ (rolePick M r ok v)
  unfold rolePick locatedPick
  rw [pick_cast]
  · apply pickAt_valid M r w hw
    have hok : ∃ key alternatives, t.ty = .variant key alternatives ∧
        payloads = alternatives.toList.map (fun τ => (⟨τ, w⟩ : LTy V)) := by
      obtain ⟨key, alternatives, e, p, _⟩ := ok
      exact ⟨key, alternatives, e, p⟩
    exact (valid_cast (M := M) (Ty.eq_variant hok) (reveal M ht v)).mpr (valid ht)
  · obtain ⟨_, _, e, p, _⟩ := ok
    rw [Ty.alternatives_of e, p]

end
end Zkc.Core.BodyAnalysis.RoleContracts
