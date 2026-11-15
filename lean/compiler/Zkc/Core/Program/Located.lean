module

public import Zkc.Core.Program.Vocabulary

@[expose] public section

/-!
Located types and role maps.

A located type is a type and the roles that hold a value of it. The role map of an
application is a bijection of role numbers that sends the callee's roles to the caller's.
-/

namespace Zkc.Core

/-! ## Located types -/

/-- A type and the roles that hold a value of it. -/
structure LTy (V : Vocabulary) where
  ty : V.Ty
  holders : Holders
deriving DecidableEq

@[reducible] def LTy.map {V : Vocabulary} (ρ : Role → Role) (a : LTy V) : LTy V :=
  ⟨a.ty, a.holders.map ρ⟩

/-- A value of the first may be used where the second is asked: the same type, held by at
least the holders asked. -/
def LTy.Covers {V : Vocabulary} (a b : LTy V) : Prop :=
  a.ty = b.ty ∧ ∀ r, r ∈ b.holders → r ∈ a.holders

/-- The iteration number inside a loop that `ps` perform. -/
@[reducible] def LTy.index {V : Vocabulary} (ps : Holders) : LTy V := ⟨.nat, ps⟩

/-- The sequence of the values of a located type that the iterations of a loop collect, held
as the values were. -/
@[reducible] def LTy.collected {V : Vocabulary} (size : Option Nat) (a : LTy V) : LTy V :=
  ⟨.seq a.ty size, a.holders⟩

/-! ## Role maps -/

/-- The role map of an application: the caller's role of each role of the callee, as a
bijection of role numbers. -/
structure RoleMap where
  to : Role → Role
  back : Role → Role
  left : ∀ j, back (to j) = j
  right : ∀ r, to (back r) = r

theorem RoleMap.injective (ρ : RoleMap) : ∀ a b, ρ.to a = ρ.to b → a = b := by
  intro a b e
  have := congrArg ρ.back e
  rwa [ρ.left, ρ.left] at this

/-- The exchange of two roles. -/
def swapRoles (a b x : Role) : Role := if x = a then b else if x = b then a else x

theorem swapRoles_swapRoles (a b x : Role) : swapRoles a b (swapRoles a b x) = x := by
  unfold swapRoles
  by_cases h1 : x = a
  · subst h1
    by_cases h2 : b = x <;> simp [h2]
  · by_cases h2 : x = b
    · subst h2
      simp [h1]
    · simp [h1, h2]

/-- Every role as it is. -/
def RoleMap.identity : RoleMap := ⟨fun j => j, fun r => r, fun _ => rfl, fun _ => rfl⟩

/-- A role map, then the exchange of two roles. -/
def RoleMap.swap (ρ : RoleMap) (a b : Role) : RoleMap where
  to j := swapRoles a b (ρ.to j)
  back r := ρ.back (swapRoles a b r)
  left j := by simp only [swapRoles_swapRoles, ρ.left]
  right r := by simp only [ρ.right, swapRoles_swapRoles]

/-- From the position `start` on, each position to the role at it, one exchange at a time. -/
def RoleMap.fill : List Role → Nat → RoleMap → RoleMap
  | [], _, ρ => ρ
  | r :: rest, start, ρ => RoleMap.fill rest (start + 1) (ρ.swap (ρ.to start) r)

set_option linter.unusedVariables false in
/-- The role map that sends the callee's role `j` to the caller's role `roles[j]`, for every
`j` below the length; it is a bijection of role numbers. That the roles are distinct is what
makes it send each position to its role (`RoleMap.ofList_to`). -/
def RoleMap.ofList (roles : List Role) (distinct : roles.Nodup) : RoleMap :=
  RoleMap.fill roles 0 RoleMap.identity

theorem RoleMap.fill_to : ∀ (rest pre : List Role) (ρ : RoleMap), (pre ++ rest).Nodup →
    (∀ i (h : i < pre.length), ρ.to i = pre[i]) →
    ∀ i (h : i < (pre ++ rest).length), (RoleMap.fill rest pre.length ρ).to i = (pre ++ rest)[i]
  | [], pre, ρ, _, hρ, i, h => by
      have lt : i < pre.length := by simpa using h
      simp only [RoleMap.fill]
      rw [List.getElem_append_left lt]
      exact hρ i lt
  | r :: rest, pre, ρ, nd, hρ, i, h => by
      have step : ∀ j (hj : j < (pre ++ [r]).length),
          (ρ.swap (ρ.to pre.length) r).to j = (pre ++ [r])[j] := by
        intro j hj
        simp only [List.length_append, List.length_singleton] at hj
        show swapRoles (ρ.to pre.length) r (ρ.to j) = _
        by_cases e : j = pre.length
        · subst e
          rw [List.getElem_append_right (Nat.le_refl _)]
          simp [swapRoles]
        · have lt : j < pre.length := by omega
          rw [List.getElem_append_left lt, hρ j lt]
          have ne1 : pre[j] ≠ ρ.to pre.length := by
            rw [← hρ j lt]
            intro e'
            exact e (ρ.injective _ _ e')
          have ne2 : pre[j] ≠ r := (List.nodup_append.mp nd).2.2 pre[j] (List.getElem_mem lt) r
            (by simp)
          simp [swapRoles, ne1, ne2]
      have ih := RoleMap.fill_to rest (pre ++ [r]) (ρ.swap (ρ.to pre.length) r) (by simpa using nd)
        step i (by simpa using h)
      simp only [List.length_append, List.length_singleton, List.append_assoc,
        List.singleton_append] at ih
      exact ih

/-- The role map of a list sends each position below the length to the role at it. -/
theorem RoleMap.ofList_to (roles : List Role) (distinct : roles.Nodup) :
    ∀ j (h : j < roles.length), (RoleMap.ofList roles distinct).to j = roles[j] := by
  intro j h
  have := RoleMap.fill_to roles [] RoleMap.identity (by simpa using distinct)
    (fun i hi => absurd hi (Nat.not_lt_zero _)) j (by simpa using h)
  show (RoleMap.fill roles 0 RoleMap.identity).to j = roles[j]
  simpa using this

/-- A caller's role outside the list plays a callee's role at or above its length. -/
theorem RoleMap.ofList_back (roles : List Role) (distinct : roles.Nodup) {r : Role}
    (out : r ∉ roles) : roles.length ≤ (RoleMap.ofList roles distinct).back r := by
  apply Nat.le_of_not_lt
  intro lt
  apply out
  have := RoleMap.ofList_to roles distinct _ lt
  rw [RoleMap.right] at this
  rw [this]
  exact List.getElem_mem lt


/-! ## Membership in a set of holders -/

theorem Holders.mem_insert {r x : Role} : ∀ {holders : Holders},
    r ∈ Holders.insert x holders ↔ r = x ∨ r ∈ holders
  | [] => by simp [Holders.insert]
  | h :: rest => by
      unfold Holders.insert
      by_cases lt : x < h
      · simp [lt]
      · by_cases eq : x = h
        · subst eq
          simp
        · simp only [lt, eq, ↓reduceIte, List.mem_cons]
          rw [Holders.mem_insert (holders := rest)]
          constructor
          · rintro (e | e | e)
            · exact .inr (.inl e)
            · exact .inl e
            · exact .inr (.inr e)
          · rintro (e | e | e)
            · exact .inr (.inl e)
            · exact .inl e
            · exact .inr (.inr e)

theorem Holders.mem_ofList {r : Role} : ∀ {roles : List Role},
    r ∈ Holders.ofList roles ↔ r ∈ roles
  | [] => by simp [Holders.ofList]
  | x :: rest => by
      have ih := Holders.mem_ofList (r := r) (roles := rest)
      simp only [Holders.ofList, List.foldr_cons, List.mem_cons] at ih ⊢
      rw [Holders.mem_insert, ih]

end Zkc.Core
