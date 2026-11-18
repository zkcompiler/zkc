module

public import Zkc.Core.Meaning.Fold

@[expose] public section

/-!
Validity of the values of a meaning, for any dialect.

Validity is a predicate of a value with its type (`Semantics.Dyn`), and values of a list are
valid when each of them with its type is (membership in `Semantics.dyns`), which is `HList.All`
of the predicate at each type (`Semantics.dyns_valid_iff`, the one conversion between the form of
the statements about any dialect and the form of those about functions). The values of variables
in scope are valid when every value in scope is (`env_all_valid`), and what a loop collects is
valid when its iterations' values are and the law of the collected values holds (`CollectedOK`,
`collected_valid`). Nothing here is about a dialect or the vocabulary: the validity of the values
of a function is in `Meaning/Validity.lean`.
-/

namespace Zkc.Core

/-! ## Valid values of any dialect -/

section
variable {D : Dialect} {sem : Semantics D} {Valid : sem.Dyn → Prop}

/-- **The one conversion between the two forms of validity.** Values with their types are valid
exactly when each value is valid at its type: the form of the statements about any dialect
(membership in `sem.dyns`) and the form `HList.All` of the statements about functions. -/
theorem Semantics.dyns_valid_iff (sem : Semantics D) {Valid : sem.Dyn → Prop} :
    ∀ {items : List D.Ty} (vs : HList sem.Val items),
      (∀ v, v ∈ sem.dyns vs → Valid v) ↔ vs.All fun τ v => Valid ⟨τ, v⟩
  | [], .nil => ⟨fun _ => trivial, fun _ _ found => nomatch found⟩
  | _ :: _, .cons v rest => by
      rw [HList.all_cons, ← sem.dyns_valid_iff (Valid := Valid) rest]
      constructor
      · intro all
        exact ⟨all _ List.mem_cons_self, fun w found => all w (List.mem_cons_of_mem _ found)⟩
      · intro both w found
        rcases List.mem_cons.mp found with same | found
        · subst same
          exact both.1
        · exact both.2 w found

/-- The values of variables are valid when every value in scope is. -/
theorem env_all_valid {Γ : Ctx D.Ty} {env : Env sem.Val Γ}
    (valid : ∀ τ (x : Var Γ τ), Valid ⟨τ, env.get x⟩) :
    ∀ {items : List D.Ty} (xs : HList (Var Γ) items), ∀ v, v ∈ sem.dyns (env.all xs) → Valid v
  | [], .nil => fun _ found => nomatch found
  | _ :: _, .cons x rest => (sem.dyns_valid_iff _).mpr (HList.all_cons.mpr
      ⟨valid _ x, (sem.dyns_valid_iff _).mp (env_all_valid valid rest)⟩)

variable (sem Valid) in
/-- Values collected so far by a loop: as many of each type as iterations, each valid. -/
def CollectedOK : {each : List D.Ty} → HList (fun a => List (sem.Val a)) each → Nat → Prop
  | [], .nil, _ => True
  | a :: _, .cons vs rest, i =>
      vs.length = i ∧ (∀ v, v ∈ vs → Valid ⟨a, v⟩) ∧ CollectedOK rest i

/-- Nothing collected is as many as no iteration. -/
theorem collectedOK_empties : ∀ (each : List D.Ty),
    CollectedOK sem Valid (HList.empties (V := sem.Val) each) 0
  | [] => trivial
  | _ :: rest => ⟨rfl, fun _ found => (nomatch found), collectedOK_empties rest⟩

/-- One more iteration's valid values keep what is collected valid. -/
theorem collectedOK_push : ∀ {each : List D.Ty} {acc : HList (fun a => List (sem.Val a)) each}
    {i : Nat} {vs : HList sem.Val each}, CollectedOK sem Valid acc i →
    (∀ v, v ∈ sem.dyns vs → Valid v) → CollectedOK sem Valid (acc.push vs) (i + 1)
  | [], .nil, _, .nil, _, _ => trivial
  | _ :: _, .cons xs rest, _, .cons v more, collected, all => by
      obtain ⟨length, valid, others⟩ := collected
      have parts := HList.all_cons.mp ((sem.dyns_valid_iff (.cons v more)).mp all)
      refine ⟨by simp [length], fun w found => ?_,
        collectedOK_push others ((sem.dyns_valid_iff more).mpr parts.2)⟩
      rcases List.mem_cons.mp found with same | found
      · subst same
        exact parts.1
      · exact valid w found

/-- What a loop collects, as one value of each type, is valid, given the law that the values
collected of valid values are valid when they are as many as the size given. -/
theorem collected_valid
    (collect : ∀ (size : Option Nat) (a : D.Ty) (vs : List (sem.Val a)),
      (∀ n, size = some n → vs.length = n) → (∀ v, v ∈ vs → Valid ⟨a, v⟩) →
      Valid ⟨D.collected size a, sem.collect size a vs⟩)
    (size : Option Nat) {n : Nat} (fits : ∀ m, size = some m → n = m) :
    ∀ {each : List D.Ty} {acc : HList (fun a => List (sem.Val a)) each},
      CollectedOK sem Valid acc n → ∀ v, v ∈ sem.dyns (sem.collected size acc) → Valid v
  | [], .nil, _ => fun _ found => nomatch found
  | a :: _, .cons vs rest, collected => by
      obtain ⟨length, valid, others⟩ := collected
      refine (sem.dyns_valid_iff _).mpr (HList.all_cons.mpr ⟨collect size a vs.reverse
          (fun m e => by rw [List.length_reverse, length]; exact fits m e)
          (fun v found => valid v (List.mem_reverse.mp found)), ?_⟩)
      exact (sem.dyns_valid_iff _).mp (collected_valid collect size fits others)

end

end Zkc.Core
