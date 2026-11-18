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

section
variable {T : Type} {F : T → Type} {P : ∀ t, F t → Prop}

/-- One more name bound to a valid value keeps every value in scope valid. -/
theorem Env.insert_preserves {Γ : Ctx T} {env : Env F Γ}
    (valid : ∀ τ (x : Var Γ τ), P τ (env.get x)) (bound : Name) {τ : T} (v : F τ)
    (valid' : P τ v) :
    ∀ σ (x : Var (Γ.insert bound τ) σ), P σ ((env.insert bound v).get x) := by
  intro σ x
  obtain ⟨name, found⟩ := x
  show P σ (env.insert bound v name σ found)
  by_cases same : name = bound
  · have typed : σ = τ := by
      have look := found
      rw [Ctx.find?_insert, ite_eq_left same] at look
      exact (Option.some.inj look).symm
    subst typed
    rw [eq_of_heq (Env.insert_at_bound env bound v same found)]
    exact valid'
  · rw [Env.insert_at_other env bound v same]
    exact valid σ ⟨name, (ite_eq_right same).symm.trans
      ((Ctx.find?_insert Γ bound τ name).symm.trans found)⟩

/-- The names of a binding bound to valid values keep every value in scope valid. -/
theorem Env.extend_preserves : ∀ {Γ : Ctx T} {env : Env F Γ},
    (∀ τ (x : Var Γ τ), P τ (env.get x)) →
    ∀ {types : List T} (bound : Names types) (vs : HList F types), vs.All P →
      ∀ τ (x : Var (Γ.extend bound) τ), P τ ((env.extend bound vs).get x)
  | _, _, valid, [], .nil, .nil, _ => valid
  | _, _, valid, _ :: _, .cons name rest, .cons v vs, all =>
      Env.extend_preserves (Env.insert_preserves valid name v (HList.all_cons.mp all).1) rest vs
        (HList.all_cons.mp all).2

end


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

section
variable {D : Dialect} {Raw : Type}

/-- A written operation gives results on valid operands, and the results are valid: the relation
that the facts of the table are about. -/
def ValidRun (sem : Semantics D) (Run : Raw → List sem.Dyn → List sem.Dyn → Prop)
    (Valid : sem.Dyn → Prop) (raw : Raw) (operands results : List sem.Dyn) : Prop :=
  Run raw operands results ∧ (∀ v, v ∈ operands → Valid v) ∧ ∀ v, v ∈ results → Valid v

/-- The payload of the alternative of a variant is valid. -/
def PickValid (sem : Semantics D) (Valid : sem.Dyn → Prop) {payloads : List D.Ty}
    (p : Pick sem.Val payloads) : Prop :=
  p.All fun τ v => Valid ⟨τ, v⟩

end

end Zkc.Core
