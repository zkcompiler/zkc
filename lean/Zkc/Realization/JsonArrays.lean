import Lean

set_option autoImplicit false

namespace Zkc.Realization.JsonArrays
open Lean (Json)

-- An internal proof representation of the existing JSON array schema.
-- No object, floating-point, null, or Boolean representation is admitted.
inductive Wire where
  | nat (n : Nat)
  | str (s : String)
  | array (xs : List Wire)
  deriving Repr

def toJson : Wire → Json
  | .nat n => .num ⟨Int.ofNat n, 0⟩
  | .str s => .str s
  | .array xs => .arr (xs.map toJson).toArray

def matchList (f : Json → Wire → Bool) : List Json → List Wire → Bool
  | [], [] => true
  | j :: js, w :: ws => f j w && matchList f js ws
  | _, _ => false

def checkJson : Nat → Json → Wire → Bool
  | 0, _, _ => false
  | _+1, .num ⟨Int.ofNat n, 0⟩, .nat m => decide (n = m)
  | _+1, .str s, .str t => decide (s = t)
  | fuel+1, .arr js, .array ws => matchList (checkJson fuel) js.toList ws
  | _, _, _ => false

theorem matchList_sound (f : Json → Wire → Bool)
    (sound : ∀ j w, f j w = true → j = toJson w)
    (js : List Json) (ws : List Wire) (h : matchList f js ws = true) :
    js = ws.map toJson := by
  induction js generalizing ws with
  | nil => cases ws <;> simp_all [matchList]
  | cons j js ih =>
    cases ws with
    | nil => simp [matchList] at h
    | cons w ws =>
      simp only [matchList, Bool.and_eq_true] at h
      simp [sound j w h.1, ih ws h.2]

theorem checkJson_sound (fuel : Nat) (j : Json) (w : Wire)
    (h : checkJson fuel j w = true) : j = toJson w := by
  induction fuel generalizing j w with
  | zero => simp [checkJson] at h
  | succ fuel ih =>
    cases w with
    | nat n =>
      cases j <;> try simp [checkJson] at h
      rename_i x
      obtain ⟨m,e⟩ := x
      cases m <;> cases e <;> simp_all [checkJson, toJson]
      change decide (_ = n) = true at h
      exact congrArg Int.ofNat (of_decide_eq_true h)
    | str s => cases j <;> simp_all [checkJson, toJson]
    | array ws =>
      cases j <;> try simp [checkJson] at h
      rename_i js
      have hl := matchList_sound (checkJson fuel) ih js.toList ws h
      have ha := congrArg List.toArray hl
      simpa [toJson] using congrArg Json.arr ha

theorem toJson_injective (w v : Wire) (h : toJson w = toJson v) : w = v := by
  induction w using Wire.rec
      (motive_2 := fun ws => ∀ vs, ws.map toJson = vs.map toJson → ws = vs)
      generalizing v with
  | nat n =>
    cases v <;> simp_all [toJson]
    exact Int.ofNat.inj h
  | str s => cases v <;> simp_all [toJson]
  | array ws ih =>
    cases v <;> try simp [toJson] at h
    rename_i vs
    exact congrArg Wire.array (ih vs h)
  | nil => rename_i vs hv; cases vs <;> simp_all
  | cons w ws ihw ihws =>
    rename_i vs hv
    cases vs with
    | nil => simp at hv
    | cons v vs =>
      simp only [List.map_cons, List.cons.injEq] at hv
      simp [ihw v hv.1, ihws vs hv.2]

def fits : Nat → Wire → Bool
  | 0, _ => false
  | _+1, .nat _ => true
  | _+1, .str _ => true
  | fuel+1, .array ws => ws.all (fits fuel)

theorem matchList_complete (f : Json → Wire → Bool) (ws : List Wire)
    (h : ∀ w ∈ ws, f (toJson w) w = true) :
    matchList f (ws.map toJson) ws = true := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [List.map_cons, matchList, Bool.and_eq_true]
    exact ⟨h w (by simp), ih (fun v hv => h v (by simp [hv]))⟩

theorem checkJson_complete (fuel : Nat) (w : Wire) (h : fits fuel w = true) :
    checkJson fuel (toJson w) w = true := by
  induction fuel generalizing w with
  | zero => simp [fits] at h
  | succ fuel ih =>
    cases w with
    | nat n => rw [toJson]; change decide (n = n) = true; simp
    | str s => simp [checkJson, toJson]
    | array ws =>
      simp only [fits, List.all_eq_true] at h
      simpa [checkJson, toJson] using
        matchList_complete (checkJson fuel) ws (fun w hw => ih w (h w hw))

theorem checkJson_iff (fuel : Nat) (j : Json) (w : Wire) (h : fits fuel w = true) :
    checkJson fuel j w = true ↔ j = toJson w := by
  constructor
  · exact checkJson_sound fuel j w
  · intro hj; rw [hj]; exact checkJson_complete fuel w h

end Zkc.Realization.JsonArrays
