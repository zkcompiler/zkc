module

public import Zkc.Core.Meaning.Role

@[expose] public section
set_option autoImplicit false

/-! Input and witness telescopes shared by written goals. Their qualified names also expose
the recursion equations that proof authors can use on deployed role inputs. -/

namespace ZkcFormal.Written.Goal.Internal
open Zkc.Core
variable {V : Vocabulary} (M : Model V)

/-- Bind each visible value next to its validity, building every position in the deployed header. -/
def inputs (r : Role) (existential : Bool) :
    (ports : List (LTy V)) → (HList (RV M r) ports → Prop) → Prop
  | [], k => k .nil
  | port :: rest, k =>
    if h : r ∈ port.holders then
      let more := fun (x : M.Val port.ty) ↦
        inputs r existential rest fun xs ↦ k (.cons (hide M r port x) xs)
      if existential then ∃ x, M.Valid port.ty x ∧ more x else ∀ x, M.Valid port.ty x → more x
    else
      inputs r existential rest fun xs ↦ k (.cons (nothing M h) xs)

/-- Read a heterogeneous value at its typed position. -/
def valueAt {α : Type} {F : α → Type} :
    {ts : List α} → {t : α} → Member ts t → HList F ts → F t
  | _, _, .head, .cons x _ => x
  | _, _, .tail i, .cons _ xs => valueAt i xs

/-- Assemble the two sides of the actual signature. Recursing on the signature makes the
argument spine compute even when the selected values are free variables. -/
def arguments {α : Type} {F : α → Type} :
    (ts : List α) → (n : Nat) → HList F (ts.take n) → HList F (ts.drop n) → HList F ts
  | [], _, _, _ => .nil
  | _ :: _, 0, _, ws => ws
  | _ :: ts, n + 1, .cons x xs, ws => .cons x (arguments ts n xs ws)

/-- Bind all witness values before entering the validity assumptions. -/
def witnesses :
    (ts : List V.Ty) → (HList M.Val ts → Prop) → Prop
  | [], k => k .nil
  | t :: ts, k => ∀ x : M.Val t, witnesses ts fun xs ↦ k (.cons x xs)

/-- Imply the body from each witness validity in parameter order. -/
def validWitnesses : {ts : List V.Ty} → HList M.Val ts → Prop → Prop
  | [], .nil, q => q
  | t :: _, .cons x xs, q => M.Valid t x → validWitnesses xs q

/-- The witness telescope is a quantifier over the list of witnesses. -/
theorem witnesses_iff : ∀ (ts : List V.Ty) (P : HList M.Val ts → Prop),
    witnesses M ts P ↔ ∀ ws, P ws
  | [], _ => ⟨fun h .nil ↦ h, fun h ↦ h .nil⟩
  | _ :: ts, P => by
    constructor
    · intro h (.cons x xs)
      exact (witnesses_iff ts _).mp (h x) xs
    · intro h x
      exact (witnesses_iff ts _).mpr fun xs ↦ h (.cons x xs)

/-- The validity assumptions of the witnesses are that every witness is valid. -/
theorem validWitnesses_iff : ∀ {ts : List V.Ty} (ws : HList M.Val ts) (P : Prop),
    validWitnesses M ws P ↔ (ws.All M.Valid → P)
  | [], .nil, _ => ⟨fun h _ ↦ h, fun h ↦ h trivial⟩
  | _ :: _, .cons _ xs, _ => by
    constructor
    · exact fun h ⟨hx, hxs⟩ ↦ (validWitnesses_iff xs _).mp (h hx) hxs
    · exact fun h hx ↦ (validWitnesses_iff xs _).mpr fun hxs ↦ h ⟨hx, hxs⟩

/-- Apply a pointwise implication under the universal deployed-input telescope. -/
theorem mapInputs (r : Role) :
    ∀ (ports : List (LTy V)) (P Q : HList (RV M r) ports → Prop),
      (∀ xs, P xs → Q xs) → inputs M r false ports P → inputs M r false ports Q
  | [], _, _, f, hp => f .nil hp
  | port :: rest, _, _, f, hp => by
    by_cases h : r ∈ port.holders
    · simp only [inputs, h, ↓reduceDIte, Bool.false_eq_true, ↓reduceIte] at hp ⊢
      exact fun x hx ↦ mapInputs r rest _ _ (fun xs ↦ f (.cons (hide M r port x) xs)) (hp x hx)
    · simp only [inputs, h, ↓reduceDIte] at hp ⊢
      exact mapInputs r rest _ _ (fun xs ↦ f (.cons (nothing M h) xs)) hp

end ZkcFormal.Written.Goal.Internal
