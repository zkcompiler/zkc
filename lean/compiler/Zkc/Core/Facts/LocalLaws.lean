module

public import Zkc.Core.Facts.Local
public import Zkc.Core.Facts.Learning
public import Zkc.Core.Meaning.Validity

@[expose] public section

/-!
What the check of facts knows of the local operations is true of their meaning.

A value of a function is a value of some type. An operation, by its written form, applied to
valid values of its operands gives valid results: the relation `LocalRun`, which is a function
of the written form and the operands because the written form names the operation. Of it,
`localOpFacts` is lawful: the form of a result, the ranges of arithmetic (TY8), and what the
type of a natural says. What an operation requires is enough for it: where every requirement
holds of its operands' values, it does not stop `undefined`; and every value that a requirement
names beyond the operands (a length, the truth value of a domain row) is there.
-/

namespace Zkc.Core

namespace FactCheck

section
variable {V : Vocabulary} (M : Model V)

/-- A value of some type. -/
abbrev Dyn : Type := Σ τ : V.Ty, M.Val τ

/-- How the check reads a value of a function: a natural or an index as a natural, a truth
value as itself. -/
def localReading : Reading (Dyn M) where
  nat
    | ⟨.nat, n⟩ => some n
    | ⟨.fin _, n⟩ => some n
    | _ => none
  bool
    | ⟨.bool, b⟩ => some b
    | _ => none

/-- A value is valid. -/
def ValidDyn (d : Dyn M) : Prop := M.Valid d.1 d.2

end

section
variable {V : Vocabulary} {M : Model V}

/-- Values of types, as values of some type. -/
def toDyns : {items : List V.Ty} → HList M.Val items → List (Dyn M)
  | [], .nil => []
  | _ :: _, .cons v rest => ⟨_, v⟩ :: toDyns rest

end

section
variable {V : Vocabulary} (M : Model V) {fns : List (FnHeader V)} (table : FnTable M fns)

/-- A local operation with the written form, applied to valid values, gives valid results. -/
def LocalRun (w : LocalRaw V) (args results : List (Dyn M)) : Prop :=
  ∃ (ins res : List V.Ty) (o : LocalOp V fns ins res) (a : HList M.Val ins)
    (r : HList M.Val res), o.print = w ∧ toDyns a = args ∧ toDyns r = results ∧
    a.All M.Valid ∧ r.All M.Valid ∧ localOp M table o a = .done r

end

/-! ## Values of some type -/

section
variable {V : Vocabulary} {M : Model V}

theorem toDyns_length : ∀ {items : List V.Ty} (vs : HList M.Val items),
    (toDyns vs).length = items.length
  | [], .nil => rfl
  | _ :: _, .cons _ vs => by simp [toDyns, toDyns_length vs]

theorem toDyns_inj : ∀ {as bs : List V.Ty} (xs : HList M.Val as) (ys : HList M.Val bs),
    toDyns xs = toDyns ys → as = bs ∧ HEq xs ys
  | [], [], .nil, .nil, _ => ⟨rfl, HEq.rfl⟩
  | [], _ :: _, .nil, .cons _ _, h => by simp [toDyns] at h
  | _ :: _, [], .cons _ _, .nil, h => by simp [toDyns] at h
  | _ :: _, _ :: _, .cons x xs, .cons y ys, h => by
      simp only [toDyns, List.cons.injEq, Sigma.mk.injEq] at h
      obtain ⟨⟨ha, hxy⟩, hrest⟩ := h
      subst ha
      have hxy' := eq_of_heq hxy
      subst hxy'
      obtain ⟨hb, hr⟩ := toDyns_inj xs ys hrest
      subst hb
      cases eq_of_heq hr
      exact ⟨rfl, HEq.rfl⟩

theorem toDyns_valid : ∀ {items : List V.Ty} {vs : HList M.Val items}, vs.All M.Valid →
    ∀ d, d ∈ toDyns vs → ValidDyn M d
  | [], .nil, _, _, m => nomatch m
  | _ :: _, .cons v vs, valid, d, m => by
      simp only [toDyns, List.mem_cons] at m
      rcases m with rfl | m
      · exact (HList.all_cons.mp valid).1
      · exact toDyns_valid (HList.all_cons.mp valid).2 d m

theorem valid_of_toDyns : ∀ {items : List V.Ty} {vs : HList M.Val items},
    (∀ d, d ∈ toDyns vs → ValidDyn M d) → vs.All M.Valid
  | [], .nil, _ => trivial
  | _ :: _, .cons v _, h => HList.all_cons.mpr
      ⟨h ⟨_, v⟩ List.mem_cons_self, valid_of_toDyns fun d m => h d (List.mem_cons_of_mem _ m)⟩

theorem HList.one {α : Type} {F : α → Type} {a : α} :
    ∀ (vs : HList F [a]), ∃ v, vs = .cons v .nil
  | .cons v .nil => ⟨v, rfl⟩

theorem HList.two {α : Type} {F : α → Type} {a b : α} :
    ∀ (vs : HList F [a, b]), ∃ u v, vs = .cons u (.cons v .nil)
  | .cons u (.cons v .nil) => ⟨u, v, rfl⟩

theorem HList.three {α : Type} {F : α → Type} {a b c : α} :
    ∀ (vs : HList F [a, b, c]), ∃ u v w, vs = .cons u (.cons v (.cons w .nil))
  | .cons u (.cons v (.cons w .nil)) => ⟨u, v, w, rfl⟩

end

/-! ## Arithmetic of ranges -/

namespace Range

theorem add_has {a b : Option Range} {x y : Nat} (ha : ∀ r, a = some r → r.Has x)
    (hb : ∀ r, b = some r → r.Has y) : ∀ r, Range.add a b = some r → r.Has (x + y) := by
  intro r e
  cases a with
  | none => simp [Range.add] at e
  | some a =>
      cases b with
      | none => simp [Range.add] at e
      | some b =>
          simp only [Range.add, Option.some.injEq] at e
          subst e
          obtain ⟨la, ua⟩ := ha a rfl
          obtain ⟨lb, ub⟩ := hb b rfl
          refine ⟨by simp only; omega, fun h e => ?_⟩
          rcases a with ⟨alo, _ | ahi⟩ <;> rcases b with ⟨blo, _ | bhi⟩ <;> simp at e
          have := ua ahi rfl
          have := ub bhi rfl
          omega

theorem sub_has {a b : Option Range} {x y : Nat} (ha : ∀ r, a = some r → r.Has x)
    (hb : ∀ r, b = some r → r.Has y) : ∀ r, Range.sub a b = some r → r.Has (x - y) := by
  intro r e
  cases a with
  | none => simp [Range.sub] at e
  | some a =>
      cases b with
      | none => simp [Range.sub] at e
      | some b =>
          simp only [Range.sub, Option.some.injEq] at e
          subst e
          obtain ⟨la, ua⟩ := ha a rfl
          obtain ⟨lb, ub⟩ := hb b rfl
          rcases a with ⟨alo, ahi⟩
          rcases b with ⟨blo, _ | bhi⟩
          · have la : alo ≤ x := la
            have lb : blo ≤ y := lb
            refine ⟨Nat.zero_le _, fun h e => ?_⟩
            cases ahi with
            | none => cases e
            | some ahi =>
                simp only [Option.map_some, Option.some.injEq] at e
                subst e
                have := ua ahi rfl
                omega
          · have la : alo ≤ x := la
            have lb : blo ≤ y := lb
            have hy := ub bhi rfl
            refine ⟨by show alo - bhi ≤ x - y; omega, fun h e => ?_⟩
            cases ahi with
            | none => cases e
            | some ahi =>
                simp only [Option.map_some, Option.some.injEq] at e
                subst e
                have := ua ahi rfl
                omega

theorem mul_has {a b : Option Range} {x y : Nat} (ha : ∀ r, a = some r → r.Has x)
    (hb : ∀ r, b = some r → r.Has y) : ∀ r, Range.mul a b = some r → r.Has (x * y) := by
  intro r e
  cases a with
  | none => simp [Range.mul] at e
  | some a =>
      cases b with
      | none => simp [Range.mul] at e
      | some b =>
          simp only [Range.mul, Option.some.injEq] at e
          subst e
          obtain ⟨la, ua⟩ := ha a rfl
          obtain ⟨lb, ub⟩ := hb b rfl
          refine ⟨Nat.mul_le_mul la lb, fun h e => ?_⟩
          rcases a with ⟨alo, _ | ahi⟩ <;> rcases b with ⟨blo, _ | bhi⟩ <;> simp at e
          subst e
          exact Nat.mul_le_mul (ua ahi rfl) (ub bhi rfl)

theorem div_has {a b : Option Range} {x y : Nat} (ha : ∀ r, a = some r → r.Has x)
    (hb : ∀ r, b = some r → r.Has y) (pos : 1 ≤ y) :
    ∀ r, Range.div a b = some r → r.Has (x / y) := by
  intro r e
  cases a with
  | none => simp [Range.div] at e
  | some a =>
      cases b with
      | none => simp [Range.div] at e
      | some b =>
          simp only [Range.div, Option.some.injEq] at e
          subst e
          obtain ⟨la, ua⟩ := ha a rfl
          obtain ⟨lb, ub⟩ := hb b rfl
          refine ⟨?_, fun h e => ?_⟩
          · cases hbh : b.hi with
            | none => simp
            | some yh =>
                simp only
                have := ub yh hbh
                exact Nat.le_trans (Nat.div_le_div_right la) (Nat.div_le_div_left this pos)
          · cases hah : a.hi with
            | none => rw [hah] at e; cases e
            | some xh =>
                rw [hah] at e
                simp only [Option.map_some, Option.some.injEq] at e
                subst e
                exact Nat.le_trans (Nat.div_le_div_right (ua xh hah))
                  (Nat.div_le_div_left (Nat.max_le.mpr ⟨lb, pos⟩) (by omega))

theorem rem_has {a b : Option Range} {x y : Nat} (ha : ∀ r, a = some r → r.Has x)
    (hb : ∀ r, b = some r → r.Has y) (pos : 1 ≤ y) :
    ∀ r, Range.rem a b = some r → r.Has (x % y) := by
  intro r e
  cases a with
  | none => simp [Range.rem] at e
  | some a =>
      cases b with
      | none => simp [Range.rem] at e
      | some b =>
          simp only [Range.rem, Option.some.injEq] at e
          subst e
          obtain ⟨_, ua⟩ := ha a rfl
          obtain ⟨_, ub⟩ := hb b rfl
          have lt := Nat.mod_lt x (by omega : y > 0)
          have le := Nat.mod_le x y
          refine ⟨Nat.zero_le _, fun h e => ?_⟩
          rcases a with ⟨alo, _ | ahi⟩ <;> rcases b with ⟨blo, _ | bhi⟩ <;>
            simp only [Option.some.injEq, reduceCtorEq] at e
          · subst e
            have := ub bhi rfl
            omega
          · subst e
            have := ua ahi rfl
            omega
          · subst e
            have := ua ahi rfl
            have := ub bhi rfl
            exact Nat.le_min.mpr ⟨by omega, by omega⟩

theorem pow_has {a b : Option Range} {x y : Nat} (ha : ∀ r, a = some r → r.Has x)
    (hb : ∀ r, b = some r → r.Has y) : ∀ r, Range.pow a b = some r → r.Has (x ^ y) := by
  intro r e
  cases a with
  | none => simp [Range.pow] at e
  | some a =>
      cases b with
      | none => simp [Range.pow] at e
      | some b =>
          simp only [Range.pow, Option.some.injEq] at e
          subst e
          obtain ⟨la, ua⟩ := ha a rfl
          obtain ⟨lb, ub⟩ := hb b rfl
          refine ⟨?_, fun h e => ?_⟩
          · simp only
            split
            · next one =>
                exact Nat.le_trans (Nat.pow_le_pow_left la _)
                  (Nat.pow_le_pow_right (by omega) lb)
            · split
              · next zero =>
                  have := ub 0 zero
                  have : y = 0 := by omega
                  subst this
                  simp
              · exact Nat.zero_le _
          · rcases a with ⟨alo, _ | ahi⟩ <;> rcases b with ⟨blo, _ | bhi⟩ <;>
              simp only [Option.some.injEq, reduceCtorEq] at e
            subst e
            have hx := ua ahi rfl
            have hy := ub bhi rfl
            simp only at lb
            cases x with
            | zero =>
                cases y with
                | zero =>
                    have : blo = 0 := by omega
                    subst this
                    exact Nat.le_max_right _ _
                | succ y => simp
            | succ x =>
                exact Nat.le_trans (Nat.le_trans (Nat.pow_le_pow_left hx _)
                  (Nat.pow_le_pow_right (by omega) hy)) (Nat.le_max_left _ _)

end Range

/-! ## The laws -/

theorem beq_decide (x y : Nat) : Nat.beq x y = decide (x = y) := by
  cases h : Nat.beq x y
  · have : ¬ x = y := fun e => by rw [← Nat.beq_eq, h] at e; cases e
    simp [this]
  · have : x = y := by rw [← Nat.beq_eq]; exact h
    simp [this]

theorem blt_decide (x y : Nat) : Nat.blt x y = decide (x < y) := by
  cases h : Nat.blt x y
  · have : ¬ x < y := fun e => by rw [← Nat.blt_eq, h] at e; cases e
    simp [this]
  · have : x < y := by rw [← Nat.blt_eq]; exact h
    simp [this]

section
variable {V : Vocabulary} {M : Model V} {fns : List (FnHeader V)} {table : FnTable M fns}

/-- A local operation is a function of its written form and its operands, when the functions it
may call have distinct keys. -/
theorem localRun_functional (distinct : (fns.map (·.key)).Nodup) {w : LocalRaw V}
    {as rs rs' : List (Dyn M)} (h1 : LocalRun M table w as rs) (h2 : LocalRun M table w as rs') :
    rs = rs' := by
  obtain ⟨ins, res, o, a, r, hp, ha, hr, _, _, run⟩ := h1
  obtain ⟨ins', res', o', a', r', hp', ha', hr', _, _, run'⟩ := h2
  obtain ⟨hi, heq⟩ := toDyns_inj a a' (ha.trans ha'.symm)
  subst hi
  cases eq_of_heq heq
  obtain ⟨hres, hoo⟩ := Sigma.mk.inj (LocalOp.print_injective distinct o o' (hp.trans hp'.symm))
  subst hres
  cases eq_of_heq hoo
  rw [run] at run'
  cases run'
  rw [← hr, ← hr']

/-- How the first result of a local operation reads. -/
theorem localRun_form {w : LocalRaw V} {as rs : List (Dyn M)} {f : ResultForm}
    (hf : localForm w = some f) (h : LocalRun M table w as rs) :
    ∃ r, rs.head? = some r ∧ FormHolds (localReading M) f as r := by
  obtain ⟨ins, res, o, a, r, rfl, rfl, rfl, _, _, run⟩ := h
  cases o with
  | row => simp [LocalOp.print, localForm] at hf
  | call => simp [LocalOp.print, localForm] at hf
  | literal τ data reads =>
      simp only [LocalOp.print] at hf
      have shape : (τ = .bool ∧ data = [0] ∧ f = .truth false) ∨
          (τ = .bool ∧ data = [1] ∧ f = .truth true) := by
        unfold localForm at hf
        split at hf <;> simp_all
      simp only [localOp, Process.done.injEq] at run
      subst run
      refine ⟨_, rfl, ?_⟩
      have literal := Ty.read_readLiteral M _ _ reads
      rcases shape with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
      · simp [Ty.read] at literal
        simp only [FormHolds, localReading]
        rw [← literal]
      · simp [Ty.read] at literal
        simp only [FormHolds, localReading]
        rw [← literal]
  | owned op =>
      cases op <;> simp [LocalOp.print, OwnedOp.name, localForm] at hf <;> subst hf
      case natAdd =>
        obtain ⟨x, y, rfl⟩ := HList.two a
        simp only [localOp, ownedOp, Process.done.injEq] at run
        subst run
        exact ⟨_, rfl, _, _, x, y, rfl, rfl, rfl, rfl⟩
      case natSub =>
        obtain ⟨x, y, rfl⟩ := HList.two a
        simp only [localOp, ownedOp] at run
        split at run
        · next le =>
            simp only [Process.done.injEq] at run
            subst run
            exact ⟨_, rfl, _, _, x, y, rfl, rfl, rfl, le, rfl⟩
        · cases run
      case natEqual =>
        obtain ⟨x, y, rfl⟩ := HList.two a
        simp only [localOp, ownedOp, Process.done.injEq] at run
        subst run
        refine ⟨_, rfl, _, _, x, y, rfl, rfl, rfl, ?_⟩
        simp only [localReading, Option.some.injEq]
        exact beq_decide x y
      case natLess =>
        obtain ⟨x, y, rfl⟩ := HList.two a
        simp only [localOp, ownedOp, Process.done.injEq] at run
        subst run
        refine ⟨_, rfl, _, _, x, y, rfl, rfl, rfl, ?_⟩
        simp only [localReading, Option.some.injEq]
        exact blt_decide x y
      case boolAnd =>
        obtain ⟨x, y, rfl⟩ := HList.two a
        simp only [localOp, ownedOp, Process.done.injEq] at run
        subst run
        exact ⟨_, rfl, _, _, x, y, rfl, rfl, rfl, rfl⟩
      case boolOr =>
        obtain ⟨x, y, rfl⟩ := HList.two a
        simp only [localOp, ownedOp, Process.done.injEq] at run
        subst run
        exact ⟨_, rfl, _, _, x, y, rfl, rfl, rfl, rfl⟩
      case boolNot =>
        obtain ⟨x, rfl⟩ := HList.one a
        simp only [localOp, ownedOp, Process.done.injEq] at run
        subst run
        exact ⟨_, rfl, _, x, rfl, rfl, rfl⟩

theorem onTwo_has {f : Option Range → Option Range → Option Range} {known : List (Option Range)}
    {x y z : Nat}
    (sound : ∀ ka kb, (∀ r, ka = some r → r.Has x) → (∀ r, kb = some r → r.Has y) →
      ∀ r, f ka kb = some r → r.Has z)
    (hx : ∀ r, known[0]? = some (some r) → r.Has x)
    (hy : ∀ r, known[1]? = some (some r) → r.Has y) :
    ∀ (i : Nat) (r : Range), (Range.onTwo f known)[i]? = some (some r) → i = 0 ∧ r.Has z := by
  intro i r e
  match known, hx, hy with
  | [ka, kb], hx, hy =>
      simp only [Range.onTwo] at e
      cases i with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at e
          exact ⟨rfl, sound ka kb (fun r h => hx r (by simp [h])) (fun r h => hy r (by simp [h]))
            r e⟩
      | succ i => simp at e
  | [], _, _ => simp [Range.onTwo] at e
  | [_], _, _ => simp [Range.onTwo] at e
  | _ :: _ :: _ :: _, _, _ => simp [Range.onTwo] at e

theorem onOne_has {known : List (Option Range)} {x : Nat}
    (hx : ∀ r, known[0]? = some (some r) → r.Has x) :
    ∀ (i : Nat) (r : Range), (Range.onOne known)[i]? = some (some r) → i = 0 ∧ r.Has x := by
  intro i r e
  match known, hx with
  | [ka], hx =>
      simp only [Range.onOne] at e
      cases i with
      | zero => exact ⟨rfl, hx r (by simpa using e)⟩
      | succ i => simp at e
  | [], _ => simp [Range.onOne] at e
  | _ :: _ :: _, _ => simp [Range.onOne] at e

theorem seqLength_has {item : V.Ty} {size : Option Nat} {len : Nat}
    (hlen : ∀ n, size = some n → len = n) {known : List (Option Range)} {i : Nat} {r : Range}
    (e : (ownedRanges .seqLength [.seq item size] known)[i]? = some (some r)) :
    i = 0 ∧ r.Has len := by
  cases size with
  | none =>
      simp only [ownedRanges] at e
      cases i with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at e
          subst e
          exact ⟨rfl, Nat.zero_le _, fun _ e => nomatch e⟩
      | succ i => simp at e
  | some size =>
      simp only [ownedRanges] at e
      cases i with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at e
          subst e
          exact ⟨rfl, Range.has_point.mpr (hlen size rfl)⟩
      | succ i => simp at e

/-- The ranges of the results of a local operation hold where those of its operands do. -/
theorem localRun_ranges {w : LocalRaw V} {as rs : List (Dyn M)} (known : List (Option Range))
    (h : LocalRun M table w as rs)
    (hk : ∀ (i : Nat) (r : Range), known[i]? = some (some r) →
      ∃ v n, as[i]? = some v ∧ (localReading M).nat v = some n ∧ r.Has n) :
    ∀ (i : Nat) (r : Range), ((localOpFacts V).ranges w known)[i]? = some (some r) →
      ∃ v n, rs[i]? = some v ∧ (localReading M).nat v = some n ∧ r.Has n := by
  obtain ⟨ins, res, o, a, r, rfl, rfl, rfl, va, _, run⟩ := h
  have at_ : ∀ (j : Nat) (x : Nat), (localReading M).nat ((toDyns a)[j]?.getD ⟨.nat, 0⟩) = some x →
      j < (toDyns a).length → ∀ r, known[j]? = some (some r) → r.Has x := by
    intro j x hx lt r e
    obtain ⟨v, n, hv, hn, has⟩ := hk j r e
    rw [List.getElem?_eq_getElem lt] at hv hx
    simp only [Option.getD_some] at hx
    cases hv
    rw [hx] at hn
    cases hn
    exact has
  intro i rr e
  cases o with
  | row => simp [LocalOp.print, localOpFacts] at e
  | call => simp [LocalOp.print, localOpFacts] at e
  | literal τ data reads =>
      simp only [LocalOp.print, localOpFacts] at e
      simp only [localOp, Process.done.injEq] at run
      subst run
      have literal := Ty.read_readLiteral M _ _ reads
      cases τ <;> rcases data with _ | ⟨n, _ | _⟩ <;> simp [literalRanges] at e
      all_goals
        cases i with
        | succ i => simp at e
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at e
          subst e
          refine ⟨_, n, rfl, ?_, Range.has_point.mpr rfl⟩
          simp only [Ty.read] at literal
          first
            | (simp at literal; simp only [localReading]; rw [← literal])
            | (split at literal
               · simp at literal; simp only [localReading]; rw [← literal]
               · cases literal)
  | owned op =>
      cases op <;> simp [LocalOp.print, OwnedOp.name, localOpFacts, ownedRanges] at e
      case natAdd =>
        obtain ⟨x, y, rfl⟩ := HList.two a
        simp only [localOp, ownedOp, Process.done.injEq] at run
        subst run
        obtain ⟨rfl, has⟩ := onTwo_has (fun _ _ ha hb => Range.add_has ha hb)
          (at_ 0 x rfl (by simp [toDyns]))
          (at_ 1 y rfl (by simp [toDyns])) i rr e
        exact ⟨_, x + y, rfl, rfl, has⟩
      case natSub =>
        obtain ⟨x, y, rfl⟩ := HList.two a
        simp only [localOp, ownedOp] at run
        split at run
        · simp only [Process.done.injEq] at run
          subst run
          obtain ⟨rfl, has⟩ := onTwo_has (fun _ _ ha hb => Range.sub_has ha hb)
            (at_ 0 x rfl (by simp [toDyns]))
            (at_ 1 y rfl (by simp [toDyns])) i rr e
          exact ⟨_, x - y, rfl, rfl, has⟩
        · cases run
      case natMul =>
        obtain ⟨x, y, rfl⟩ := HList.two a
        simp only [localOp, ownedOp, Process.done.injEq] at run
        subst run
        obtain ⟨rfl, has⟩ := onTwo_has (fun _ _ ha hb => Range.mul_has ha hb)
          (at_ 0 x rfl (by simp [toDyns]))
          (at_ 1 y rfl (by simp [toDyns])) i rr e
        exact ⟨_, x * y, rfl, rfl, has⟩
      case natDiv =>
        obtain ⟨x, y, rfl⟩ := HList.two a
        simp only [localOp, ownedOp] at run
        split at run
        · next pos =>
            simp only [Process.done.injEq] at run
            subst run
            obtain ⟨rfl, has⟩ := onTwo_has (fun ka kb ha hb => Range.div_has ha hb pos)
              (at_ 0 x rfl (by simp [toDyns])) (at_ 1 y rfl (by simp [toDyns])) i rr e
            exact ⟨_, x / y, rfl, rfl, has⟩
        · cases run
      case natRem =>
        obtain ⟨x, y, rfl⟩ := HList.two a
        simp only [localOp, ownedOp] at run
        split at run
        · next pos =>
            simp only [Process.done.injEq] at run
            subst run
            obtain ⟨rfl, has⟩ := onTwo_has (fun ka kb ha hb => Range.rem_has ha hb pos)
              (at_ 0 x rfl (by simp [toDyns])) (at_ 1 y rfl (by simp [toDyns])) i rr e
            exact ⟨_, x % y, rfl, rfl, has⟩
        · cases run
      case natPow =>
        obtain ⟨x, y, rfl⟩ := HList.two a
        simp only [localOp, ownedOp, Process.done.injEq] at run
        subst run
        obtain ⟨rfl, has⟩ := onTwo_has (fun _ _ ha hb => Range.pow_has ha hb)
          (at_ 0 x rfl (by simp [toDyns]))
          (at_ 1 y rfl (by simp [toDyns])) i rr e
        exact ⟨_, x ^ y, rfl, rfl, has⟩
      case seqLength =>
        obtain ⟨xs, rfl⟩ := HList.one a
        simp only [localOp, ownedOp, Process.done.injEq] at run
        subst run
        obtain ⟨rfl, has⟩ := seqLength_has ((HList.all_cons.mp va).1).2 e
        exact ⟨_, _, rfl, rfl, has⟩
      case natBelow bound =>
        obtain ⟨x, rfl⟩ := HList.one a
        simp only [localOp, ownedOp] at run
        split at run
        · simp only [Process.done.injEq] at run
          subst run
          obtain ⟨rfl, has⟩ := onOne_has (at_ 0 x rfl (by simp [toDyns])) i rr e
          exact ⟨_, x, rfl, rfl, has⟩
        · cases run
      case finToNat bound =>
        obtain ⟨x, rfl⟩ := HList.one a
        simp only [localOp, ownedOp, Process.done.injEq] at run
        subst run
        obtain ⟨rfl, has⟩ := onOne_has (at_ 0 x rfl (by simp [toDyns])) i rr e
        exact ⟨_, x, rfl, rfl, has⟩
      case finWiden bound wider le =>
        obtain ⟨x, rfl⟩ := HList.one a
        simp only [localOp, ownedOp, Process.done.injEq] at run
        subst run
        obtain ⟨rfl, has⟩ := onOne_has (at_ 0 x rfl (by simp [toDyns])) i rr e
        exact ⟨_, x, rfl, rfl, has⟩

/-- What `OpFacts` says of the local operations is true of their meaning. -/
theorem localOpFacts_lawful (distinct : (fns.map (·.key)).Nodup) :
    OpFacts.Lawful (localOpFacts V) (localReading M) (LocalRun M table) where
  functional _ _ _ _ h1 h2 := localRun_functional distinct h1 h2
  form _ _ _ _ hf h := localRun_form hf h
  ranges _ _ _ known h hk := localRun_ranges known h hk

/-- No valid value has a type that the local dialect says has no value. -/
theorem localNoValue_valid {τ : V.Ty} (v : M.Val τ) (valid : M.Valid τ v) :
    (localFactRules V fns).noValue τ = false :=
  Ty.noValue_of_valid τ v valid

/-- What the type of a natural says of it holds of its valid values. -/
theorem localRange_has {τ : V.Ty} {r : Range} (h : localRange τ = some r) (v : M.Val τ)
    (valid : M.Valid τ v) : ∃ n, (localReading M).nat ⟨τ, v⟩ = some n ∧ r.Has n := by
  cases τ with
  | nat =>
      simp only [localRange, Option.some.injEq] at h
      subst h
      exact ⟨v, rfl, Nat.zero_le _, fun _ e => nomatch e⟩
  | fin bound =>
      simp only [localRange, Option.some.injEq] at h
      subst h
      have hv : (show Nat from v) < bound := valid
      refine ⟨v, rfl, ?_⟩
      by_cases b0 : bound = 0
      · subst b0
        exact absurd hv (Nat.not_lt_zero _)
      · simp only [b0, ↓reduceIte]
        exact ⟨Nat.zero_le _, fun h e => by simp at e; subst e; exact Nat.le_sub_one_of_lt hv⟩
  | _ => simp [localRange] at h

/-! ## What operations require -/

theorem atPositions_append {α : Type} (xs : List α) :
    ∀ (ps qs : List Nat), atPositions xs (ps ++ qs) =
      (atPositions xs ps).bind fun as => (atPositions xs qs).map fun bs => as ++ bs
  | [], qs => by simp [atPositions]
  | p :: ps, qs => by
      simp only [List.cons_append, atPositions, atPositions_append xs ps qs]
      cases xs[p]? <;> cases atPositions xs ps <;> simp
      cases atPositions xs qs <;> simp

theorem atPositions_range {α : Type} (xs : List α) :
    ∀ n, n ≤ xs.length → atPositions xs (List.range n) = some (xs.take n)
  | 0, _ => by simp [atPositions]
  | n + 1, le => by
      rw [List.range_succ, atPositions_append, atPositions_range xs n (by omega)]
      simp only [atPositions, List.getElem?_eq_getElem (by omega : n < xs.length),
        Option.bind_some, Option.map_some, Option.some.injEq]
      rw [List.take_add_one, List.getElem?_eq_getElem (by omega : n < xs.length)]
      rfl

theorem DenotesAll.one {Raw : Type} {Run : Raw → List (Dyn M) → List (Dyn M) → Prop}
    {args : List (Dyn M)} {o : Operand Raw} {vs : List (Dyn M)} (h : DenotesAll Run args [o] vs) :
    ∃ v, vs = [v] ∧ o.Denotes Run args v := by
  match vs, h with
  | [v], ⟨d, _⟩ => exact ⟨v, rfl, d⟩

theorem DenotesAll.two {Raw : Type} {Run : Raw → List (Dyn M) → List (Dyn M) → Prop}
    {args : List (Dyn M)} {o o' : Operand Raw} {vs : List (Dyn M)}
    (h : DenotesAll Run args [o, o'] vs) :
    ∃ v v', vs = [v, v'] ∧ o.Denotes Run args v ∧ o'.Denotes Run args v' := by
  match vs, h with
  | [v, v'], ⟨d, d', _⟩ => exact ⟨v, v', rfl, d, d'⟩

/-- Applied to a sequence, its length. -/
theorem localRun_length {item : V.Ty} {size : Option Nat} {xs : M.Val (.seq item size)}
    {rs : List (Dyn M)}
    (h : LocalRun M table (.owned .seqLength [.seq item size] []) [⟨.seq item size, xs⟩] rs) :
    rs = [⟨.nat, (xs : List (M.Val item)).length⟩] := by
  obtain ⟨ins, res, o, a, r, hp, ha, rfl, _, _, run⟩ := h
  cases o with
  | row => simp [LocalOp.print] at hp
  | literal => simp [LocalOp.print] at hp
  | call => simp [LocalOp.print] at hp
  | owned op =>
      cases op <;> simp [LocalOp.print, OwnedOp.name] at hp
      obtain ⟨rfl, rfl⟩ := hp
      obtain ⟨ys, rfl⟩ := HList.one a
      simp only [toDyns, List.cons.injEq, Sigma.mk.injEq, heq_eq_eq, and_true, true_and] at ha
      subst ha
      simp only [localOp, ownedOp, Process.done.injEq] at run
      subst run
      rfl

theorem localRun_length_intro {item : V.Ty} {size : Option Nat}
    (free : Ty.isLinear V item = false) (xs : M.Val (.seq item size)) (valid : M.Valid _ xs) :
    LocalRun M table (.owned .seqLength [.seq item size] []) [⟨.seq item size, xs⟩]
      [⟨.nat, (xs : List (M.Val item)).length⟩] :=
  ⟨_, _, .owned (.seqLength item size free), .cons xs .nil,
    .cons (xs : List (M.Val item)).length .nil,
    rfl, rfl, rfl, HList.all_cons.mpr ⟨valid, trivial⟩, HList.all_cons.mpr ⟨trivial, trivial⟩, rfl⟩

/-- The domain row of a restricted row, at its operands, gives whether they are in its
domain. -/
theorem localRun_domain_intro {key domain : V.RowKey} {sig : RowSignature V.TypeKey V.RowKey}
    (known : V.row key = some sig) (kind : sig.kind = .restricted domain)
    (a : HList M.Val sig.ins) (va : a.All M.Valid) :
    LocalRun M table (.row domain) (toDyns a) [⟨.bool, M.inDomain key sig known a⟩] := by
  refine ⟨_, _, .row domain ⟨sig.ins, [.bool], .pure⟩ (V.decided key sig domain known kind), a,
    .cons (M.inDomain key sig known a) .nil, rfl, rfl, rfl, va,
    HList.all_cons.mpr ⟨trivial, trivial⟩, ?_⟩
  simp only [localOp]
  rw [M.decides key sig known domain kind a]

/-- What the domain row of a restricted row gives at its operands. -/
theorem localRun_domain {key domain : V.RowKey} {sig : RowSignature V.TypeKey V.RowKey}
    (known : V.row key = some sig) (kind : sig.kind = .restricted domain)
    (a : HList M.Val sig.ins) {rs : List (Dyn M)}
    (h : LocalRun M table (.row domain) (toDyns a) rs) :
    rs = [⟨.bool, M.inDomain key sig known a⟩] := by
  have decides := M.decides key sig known domain kind a
  obtain ⟨ins', res', o, a', r, hp, ha, rfl, _, _, run⟩ := h
  cases o with
  | owned => simp [LocalOp.print] at hp
  | literal => simp [LocalOp.print] at hp
  | call => simp [LocalOp.print] at hp
  | row domain' sig' known' =>
      simp only [LocalOp.print, LocalRaw.row.injEq] at hp
      subst hp
      have : sig' = ⟨sig.ins, [.bool], .pure⟩ :=
        Option.some.inj (known'.symm.trans (V.decided key sig _ known kind))
      subst this
      obtain ⟨_, heq⟩ := toDyns_inj a' a ha
      have ha' : a' = a := eq_of_heq heq
      subst ha'
      simp only [localOp] at run
      rw [decides] at run
      simp only [Process.done.injEq] at run
      subst run
      rfl

theorem stops_of_halt {α : Type} : ∀ (p : Local α), (∀ h, p = .halt h → h ≠ .undefined) →
    p.Stops (· ≠ .undefined)
  | .done _, _ => trivial
  | .halt h, hh => hh h rfl
  | .call op _, _ => nomatch op

/-- A row, at operands where what it requires holds, gives its outputs. -/
theorem row_defined (key : V.RowKey) (sig : RowSignature V.TypeKey V.RowKey)
    (known : V.row key = some sig) (a : HList M.Val sig.ins)
    (holds : ∀ req, req ∈ rowRequires key →
      req.Holds (LocalRun M table) (localReading M) (toDyns a)) :
    ∃ outs, M.apply key sig known a = some outs := by
  have defined := M.defined key sig known a
  suffices h : M.inDomain key sig known a = true by
    rw [h] at defined
    exact Option.isSome_iff_exists.mp defined
  cases hk : sig.kind with
  | pure => exact M.total key sig known a hk
  | restricted domain =>
      have req : rowRequires key =
          [.holds (.apply (.row domain) (List.range sig.ins.length))] := by
        simp only [rowRequires, known, hk]
      obtain ⟨vs, d, rel⟩ := holds (.holds (.apply (.row domain) (List.range sig.ins.length)))
        (by rw [req]; simp)
      obtain ⟨v, rfl, hv⟩ := DenotesAll.one d
      obtain ⟨as, rs, hpos, run, head⟩ := hv
      rw [← toDyns_length a, atPositions_range _ _ (Nat.le_refl _), List.take_length,
        Option.some.injEq] at hpos
      subst hpos
      have := localRun_domain known hk a run
      subst this
      simp only [List.head?_cons, Option.some.injEq] at head
      subst head
      simpa [Requirement.Relation, localReading] using rel

/-! ### Each operation with a domain -/

/-- What a requirement says, of values that its operands name. -/
abbrev Holds (args : List (Dyn M)) (req : Requirement (LocalRaw V)) : Prop :=
  req.Holds (LocalRun M table) (localReading M) args

theorem holds_args {args : List (Dyn M)} {i j : Nat} {req : Requirement (LocalRaw V)}
    {u v : Dyn M} (hu : args[i]? = some u) (hv : args[j]? = some v)
    (ops : req.operands = [.arg i, .arg j]) (h : Holds (table := table) args req) :
    req.Relation (localReading M) [u, v] := by
  obtain ⟨vs, d, rel⟩ := h
  rw [ops] at d
  obtain ⟨u', v', rfl, d1, d2⟩ := DenotesAll.two d
  simp only [Operand.Denotes] at d1 d2
  rw [hu] at d1
  rw [hv] at d2
  cases d1
  cases d2
  exact rel

theorem holds_arg {args : List (Dyn M)} {i : Nat} {req : Requirement (LocalRaw V)}
    {u : Dyn M} (hu : args[i]? = some u) (ops : req.operands = [.arg i])
    (h : Holds (table := table) args req) : req.Relation (localReading M) [u] := by
  obtain ⟨vs, d, rel⟩ := h
  rw [ops] at d
  obtain ⟨u', rfl, d1⟩ := DenotesAll.one d
  simp only [Operand.Denotes] at d1
  rw [hu] at d1
  cases d1
  exact rel

/-- The value of the length of the first operand, as a requirement names it. -/
theorem denotes_length {item : V.Ty} {size : Option Nat} {xs : M.Val (.seq item size)}
    {rest : List (Dyn M)} {v : Dyn M}
    (h : (Operand.apply (lengthOfType (.seq item size)) [0] : Operand (LocalRaw V)).Denotes
      (LocalRun M table) (⟨.seq item size, xs⟩ :: rest) v) :
    v = ⟨.nat, (xs : List (M.Val item)).length⟩ := by
  obtain ⟨as, rs, hpos, run, head⟩ := h
  simp only [atPositions, List.getElem?_cons_zero, Option.some.injEq] at hpos
  subst hpos
  rw [localRun_length run] at head
  simp only [List.head?_cons, Option.some.injEq] at head
  exact head.symm

theorem natSub_defined (x y : Nat)
    (holds : ∀ req, req ∈ ownedRequires (V := V) .natSub [] →
      Holds (table := table) [⟨.nat, x⟩, ⟨.nat, y⟩] req) :
    ∀ h, ownedOp M (.natSub (V := V)) (.cons x (.cons y .nil)) = .halt h → h ≠ .undefined := by
  intro h e
  have le := holds_args (u := ⟨.nat, y⟩) (v := ⟨.nat, x⟩) rfl rfl rfl
    (holds (.le (.arg 1) (.arg 0)) (by simp [ownedRequires])) y x rfl rfl
  simp [ownedOp, le] at e

theorem natDiv_defined (x y : Nat)
    (holds : ∀ req, req ∈ ownedRequires (V := V) .natDiv [] →
      Holds (table := table) [⟨.nat, x⟩, ⟨.nat, y⟩] req) :
    ∀ h, ownedOp M (.natDiv (V := V)) (.cons x (.cons y .nil)) = .halt h → h ≠ .undefined := by
  intro h e
  have pos := holds_arg (u := ⟨.nat, y⟩) rfl rfl
    (holds (.atLeast (.arg 1) 1) (by simp [ownedRequires])) y rfl
  simp [ownedOp, show 1 ≤ y from pos] at e

theorem natRem_defined (x y : Nat)
    (holds : ∀ req, req ∈ ownedRequires (V := V) .natRem [] →
      Holds (table := table) [⟨.nat, x⟩, ⟨.nat, y⟩] req) :
    ∀ h, ownedOp M (.natRem (V := V)) (.cons x (.cons y .nil)) = .halt h → h ≠ .undefined := by
  intro h e
  have pos := holds_arg (u := ⟨.nat, y⟩) rfl rfl
    (holds (.atLeast (.arg 1) 1) (by simp [ownedRequires])) y rfl
  simp [ownedOp, show 1 ≤ y from pos] at e

theorem natBelow_defined (bound n : Nat)
    (holds : ∀ req, req ∈ ownedRequires (V := V) .natBelow [.fin bound] →
      Holds (table := table) [⟨.nat, n⟩] req) :
    ∀ h, ownedOp M (.natBelow (V := V) bound) (.cons n .nil) = .halt h → h ≠ .undefined := by
  intro h e
  have lt := holds_arg (u := ⟨.nat, n⟩) rfl rfl
    (holds (.below (.arg 0) bound) (by simp [ownedRequires])) n rfl
  simp [ownedOp, show n < bound from lt] at e

theorem seqAt_defined {item : V.Ty} {size : Option Nat} (free : Ty.isLinear V item = false)
    (xs : M.Val (.seq item size)) (i : Nat) (valid : M.Valid _ xs)
    (holds : ∀ req, req ∈ ownedRequires .seqAt [.seq item size] →
      Holds (table := table) [⟨.seq item size, xs⟩, ⟨.nat, i⟩] req) :
    ∀ h, ownedOp M (.seqAt item size free) (.cons xs (.cons i .nil)) = .halt h →
      h ≠ .undefined := by
  intro h e
  have lt : i < (xs : List (M.Val item)).length := by
    cases size with
    | some size =>
        have := holds_arg (u := ⟨.nat, i⟩) rfl rfl
          (holds (.below (.arg 1) size) (by simp [ownedRequires])) i rfl
        rw [valid.2 size rfl]
        exact this
    | none =>
        obtain ⟨vs, d, rel⟩ := holds (.lt (.arg 1) (.apply (lengthOfType (.seq item none)) [0]))
          (by simp [ownedRequires])
        obtain ⟨u, v, rfl, d1, d2⟩ := DenotesAll.two d
        simp only [Operand.Denotes, List.getElem?_cons_succ, List.getElem?_cons_zero,
          Option.some.injEq] at d1
        subst d1
        rw [denotes_length d2] at rel
        exact rel i _ rfl rfl
  simp only [ownedOp] at e
  split at e
  · cases e
  · next none =>
      rw [List.getElem?_eq_getElem lt] at none
      cases none

theorem seqSlice_defined {item : V.Ty} {size result : Option Nat}
    (free : Ty.isLinear V item = false) (xs : M.Val (.seq item size)) (first second : Nat)
    (holds : ∀ req, req ∈ ownedRequires .seqSlice [.seq item size, .seq item result] →
      Holds (table := table) [⟨.seq item size, xs⟩, ⟨.nat, first⟩, ⟨.nat, second⟩] req) :
    ∀ h, ownedOp M (.seqSlice item size result free)
      (.cons xs (.cons first (.cons second .nil))) = .halt h → h ≠ .undefined := by
  intro h e
  have ordered := holds_args (u := ⟨.nat, first⟩) (v := ⟨.nat, second⟩) rfl rfl rfl
    (holds (.le (.arg 1) (.arg 2)) (by simp [ownedRequires])) first second rfl rfl
  have within : second ≤ (xs : List (M.Val item)).length := by
    obtain ⟨vs, d, rel⟩ := holds (.le (.arg 2) (.apply (lengthOfType (.seq item size)) [0]))
      (by simp [ownedRequires])
    obtain ⟨u, v, rfl, d1, d2⟩ := DenotesAll.two d
    simp only [Operand.Denotes, List.getElem?_cons_succ, List.getElem?_cons_zero,
      Option.some.injEq] at d1
    subst d1
    rw [denotes_length d2] at rel
    exact rel second _ rfl rfl
  have fits : fitsSize result (second - first) = true := by
    cases result with
    | none => rfl
    | some count =>
        have := holds_args (u := ⟨.nat, second⟩) (v := ⟨.nat, first⟩) rfl rfl rfl
          (holds (.difference (.arg 2) (.arg 1) count) (by simp [ownedRequires]))
          second first rfl rfl
        simp [fitsSize, this]
  simp only [ownedOp] at e
  split at e
  · cases e
  · next outside => exact (outside ⟨ordered, within, fits⟩).elim

theorem seqSized_defined {item : V.Ty} {size : Nat} {free : Ty.isLinear V item = false}
    (xs : M.Val (.seq item none))
    (holds : ∀ req, req ∈ ownedRequires .seqSized [.seq item (some size)] →
      Holds (table := table) [⟨.seq item none, xs⟩] req) :
    ∀ h, ownedOp M (.seqSized item size free) (.cons xs .nil) = .halt h → h ≠ .undefined := by
  intro h e
  have length : (xs : List (M.Val item)).length = size := by
    obtain ⟨vs, d, rel⟩ := holds
      (.exactly (.apply (lengthOfType (.seq item none)) [0]) size) (by simp [ownedRequires])
    obtain ⟨u, rfl, d1⟩ := DenotesAll.one d
    rw [denotes_length d1] at rel
    exact rel _ rfl
  simp [ownedOp, length] at e

/-- A local operation, applied to valid operands at whose values every requirement of its
written form holds, does not stop `undefined`, when the functions that it may call do not. -/
theorem localOp_defined
    (safe : ∀ hdr (callee : Var fns hdr) (args : HList M.Val hdr.ins), args.All M.Valid →
      (table hdr callee args).Stops (· ≠ .undefined))
    {ins res : List V.Ty} (o : LocalOp V fns ins res) (a : HList M.Val ins)
    (va : a.All M.Valid)
    (holds : ∀ req, req ∈ (localOpFacts V).requires o.print →
      Holds (table := table) (toDyns a) req) :
    (localOp M table o a).Stops (· ≠ .undefined) := by
  cases o with
  | literal => exact trivial
  | call callee => exact safe _ callee a va
  | row key sig known =>
      obtain ⟨outs, h⟩ := row_defined key sig known a (fun req m => holds req m)
      simp only [localOp, h]
      exact trivial
  | owned op =>
      apply stops_of_halt
      intro h e
      simp only [localOp] at e
      have hreq : ∀ req, req ∈ ownedRequires op.name.1 op.name.2.1 →
          Holds (table := table) (toDyns a) req := fun req m => holds req m
      clear holds
      cases op
      case natSub =>
        obtain ⟨x, y, rfl⟩ := HList.two a
        exact natSub_defined x y hreq h e
      case natDiv =>
        obtain ⟨x, y, rfl⟩ := HList.two a
        exact natDiv_defined x y hreq h e
      case natRem =>
        obtain ⟨x, y, rfl⟩ := HList.two a
        exact natRem_defined x y hreq h e
      case natBelow =>
        obtain ⟨n, rfl⟩ := HList.one a
        exact natBelow_defined _ n hreq h e
      case seqAt =>
        obtain ⟨xs, i, rfl⟩ := HList.two a
        exact seqAt_defined _ xs i (HList.all_cons.mp va).1 hreq h e
      case seqSlice =>
        obtain ⟨xs, first, second, rfl⟩ := HList.three a
        exact seqSlice_defined _ xs first second hreq h e
      case seqSized =>
        obtain ⟨xs, rfl⟩ := HList.one a
        exact seqSized_defined xs hreq h e
      all_goals first
        | (obtain ⟨x, y, z, rfl⟩ := HList.three a; simp [ownedOp] at e)
        | (obtain ⟨x, y, rfl⟩ := HList.two a; simp [ownedOp] at e)
        | (obtain ⟨x, rfl⟩ := HList.one a; simp [ownedOp] at e)
        | simp [ownedOp] at e

/-- Every value that a requirement of a local operation names beyond its operands is there, at
valid operands: one value, given by its written operation. -/
theorem localRequires_runs {ins res : List V.Ty} (o : LocalOp V fns ins res)
    (a : HList M.Val ins) (va : a.All M.Valid) :
    ∀ req, req ∈ (localOpFacts V).requires o.print → ∀ op, op ∈ req.operands → ∀ w ps,
      op = .apply w ps → ∃ as rs, atPositions (toDyns a) ps = some as ∧
        LocalRun M table w as rs ∧ rs.length = 1 := by
  intro req m op mo w ps e
  subst e
  cases o with
  | literal => simp [LocalOp.print, localOpFacts] at m
  | call => simp [LocalOp.print, localOpFacts] at m
  | row key sig known =>
      simp only [LocalOp.print, localOpFacts, rowRequires, known] at m
      split at m
      · simp at m
      · next domain hk =>
          simp only [List.mem_singleton] at m
          subst m
          simp only [Requirement.operands, List.mem_singleton, Operand.apply.injEq] at mo
          obtain ⟨rfl, rfl⟩ := mo
          refine ⟨toDyns a, _, ?_, localRun_domain_intro known hk a va, rfl⟩
          rw [← toDyns_length a, atPositions_range _ _ (Nat.le_refl _), List.take_length]
  | owned op =>
      simp only [LocalOp.print, localOpFacts] at m
      cases op
      case seqAt =>
        obtain ⟨xs, i, rfl⟩ := HList.two a
        rename_i size _
        cases size <;> simp [OwnedOp.name, ownedRequires] at m <;> subst m <;>
          simp [Requirement.operands] at mo
        obtain ⟨rfl, rfl⟩ := mo
        exact ⟨_, _, rfl, localRun_length_intro ‹_› xs (HList.all_cons.mp va).1, rfl⟩
      case seqSlice =>
        obtain ⟨xs, first, second, rfl⟩ := HList.three a
        rename_i result _
        cases result <;> simp [OwnedOp.name, ownedRequires] at m <;>
          rcases m with rfl | rfl | rfl <;> simp [Requirement.operands] at mo
        all_goals
          obtain ⟨rfl, rfl⟩ := mo
          exact ⟨_, _, rfl, localRun_length_intro ‹_› xs (HList.all_cons.mp va).1, rfl⟩
      case seqSized item _ free =>
        obtain ⟨xs, rfl⟩ := HList.one a
        simp [OwnedOp.name, ownedRequires] at m
        subst m
        simp [Requirement.operands] at mo
        obtain ⟨rfl, rfl⟩ := mo
        exact ⟨_, _, rfl, localRun_length_intro free xs (HList.all_cons.mp va).1, rfl⟩
      all_goals simp [OwnedOp.name, ownedRequires] at m
      all_goals subst m
      all_goals simp [Requirement.operands] at mo

end

end FactCheck

end Zkc.Core
