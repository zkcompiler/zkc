module

public import Zkc.Core.Facts.Local
public import Zkc.Core.Facts.Theorems
public import Zkc.Core.Meaning.Validity
public import Zkc.Core.Meaning.Stops

@[expose] public section

/-!
The laws of the function dialect, and the soundness of the check of facts for a function.

A value of a function is a value of some type. An operation, by its written form, applied to
valid values of its operands gives valid results: the relation `LocalRun`, which is a function
of the written form and the operands because the written form names the operation. Of it, what
the analysis knows of the written operations is true: the form of a result, the ranges of
arithmetic (TY8), and what the type of a natural says. What an operation requires is enough for
it: where every requirement holds of its operands' values, it does not stop `undefined`; and
every value that a requirement names beyond the operands (a length, the truth value of a domain
row) is there.

A written form gives results on operands when it is the printed form of a local operation that
returns those results on those operands (`LocalReturns`), whatever the values, valid or not: the
law `computes` of the value form is for every value, and so is the law `commutative`, since the
meaning of each operation that commutes is symmetric for all values of its operands. Against
callees with distinct keys, of which those whose headers say that they cannot stop stop only
`undefined`, the local operations that are values satisfy the laws of the value form
(`localFactRules_binding`); following, which decides two operations by their printed forms, is
lawful over headers with distinct keys (`localSkelRules_lawful`).

The callees that a statement about a function is made against (`Callees`): distinct keys, never
`undefined` on valid inputs, valid results, and only `undefined` as a stop where the header says
that the function cannot stop. Against them the rules of the function dialect are lawful for the
semantics of a function (`localFactRules_lawful`), read as the check of facts reads it
(`localReading`), with the relation `LocalReturns`, validity of the model (`ValidDyn`) and the
stop `undefined`; the facts of the table are about `ValidRun` of `LocalReturns`, which is
`LocalRun` (`Analysis.Facts.localRun_of_valid`, `Analysis.Facts.validRun_of_local`). The law
`collect` asks that the collected values be as many as the size given: without that it is false
of the function dialect (`Analysis.collect_without_length`). So the check of facts is sound for a
function (`checkFacts_sound`), from the soundness of the analysis (`Analysis.analyse_safe`).
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

end

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
    (safe : ∀ hdr (callee : Member fns hdr) (args : HList M.Val hdr.ins), args.All M.Valid →
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
      apply Local.stops_of_halts
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

/-! ## Valid values in scope, payloads and collected values -/

section
variable {V : Vocabulary} {M : Model V}

/-- The values of variables are valid when every value in scope is. -/
theorem env_all_valid {Γ : Ctx V.Ty} {env : Env M.Val Γ}
    (h : ∀ τ (x : Var Γ τ), M.Valid τ (env.get x)) :
    ∀ {items : List V.Ty} (xs : HList (Var Γ) items), (env.all xs).All M.Valid
  | [], .nil => trivial
  | _ :: _, .cons x rest => HList.all_cons.mpr ⟨h _ x, env_all_valid h rest⟩

/-- The payload of an alternative is valid. -/
def PickValid : {payloads : List V.Ty} → Pick M.Val payloads → Prop
  | _, .here v => M.Valid _ v
  | _, .there p => PickValid p

theorem Tys.pick_valid : ∀ (alts : Tys V.TypeKey) (c : alts.Choice M.toCarriers),
    Tys.ValidChoice M.toCarriers alts c → PickValid (Tys.pick M alts c)
  | .nil, c, _ => nomatch c
  | .cons _ _, .inl _, h => h
  | .cons _ rest, .inr c, h => Tys.pick_valid rest c h

theorem pickValid_cast {ps qs : List V.Ty} (h : ps = qs) (p : Pick M.Val ps) :
    PickValid (cast (congrArg (Pick M.Val) h) p) ↔ PickValid p := by
  subst h
  rfl

theorem valid_cast {τ τ' : V.Ty} (h : τ = τ') (v : M.Val τ) :
    M.Valid τ' (cast (congrArg M.Val h) v) ↔ M.Valid τ v := by
  subst h
  rfl

theorem localPick_valid {t : V.Ty} {payloads : List V.Ty}
    (h : ∃ key alternatives, t = .variant key alternatives ∧ payloads = alternatives.toList)
    (v : M.Val t) (valid : M.Valid t v) : PickValid (localPick M h v) := by
  simp only [localPick]
  rw [pickValid_cast (by obtain ⟨_, _, e, q⟩ := h; rw [Ty.alternatives_of e, q])]
  apply Tys.pick_valid
  have := (valid_cast (Ty.eq_variant h) v).mpr valid
  exact this

/-- Values collected so far: as many of each type as iterations, each valid. -/
def CollectedOK : {each : List V.Ty} → HList (fun a => List (M.Val a)) each → Nat → Prop
  | [], .nil, _ => True
  | a :: _, .cons vs rest, i => vs.length = i ∧ (∀ v, v ∈ vs → M.Valid a v) ∧ CollectedOK rest i

theorem collectedOK_empties : ∀ (each : List V.Ty),
    CollectedOK (HList.empties (V := M.Val) each) 0
  | [] => trivial
  | _ :: rest => ⟨rfl, fun _ m => (nomatch m), collectedOK_empties rest⟩

theorem collectedOK_push : ∀ {each : List V.Ty} {acc : HList (fun a => List (M.Val a)) each}
    {i : Nat} {vs : HList M.Val each}, CollectedOK acc i → vs.All M.Valid →
    CollectedOK (acc.push vs) (i + 1)
  | [], .nil, _, .nil, _, _ => trivial
  | _ :: _, .cons xs rest, _, .cons v more, h, all => by
      obtain ⟨len, valid, others⟩ := h
      refine ⟨by simp [len], fun w m => ?_, collectedOK_push others (HList.all_cons.mp all).2⟩
      rcases List.mem_append.mp m with m | m
      · exact valid w m
      · simp only [List.mem_singleton] at m
        subst m
        exact (HList.all_cons.mp all).1

theorem collected_valid {fns : List (FnHeader V)} {table : FnTable M fns} (size : Option Nat)
    {n : Nat} (fits : ∀ m, size = some m → n = m) :
    ∀ {each : List V.Ty} {acc : HList (fun a => List (M.Val a)) each}, CollectedOK acc n →
      ((localSem M fns table).collected size acc).All M.Valid
  | [], .nil, _ => trivial
  | _ :: _, .cons vs rest, h => by
      obtain ⟨len, valid, others⟩ := h
      exact HList.all_cons.mpr ⟨⟨valid, fun m e => by rw [len]; exact fits m e⟩,
        collected_valid size fits others⟩

end

end FactCheck

open FactCheck (Dyn toDyns toDyns_inj)

section
variable {V : Vocabulary} (M : Model V) {fns : List (FnHeader V)} (table : FnTable M fns)

/-- A written form gives results on operands when it is the printed form of a local operation
that returns those results on those operands. The values need not be valid. -/
def LocalReturns (written : LocalRaw V) (operands results : List (Dyn M)) : Prop :=
  ∃ (ins res : List V.Ty) (o : LocalOp V fns ins res) (args : HList M.Val ins)
    (returned : HList M.Val res), o.print = written ∧ toDyns args = operands ∧
    toDyns returned = results ∧ localOp M table o args = .done returned

/-- Values with their types, of the local semantics, are the values of some type of the check of
facts. -/
theorem localDyns_eq_toDyns :
    ∀ {items : List V.Ty} (values : HList M.Val items),
      (localSem M fns table).dyns values = toDyns values
  | [], .nil => rfl
  | _ :: _, .cons v rest => by
      show ⟨_, v⟩ :: (localSem M fns table).dyns rest = ⟨_, v⟩ :: toDyns rest
      rw [localDyns_eq_toDyns rest]

/-- The equality of naturals as the core computes it (`Nat.beq`) does not depend on the order of
its operands. -/
theorem natEqual_symmetric (first second : Nat) : Nat.beq first second = Nat.beq second first :=
  Bool.eq_iff_iff.mpr (by simp only [Nat.beq_eq]; exact eq_comm)

/-- The local operations that are values satisfy the laws of the value form: one that is a
value returns what its printed form gives, or stops `undefined`; a printed form gives one
result; and a printed form that commutes, which is that of an operation that the core owns whose
meaning is symmetric in its two operands, gives the same result on them exchanged. Its
hypotheses: the callees have distinct keys, so that a printed form names one operation; and a
callee whose header says that it cannot stop stops only `undefined`, since a call of it is a
value. -/
theorem localFactRules_binding (distinct : (fns.map (·.key)).Nodup)
    (quiet : ∀ hdr (callee : Member fns hdr) (args : HList M.Val hdr.ins), hdr.canStop = false →
      (table hdr callee args).Stops (· = .undefined)) :
    (localFactRules V fns).values.Binding (localSem M fns table) (LocalReturns M table)
      (· = Stop.undefined) where
  computes := by
    intro ins res o raw written key path values
    cases stops : LocalOp.canStop o with
    | true => simp only [FactRules.values, localFactRules, stops, Bool.cond_true, reduceCtorEq] at written
    | false =>
        simp only [FactRules.values, localFactRules, stops, Bool.cond_false, Option.some.injEq] at written
        show (∃ results, localOp M table o values = .done results ∧ _) ∨
          ∃ stop, localOp M table o values = .halt stop ∧ stop = Stop.undefined
        have undefinedOnly := localOp_stops_undefined M table quiet o values stops
        cases ran : localOp M table o values with
        | done returned =>
            exact .inl ⟨returned, rfl, ins, res, o, values, returned, written,
              (localDyns_eq_toDyns M table values).symm,
              (localDyns_eq_toDyns M table returned).symm, ran⟩
        | halt stop =>
            rw [ran] at undefinedOnly
            exact .inr ⟨stop, rfl, undefinedOnly⟩
        | call op _ => exact nomatch op
  functional := by
    intro raw operands results results' first second
    obtain ⟨ins, res, o, args, returned, printed, sameArgs, sameResults, ran⟩ := first
    obtain ⟨ins', res', o', args', returned', printed', sameArgs', sameResults', ran'⟩ := second
    obtain ⟨rfl, sameValues⟩ := toDyns_inj args args' (sameArgs.trans sameArgs'.symm)
    cases eq_of_heq sameValues
    obtain ⟨rfl, sameOp⟩ :=
      Sigma.mk.inj (LocalOp.print_injective distinct o o' (printed.trans printed'.symm))
    cases eq_of_heq sameOp
    rw [ran] at ran'
    cases ran'
    rw [← sameResults, ← sameResults']
  commutative := by
    intro raw commutes first second results returns
    obtain ⟨ins, res, o, args, returned, printed, sameArgs, sameResults, ran⟩ := returns
    subst printed
    cases o with
    | row => simp [FactRules.values, localFactRules, LocalOp.print, LocalRaw.commutes] at commutes
    | literal => simp [FactRules.values, localFactRules, LocalOp.print, LocalRaw.commutes] at commutes
    | call => simp [FactRules.values, localFactRules, LocalOp.print, LocalRaw.commutes] at commutes
    | owned o =>
        cases o <;> simp [FactRules.values, localFactRules, LocalOp.print, OwnedOp.name, LocalRaw.commutes,
          OwnedName.commutes] at commutes
        all_goals
          rcases args with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
          simp only [toDyns, List.cons.injEq] at sameArgs
          obtain ⟨rfl, rfl, -⟩ := sameArgs
          refine ⟨_, _, .owned _, .cons b (.cons a .nil), returned, rfl, rfl, sameResults, ?_⟩
          rw [← ran]
          simp only [localOp, ownedOp, Nat.add_comm, Nat.mul_comm, Bool.and_comm, Bool.or_comm,
            Bool.beq_comm, natEqual_symmetric]

end

/-- Operations that following finds the same are the same, over headers with distinct keys: a
printed form names one operation. -/
theorem localSkelRules_lawful {V : Vocabulary} {fns : List (FnHeader V)}
    (distinct : (fns.map (·.key)).Nodup) : (localSkelRules V fns).Lawful := by
  intro ins res res' o o' found
  exact Sigma.mk.inj (LocalOp.print_injective distinct o o' (of_decide_eq_true found))

/-! ## The callees of a function -/

section
variable {V : Vocabulary}

/-- The callees that a statement about a function is made against: distinct keys, never
`undefined` on valid inputs, valid results, and only `undefined` as a stop where the header says
that the function cannot stop. -/
structure Callees (M : Model V) {fns : List (FnHeader V)} (table : FnTable M fns) : Prop where
  distinct : (fns.map (·.key)).Nodup
  safe : FnTable.Safe table
  keeps : FnTable.KeepsValidity table
  quiet : ∀ hdr (callee : Member fns hdr) (args : HList M.Val hdr.ins), hdr.canStop = false →
    (table hdr callee args).Stops (· = .undefined)

end


namespace Analysis

open FactCheck

namespace Facts

section
variable {V : Vocabulary} {M : Model V} {fns : List (FnHeader V)} {table : FnTable M fns}

/-- A local operation that returns valid results on valid operands, by its written form, is a run
of the check of facts. -/
theorem localRun_of_valid {w : LocalRaw V} {as rs : List (Dyn M)}
    (h : ValidRun (localSem M fns table) (LocalReturns M table) (ValidDyn M) w as rs) :
    LocalRun M table w as rs := by
  obtain ⟨⟨ins, res, o, args, returned, printed, sameArgs, sameResults, ran⟩, va, vr⟩ := h
  subst sameArgs sameResults
  exact ⟨ins, res, o, args, returned, printed, rfl, rfl, valid_of_toDyns va, valid_of_toDyns vr,
    ran⟩

/-- A run of the check of facts is a local operation that returns valid results on valid
operands. -/
theorem validRun_of_local {w : LocalRaw V} {as rs : List (Dyn M)} (h : LocalRun M table w as rs) :
    ValidRun (localSem M fns table) (LocalReturns M table) (ValidDyn M) w as rs := by
  obtain ⟨ins, res, o, a, r, printed, ha, hr, va, vr, ran⟩ := h
  subst ha hr
  exact ⟨⟨ins, res, o, a, r, printed, rfl, rfl, ran⟩, toDyns_valid va, toDyns_valid vr⟩

end

section
variable {Raw Val : Type} {Run Run' : Raw → List Val → List Val → Prop}
  (sub : ∀ w as rs, Run w as rs → Run' w as rs)
include sub

/-- What an operand of a requirement names of one relation it names of a larger one. -/
theorem operand_denotes_mono {args : List Val} :
    ∀ {o : Operand Raw} {v : Val}, o.Denotes Run args v → o.Denotes Run' args v
  | .arg _, _, h => h
  | .apply _ _, _, ⟨operands, rs, positions, run, head⟩ =>
      ⟨operands, rs, positions, sub _ _ _ run, head⟩

theorem denotesAll_mono {args : List Val} :
    ∀ {os : List (Operand Raw)} {vs : List Val}, DenotesAll Run args os vs →
      DenotesAll Run' args os vs
  | [], [], h => h
  | _ :: _, _ :: _, ⟨first, rest⟩ => ⟨operand_denotes_mono sub first, denotesAll_mono rest⟩
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

/-- A requirement that holds of one relation holds of a larger one. -/
theorem requirement_holds_mono {R : Reading Val} {args : List Val} {req : Requirement Raw}
    (h : req.Holds Run R args) : req.Holds Run' R args := by
  obtain ⟨vs, d, rel⟩ := h
  exact ⟨vs, denotesAll_mono sub d, rel⟩

end

section
variable {V : Vocabulary} (M : Model V)

/-- The payload of a valid variant, as the core says it, is valid as the laws say it. -/
theorem pickValid_local {fns : List (FnHeader V)} (table : FnTable M fns) :
    ∀ {payloads : List V.Ty} (p : Pick M.Val payloads), FactCheck.PickValid (M := M) p →
      PickValid (localSem M fns table) (ValidDyn M) p
  | _, .here _, h => h
  | _, .there p, h => pickValid_local table p h

end

end Facts

section
variable {V : Vocabulary} (M : Model V) {fns : List (FnHeader V)} (table : FnTable M fns)

/-- The law `collect` as first stated, without the length of the collected values, is false of
the function dialect: a sequence of a written size is valid only of that length. -/
theorem collect_without_length :
    ¬ ∀ (size : Option Nat) (a : V.Ty) (vs : List ((localSem M fns table).Val a)),
      (∀ v, v ∈ vs → ValidDyn M ⟨a, v⟩) →
      ValidDyn M ⟨(localDialect V fns).collected size a, (localSem M fns table).collect size a vs⟩ :=
  fun law => by
    have := (law (some 1) .nat [] (fun _ m => nomatch m)).2 1 rfl
    cases this

end

end Analysis

open FactCheck

section
variable {V : Vocabulary} (M : Model V) {fns : List (FnHeader V)} (table : FnTable M fns)

/-- **The laws hold of the function dialect.** Against callees with distinct keys that never stop
`undefined` on valid inputs, keep validity, and stop only `undefined` where their headers say that
they cannot stop, the rules of the function dialect are lawful for its semantics, for any
permitted replies. -/
theorem localFactRules_lawful (distinct : (fns.map (·.key)).Nodup) (safe : FnTable.Safe table)
    (keeps : FnTable.KeepsValidity table)
    (quiet : ∀ hdr (callee : Member fns hdr) (args : HList M.Val hdr.ins), hdr.canStop = false →
      (table hdr callee args).Stops (· = .undefined))
    (permitted : ∀ op, (localSem M fns table).S.Reply op → Prop) :
    (localFactRules V fns).Lawful (localSem M fns table) permitted (localReading M)
      (LocalReturns M table) (ValidDyn M) (· = .undefined) where
  binding := localFactRules_binding M table distinct quiet
  ops :=
    { functional := fun _ _ _ _ h1 h2 =>
        localRun_functional distinct (Analysis.Facts.localRun_of_valid h1) (Analysis.Facts.localRun_of_valid h2)
      form := fun _ _ _ _ hf h => localRun_form hf (Analysis.Facts.localRun_of_valid h)
      ranges := fun _ _ _ known h hk => localRun_ranges known (Analysis.Facts.localRun_of_valid h) hk }
  keeps := by
    intro raw operands results run valid
    obtain ⟨ins, res, o, args, returned, printed, sameArgs, sameResults, ran⟩ := run
    subst sameArgs sameResults
    exact toDyns_valid (localOp_valid table keeps o args returned (valid_of_toDyns valid) ran)
  defined := by
    intro ins res o raw written key path values valid holds
    cases stops : LocalOp.canStop o with
    | true => simp [localFactRules, stops] at written
    | false =>
        simp only [localFactRules, stops, Bool.cond_false, Option.some.injEq]
          at written
        subst written
        have va : values.All M.Valid := valid_of_toDyns fun d m =>
          valid d (by rw [localDyns_eq_toDyns M table]; exact m)
        have defined := localOp_defined safe o values va fun req m => by
          have h := holds req m
          rw [localDyns_eq_toDyns M table] at h
          exact Analysis.Facts.requirement_holds_mono (fun _ _ _ run => Analysis.Facts.localRun_of_valid run) h
        have onlyUndefined := localOp_stops_undefined M table quiet o values stops
        show ∃ results, localOp M table o values = .done results
        cases hrun : localOp M table o values with
        | done r => exact ⟨r, rfl⟩
        | halt h =>
            rw [hrun] at defined onlyUndefined
            exact absurd onlyUndefined defined
        | call op _ => exact nomatch op
  named := by
    intro ins res o raw written values valid req m operand mo w ps e
    cases stops : LocalOp.canStop o with
    | true => simp [localFactRules, stops] at written
    | false =>
        simp only [localFactRules, stops, Bool.cond_false, Option.some.injEq]
          at written
        subst written
        have va : values.All M.Valid := valid_of_toDyns fun d m =>
          valid d (by rw [localDyns_eq_toDyns M table]; exact m)
        obtain ⟨as, rs, hp, run, one⟩ := localRequires_runs o values va req m operand mo w ps e
        refine ⟨as, rs, by rw [localDyns_eq_toDyns M table]; exact hp,
          Analysis.Facts.validRun_of_local run, one⟩
  effect := by
    intro ins res o written key path values valid
    have va : values.All M.Valid := valid_of_toDyns fun d m =>
      valid d (by rw [localDyns_eq_toDyns M table]; exact m)
    cases o with
    | call callee =>
        have stops := safe _ callee values va
        show (table _ callee values).Every permitted _ _
        cases hrun : table _ callee values with
        | done r =>
            show ∀ v, v ∈ (localSem M fns table).dyns r → ValidDyn M v
            rw [localDyns_eq_toDyns M table]
            exact toDyns_valid (keeps _ callee values r va hrun)
        | halt h =>
            rw [hrun] at stops
            exact stops
        | call op _ => exact nomatch op
    | row => simp [localFactRules, LocalOp.canStop] at written
    | owned => simp [localFactRules, LocalOp.canStop] at written
    | literal => simp [localFactRules, LocalOp.canStop] at written
  range := fun _ _ v h valid => localRange_has h v valid
  noValue := fun _ v valid => localNoValue_valid (fns := fns) v valid
  condition := by
    intro w t ok v _
    subst ok
    rfl
  count := by
    intro w t ok v _
    subst ok
    rfl
  pick := fun ok v valid => Analysis.Facts.pickValid_local M table _ (localPick_valid ok v valid)
  index := fun _ _ => ⟨trivial, rfl⟩
  collect := fun _ _ _ length valid => ⟨valid, length⟩
  begin := fun _ _ _ => trivial
  settle := fun _ _ _ => trivial
  stop := fun _ _ _ => nofun

end

/-! ## The check of facts of a function -/

section
variable {V : Vocabulary} {M : Model V} {fns : List (FnHeader V)}

open FactCheck in
/-- **The check of facts is sound for functions.** A body with distinct addresses that the check
accepts, against callees with distinct keys that never stop `undefined` on valid inputs, keep
validity and stop only `undefined` where their headers say that they cannot stop: on valid
inputs every loop respects the bound that the check gave it, and the body never stops
`undefined` and returns valid values. -/
theorem checkFacts_sound {table : FnTable M fns} (callees : Callees M table) (definition : Key)
    {types outs : List V.Ty} (inputs : Names types)
    (body : Term (localDialect V fns) (Ctx.empty.extend inputs) outs)
    (distinct : Term.Distinct body) {bounds : List (Place × Nat)}
    (accepted : checkFacts (localFactRules V fns) (localSkelRules V fns) definition none inputs
      body = .ok bounds)
    (F : List (Place × Nat))
    (recorded : ∀ p b, (p, b) ∈ F → p.definition = definition → p.role = none → (p, b) ∈ bounds)
    (ins : HList M.Val types) (valid : ins.All M.Valid) :
    body.EveryLoop (localSem M fns table) (fun _ _ => True)
        (Annotation.Bounded ⟨F⟩ definition none) [] [] (Env.empty.extend inputs ins) ∧
      (body.denote (localSem M fns table) [] (Env.empty.extend inputs ins)).Every
        (fun _ _ => True) (fun outs => outs.All M.Valid) (· ≠ .undefined) := by
  obtain ⟨refused, same⟩ := checkFacts_ok accepted
  subst same
  have safe := Analysis.analyse_safe (localFactRules V fns) (localSkelRules V fns)
    (localSem M fns table) (fun _ _ => True) (localReading M) (LocalReturns M table) (ValidDyn M)
    (· = .undefined)
    (localFactRules_lawful M table callees.distinct callees.safe callees.keeps callees.quiet
      (fun _ _ => True))
    (localSkelRules_lawful callees.distinct) definition none inputs body distinct refused F
    (fun p b m d r => List.mem_reverse.mp (recorded p b m d r))
    ins (by rw [localDyns_eq_toDyns M table]; exact toDyns_valid valid)
  refine ⟨safe.1, Process.every_mono _ _ (fun outs returned => ?_) (fun _ h => h) safe.2⟩
  rw [localDyns_eq_toDyns M table] at returned
  exact valid_of_toDyns returned

end

end Zkc.Core
