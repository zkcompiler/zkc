module

public import Zkc.Core.Facts.Local
public import Zkc.Core.Facts.Theorems
public import Zkc.Core.Meaning.Validity
public import Zkc.Core.Meaning.Stops
public import Zkc.Core.Meaning.Call
public import Zkc.Core.Evidence.Summary

@[expose] public section

/-!
The laws of the function dialect, and the soundness of the check of facts for a function.

A value of a function is a value of its semantics with its type (`Semantics.Dyn`). A written form
gives results on operands when it is the printed form of a local operation that returns those
results on those operands (`LocalReturns`), whatever the values, valid or not; it is a function of
the written form and the operands, because the written form names the operation
(`localReturns_functional`). The facts of the table are about it on valid values (`ValidRun`). Of
it, what the analysis knows of the written operations is true: the form of a result, the ranges of
arithmetic (TY8), and what the type of a natural says. Every operation has the requirements of
its printed form, and what an operation requires is enough for it: where every requirement holds
of its operands' values, it does not stop `undefined`; and every value that a requirement names
beyond the operands (a length, the truth value of a domain row) is there. A call has no
requirement yet, so a call of a function that can stop, which is kept in order, is safe on every
valid input because its callee is (`Callees`).

The law `computes` of the value form is for every value, and so is the law `commutative`, since
the meaning of each operation that commutes is symmetric for all values of its operands. Against
callees with distinct keys, of which those whose headers say that they cannot stop stop only
`undefined`, the local operations that are values satisfy the laws of the value form
(`localFactRules_binding`); following, which decides two operations by their printed forms, is
lawful over headers with distinct keys, as the rules of elaboration are (`Rules.skel_lawful`,
`localRules_lawful`).

Against the callees that a statement about a function is made against (`Callees`,
`Meaning/Validity.lean`), the rules of the function dialect are lawful for the semantics of a
function (`localFactRules_lawful`), read as the check of facts reads it (`localReading`), with the
relation `LocalReturns`, the validity of the model (`ValidDyn`) and the stop `undefined`. The law
`collect` asks that the collected values be as many as the size given: without that it is false
of the function dialect (`Analysis.collect_without_length`). The theorems of the analysis are
instantiated for functions here, once, against a model, a table and `Callees`, and stated as the
statements about functions are, with `HList.All` (converted by `Semantics.dyns_valid_iff`): the
check of facts is sound for a function (`checkFacts_sound`, from `Analysis.analyse_safe`), and a
body that follows the analysis of a body that is safe on the given inputs is safe, respects the
bounds recorded while it follows and means the same (`localFollow_assured`, from
`Analysis.follow_assured`).

Read so, a summary of a function (`Summary`, `Evidence/Summary.lean`) holds of its entry in a
table exactly when the entry has the contract of `Meaning/Call.lean` whose precondition is valid
inputs that satisfy the requirements, whose postcondition is valid results that satisfy the
guarantees, and whose stops are not `undefined` (`localSummary_contract`).
-/
namespace Zkc.Core

section
variable {V : Vocabulary} (M : Model V) {fns : List (FnHeader V)} (table : FnTable M fns)

/-- A written form gives results on operands when it is the printed form of a local operation
that returns those results on those operands. The values need not be valid. -/
def LocalReturns (written : LocalRaw V) (operands results : List (localSem M fns table).Dyn) :
    Prop :=
  ∃ (ins res : List V.Ty) (o : LocalOp V fns ins res) (args : HList M.Val ins)
    (returned : HList M.Val res), o.print = written ∧ (localSem M fns table).dyns args = operands ∧
    (localSem M fns table).dyns returned = results ∧ localOp M table o args = .done returned

end

namespace FactCheck

section
variable {V : Vocabulary} (M : Model V)

/-- How the check reads a value of a function: a natural or an index as a natural, a truth
value as itself. -/
def localReading : Reading ((τ : V.Ty) × M.Val τ) where
  nat
    | ⟨.nat, n⟩ => some n
    | ⟨.fin _, n⟩ => some n
    | _ => none
  bool
    | ⟨.bool, b⟩ => some b
    | _ => none

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
theorem localReturns_functional (distinct : (fns.map (·.key)).Nodup) {w : LocalRaw V}
    {as rs rs' : List (localSem M fns table).Dyn} (first : LocalReturns M table w as rs)
    (second : LocalReturns M table w as rs') : rs = rs' := by
  obtain ⟨ins, res, o, args, returned, printed, sameArgs, sameResults, ran⟩ := first
  obtain ⟨ins', res', o', args', returned', printed', sameArgs', sameResults', ran'⟩ := second
  obtain ⟨rfl, sameValues⟩ :=
    (localSem M fns table).dyns_heq args args' (sameArgs.trans sameArgs'.symm)
  cases eq_of_heq sameValues
  obtain ⟨rfl, sameOp⟩ :=
    Sigma.mk.inj (LocalOp.print_injective distinct o o' (printed.trans printed'.symm))
  cases eq_of_heq sameOp
  rw [ran] at ran'
  cases ran'
  rw [← sameResults, ← sameResults']

/-- How the first result of a local operation reads. -/
theorem localReturns_form {w : LocalRaw V} {as rs : List (localSem M fns table).Dyn}
    {f : ResultForm} (hf : (localOpFacts V).form w = some f) (h : LocalReturns M table w as rs) :
    ∃ r, rs.head? = some r ∧ FormHolds (localReading M) f as r := by
  obtain ⟨ins, res, o, a, r, rfl, rfl, rfl, run⟩ := h
  cases o with
  | row => simp [LocalOp.print, localOpFacts] at hf
  | call => simp [LocalOp.print, localOpFacts] at hf
  | literal τ data reads =>
      simp only [LocalOp.print] at hf
      have shape : (τ = .bool ∧ data = [0] ∧ f = .truth false) ∨
          (τ = .bool ∧ data = [1] ∧ f = .truth true) := by
        simp only [localOpFacts] at hf
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
      cases op <;> simp [LocalOp.print, OwnedOp.name, localOpFacts, ownedContract] at hf <;>
        subst hf
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
    (e : ((ownedContract (V := V) .seqLength).ranges [.seq item size] known)[i]? =
      some (some r)) :
    i = 0 ∧ r.Has len := by
  cases size with
  | none =>
      simp only [ownedContract] at e
      cases i with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at e
          subst e
          exact ⟨rfl, Nat.zero_le _, fun _ e => nomatch e⟩
      | succ i => simp at e
  | some size =>
      simp only [ownedContract] at e
      cases i with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at e
          subst e
          exact ⟨rfl, Range.has_point.mpr (hlen size rfl)⟩
      | succ i => simp at e

/-- The ranges of the results of a local operation hold where those of its operands do. -/
theorem localRun_ranges {w : LocalRaw V} {as rs : List (localSem M fns table).Dyn}
    (known : List (Option Range))
    (h : ValidRun (localSem M fns table) (LocalReturns M table) (ValidDyn M) w as rs)
    (hk : ∀ (i : Nat) (r : Range), known[i]? = some (some r) →
      ∃ v n, as[i]? = some v ∧ (localReading M).nat v = some n ∧ r.Has n) :
    ∀ (i : Nat) (r : Range), ((localOpFacts V).ranges w known)[i]? = some (some r) →
      ∃ v n, rs[i]? = some v ∧ (localReading M).nat v = some n ∧ r.Has n := by
  obtain ⟨⟨ins, res, o, a, r, rfl, rfl, rfl, run⟩, valid, _⟩ := h
  have va : a.All M.Valid := ((localSem M fns table).dyns_valid_iff a).mp valid
  have at_ : ∀ (j : Nat) (x : Nat),
      (localReading M).nat (((localSem M fns table).dyns a)[j]?.getD ⟨.nat, 0⟩) = some x →
      j < ((localSem M fns table).dyns a).length → ∀ r, known[j]? = some (some r) → r.Has x := by
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
      cases op <;> simp [LocalOp.print, OwnedOp.name, localOpFacts, ownedContract] at e
      case natAdd =>
        obtain ⟨x, y, rfl⟩ := HList.two a
        simp only [localOp, ownedOp, Process.done.injEq] at run
        subst run
        obtain ⟨rfl, has⟩ := onTwo_has (fun _ _ ha hb => Range.add_has ha hb)
          (at_ 0 x rfl (by simp [Semantics.dyns_length]))
          (at_ 1 y rfl (by simp [Semantics.dyns_length])) i rr e
        exact ⟨_, x + y, rfl, rfl, has⟩
      case natSub =>
        obtain ⟨x, y, rfl⟩ := HList.two a
        simp only [localOp, ownedOp] at run
        split at run
        · simp only [Process.done.injEq] at run
          subst run
          obtain ⟨rfl, has⟩ := onTwo_has (fun _ _ ha hb => Range.sub_has ha hb)
            (at_ 0 x rfl (by simp [Semantics.dyns_length]))
            (at_ 1 y rfl (by simp [Semantics.dyns_length])) i rr e
          exact ⟨_, x - y, rfl, rfl, has⟩
        · cases run
      case natMul =>
        obtain ⟨x, y, rfl⟩ := HList.two a
        simp only [localOp, ownedOp, Process.done.injEq] at run
        subst run
        obtain ⟨rfl, has⟩ := onTwo_has (fun _ _ ha hb => Range.mul_has ha hb)
          (at_ 0 x rfl (by simp [Semantics.dyns_length]))
          (at_ 1 y rfl (by simp [Semantics.dyns_length])) i rr e
        exact ⟨_, x * y, rfl, rfl, has⟩
      case natDiv =>
        obtain ⟨x, y, rfl⟩ := HList.two a
        simp only [localOp, ownedOp] at run
        split at run
        · next pos =>
            simp only [Process.done.injEq] at run
            subst run
            obtain ⟨rfl, has⟩ := onTwo_has (fun ka kb ha hb => Range.div_has ha hb pos)
              (at_ 0 x rfl (by simp [Semantics.dyns_length]))
              (at_ 1 y rfl (by simp [Semantics.dyns_length])) i rr e
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
              (at_ 0 x rfl (by simp [Semantics.dyns_length]))
              (at_ 1 y rfl (by simp [Semantics.dyns_length])) i rr e
            exact ⟨_, x % y, rfl, rfl, has⟩
        · cases run
      case natPow =>
        obtain ⟨x, y, rfl⟩ := HList.two a
        simp only [localOp, ownedOp, Process.done.injEq] at run
        subst run
        obtain ⟨rfl, has⟩ := onTwo_has (fun _ _ ha hb => Range.pow_has ha hb)
          (at_ 0 x rfl (by simp [Semantics.dyns_length]))
          (at_ 1 y rfl (by simp [Semantics.dyns_length])) i rr e
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
          obtain ⟨rfl, has⟩ := onOne_has (at_ 0 x rfl (by simp [Semantics.dyns_length])) i rr e
          exact ⟨_, x, rfl, rfl, has⟩
        · cases run
      case finToNat bound =>
        obtain ⟨x, rfl⟩ := HList.one a
        simp only [localOp, ownedOp, Process.done.injEq] at run
        subst run
        obtain ⟨rfl, has⟩ := onOne_has (at_ 0 x rfl (by simp [Semantics.dyns_length])) i rr e
        exact ⟨_, x, rfl, rfl, has⟩
      case finWiden bound wider le =>
        obtain ⟨x, rfl⟩ := HList.one a
        simp only [localOp, ownedOp, Process.done.injEq] at run
        subst run
        obtain ⟨rfl, has⟩ := onOne_has (at_ 0 x rfl (by simp [Semantics.dyns_length])) i rr e
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

/-- Applied to a sequence, its length. -/
theorem localReturns_length {item : V.Ty} {size : Option Nat} {xs : M.Val (.seq item size)}
    {rs : List (localSem M fns table).Dyn}
    (h : LocalReturns M table (.owned .seqLength [.seq item size] []) [⟨.seq item size, xs⟩] rs) :
    rs = [⟨.nat, (xs : List (M.Val item)).length⟩] := by
  obtain ⟨ins, res, o, a, r, hp, ha, rfl, run⟩ := h
  cases o with
  | row => simp [LocalOp.print] at hp
  | literal => simp [LocalOp.print] at hp
  | call => simp [LocalOp.print] at hp
  | owned op =>
      cases op <;> simp [LocalOp.print, OwnedOp.name] at hp
      obtain ⟨rfl, rfl⟩ := hp
      obtain ⟨ys, rfl⟩ := HList.one a
      have ha : [(⟨_, ys⟩ : (τ : V.Ty) × M.Val τ)] = [⟨_, xs⟩] := ha
      simp only [List.cons.injEq, Sigma.mk.injEq, heq_eq_eq, and_true, true_and] at ha
      subst ha
      simp only [localOp, ownedOp, Process.done.injEq] at run
      subst run
      rfl

theorem localRun_length_intro {item : V.Ty} {size : Option Nat}
    (free : Ty.isLinear V item = false) (xs : M.Val (.seq item size)) (valid : M.Valid _ xs) :
    ValidRun (localSem M fns table) (LocalReturns M table) (ValidDyn M)
      (.owned .seqLength [.seq item size] []) [⟨.seq item size, xs⟩]
      [⟨.nat, (xs : List (M.Val item)).length⟩] :=
  ⟨⟨_, _, .owned (.seqLength item size free), .cons xs .nil,
      .cons (xs : List (M.Val item)).length .nil, rfl, rfl, rfl, rfl⟩,
    fun _ found => by
      rw [List.mem_singleton] at found
      subst found
      exact valid,
    fun _ found => by
      rw [List.mem_singleton] at found
      subst found
      trivial⟩

/-- The domain row of a restricted row, at its operands, gives whether they are in its
domain. -/
theorem localRun_domain_intro {key domain : V.RowKey} {sig : RowSignature V.TypeKey V.RowKey}
    (known : V.row key = some sig) (kind : sig.kind = .restricted domain)
    (a : HList M.Val sig.ins) (va : a.All M.Valid) :
    ValidRun (localSem M fns table) (LocalReturns M table) (ValidDyn M) (.row domain)
      ((localSem M fns table).dyns a) [⟨.bool, M.inDomain key sig known a⟩] := by
  refine ⟨⟨_, _, .row domain ⟨sig.ins, [.bool], .pure⟩ (V.decided key sig domain known kind), a,
      .cons (M.inDomain key sig known a) .nil, rfl, rfl, rfl, ?_⟩,
    ((localSem M fns table).dyns_valid_iff a).mpr va, fun _ found => by
      rw [List.mem_singleton] at found
      subst found
      trivial⟩
  simp only [localOp]
  rw [M.decides key sig known domain kind a]

/-- What the domain row of a restricted row gives at its operands. -/
theorem localReturns_domain {key domain : V.RowKey} {sig : RowSignature V.TypeKey V.RowKey}
    (known : V.row key = some sig) (kind : sig.kind = .restricted domain)
    (a : HList M.Val sig.ins) {rs : List (localSem M fns table).Dyn}
    (h : LocalReturns M table (.row domain) ((localSem M fns table).dyns a) rs) :
    rs = [⟨.bool, M.inDomain key sig known a⟩] := by
  have decides := M.decides key sig known domain kind a
  obtain ⟨ins', res', o, a', r, hp, ha, rfl, run⟩ := h
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
      obtain ⟨_, heq⟩ := (localSem M fns table).dyns_heq a' a ha
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
      req.Holds (ValidRun (localSem M fns table) (LocalReturns M table) (ValidDyn M))
        (localReading M) ((localSem M fns table).dyns a)) :
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
      rw [← (localSem M fns table).dyns_length a, atPositions_range _ _ (Nat.le_refl _),
        List.take_length, Option.some.injEq] at hpos
      subst hpos
      have := localReturns_domain known hk a run.1
      subst this
      simp only [List.head?_cons, Option.some.injEq] at head
      subst head
      simpa [Requirement.Relation, localReading] using rel

/-! ### Each operation with a domain -/

/-- What a requirement says, of values that its operands name. -/
abbrev Holds (args : List (localSem M fns table).Dyn) (req : Requirement (LocalRaw V)) : Prop :=
  req.Holds (ValidRun (localSem M fns table) (LocalReturns M table) (ValidDyn M)) (localReading M)
    args

theorem holds_args {args : List (localSem M fns table).Dyn} {i j : Nat}
    {req : Requirement (LocalRaw V)} {u v : (localSem M fns table).Dyn} (hu : args[i]? = some u)
    (hv : args[j]? = some v)
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

theorem holds_arg {args : List (localSem M fns table).Dyn} {i : Nat}
    {req : Requirement (LocalRaw V)} {u : (localSem M fns table).Dyn} (hu : args[i]? = some u)
    (ops : req.operands = [.arg i])
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
    {rest : List (localSem M fns table).Dyn} {v : (localSem M fns table).Dyn}
    (h : (Operand.apply (lengthOfType (.seq item size)) [0] : Operand (LocalRaw V)).Denotes
      (ValidRun (localSem M fns table) (LocalReturns M table) (ValidDyn M))
      (⟨.seq item size, xs⟩ :: rest) v) :
    v = ⟨.nat, (xs : List (M.Val item)).length⟩ := by
  obtain ⟨as, rs, hpos, run, head⟩ := h
  simp only [atPositions, List.getElem?_cons_zero, Option.some.injEq] at hpos
  subst hpos
  rw [localReturns_length run.1] at head
  simp only [List.head?_cons, Option.some.injEq] at head
  exact head.symm

theorem natSub_defined (x y : Nat)
    (holds : ∀ req, req ∈ (ownedContract (V := V) .natSub).requires [] →
      Holds (table := table) [⟨.nat, x⟩, ⟨.nat, y⟩] req) :
    ∀ h, ownedOp M (.natSub (V := V)) (.cons x (.cons y .nil)) = .halt h → h ≠ .undefined := by
  intro h e
  have le := holds_args (u := ⟨.nat, y⟩) (v := ⟨.nat, x⟩) rfl rfl rfl
    (holds (.le (.arg 1) (.arg 0)) (by simp [ownedContract])) y x rfl rfl
  simp [ownedOp, le] at e

theorem natDiv_defined (x y : Nat)
    (holds : ∀ req, req ∈ (ownedContract (V := V) .natDiv).requires [] →
      Holds (table := table) [⟨.nat, x⟩, ⟨.nat, y⟩] req) :
    ∀ h, ownedOp M (.natDiv (V := V)) (.cons x (.cons y .nil)) = .halt h → h ≠ .undefined := by
  intro h e
  have pos := holds_arg (u := ⟨.nat, y⟩) rfl rfl
    (holds (.atLeast (.arg 1) 1) (by simp [ownedContract])) y rfl
  simp [ownedOp, show 1 ≤ y from pos] at e

theorem natRem_defined (x y : Nat)
    (holds : ∀ req, req ∈ (ownedContract (V := V) .natRem).requires [] →
      Holds (table := table) [⟨.nat, x⟩, ⟨.nat, y⟩] req) :
    ∀ h, ownedOp M (.natRem (V := V)) (.cons x (.cons y .nil)) = .halt h → h ≠ .undefined := by
  intro h e
  have pos := holds_arg (u := ⟨.nat, y⟩) rfl rfl
    (holds (.atLeast (.arg 1) 1) (by simp [ownedContract])) y rfl
  simp [ownedOp, show 1 ≤ y from pos] at e

theorem natBelow_defined (bound n : Nat)
    (holds : ∀ req, req ∈ (ownedContract (V := V) .natBelow).requires [.fin bound] →
      Holds (table := table) [⟨.nat, n⟩] req) :
    ∀ h, ownedOp M (.natBelow (V := V) bound) (.cons n .nil) = .halt h → h ≠ .undefined := by
  intro h e
  have lt := holds_arg (u := ⟨.nat, n⟩) rfl rfl
    (holds (.below (.arg 0) bound) (by simp [ownedContract])) n rfl
  simp [ownedOp, show n < bound from lt] at e

theorem seqAt_defined {item : V.Ty} {size : Option Nat} (free : Ty.isLinear V item = false)
    (xs : M.Val (.seq item size)) (i : Nat) (valid : M.Valid _ xs)
    (holds : ∀ req, req ∈ (ownedContract .seqAt).requires [.seq item size] →
      Holds (table := table) [⟨.seq item size, xs⟩, ⟨.nat, i⟩] req) :
    ∀ h, ownedOp M (.seqAt item size free) (.cons xs (.cons i .nil)) = .halt h →
      h ≠ .undefined := by
  intro h e
  have lt : i < (xs : List (M.Val item)).length := by
    cases size with
    | some size =>
        have := holds_arg (u := ⟨.nat, i⟩) rfl rfl
          (holds (.below (.arg 1) size) (by simp [ownedContract])) i rfl
        rw [valid.2 size rfl]
        exact this
    | none =>
        obtain ⟨vs, d, rel⟩ := holds (.lt (.arg 1) (.apply (lengthOfType (.seq item none)) [0]))
          (by simp [ownedContract])
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
    (holds : ∀ req, req ∈ (ownedContract .seqSlice).requires [.seq item size, .seq item result] →
      Holds (table := table) [⟨.seq item size, xs⟩, ⟨.nat, first⟩, ⟨.nat, second⟩] req) :
    ∀ h, ownedOp M (.seqSlice item size result free)
      (.cons xs (.cons first (.cons second .nil))) = .halt h → h ≠ .undefined := by
  intro h e
  have ordered := holds_args (u := ⟨.nat, first⟩) (v := ⟨.nat, second⟩) rfl rfl rfl
    (holds (.le (.arg 1) (.arg 2)) (by simp [ownedContract])) first second rfl rfl
  have within : second ≤ (xs : List (M.Val item)).length := by
    obtain ⟨vs, d, rel⟩ := holds (.le (.arg 2) (.apply (lengthOfType (.seq item size)) [0]))
      (by simp [ownedContract])
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
          (holds (.difference (.arg 2) (.arg 1) count) (by simp [ownedContract]))
          second first rfl rfl
        simp [fitsSize, this]
  simp only [ownedOp] at e
  split at e
  · cases e
  · next outside => exact (outside ⟨ordered, within, fits⟩).elim

theorem seqSized_defined {item : V.Ty} {size : Nat} {free : Ty.isLinear V item = false}
    (xs : M.Val (.seq item none))
    (holds : ∀ req, req ∈ (ownedContract .seqSized).requires [.seq item (some size)] →
      Holds (table := table) [⟨.seq item none, xs⟩] req) :
    ∀ h, ownedOp M (.seqSized item size free) (.cons xs .nil) = .halt h → h ≠ .undefined := by
  intro h e
  have length : (xs : List (M.Val item)).length = size := by
    obtain ⟨vs, d, rel⟩ := holds
      (.exactly (.apply (lengthOfType (.seq item none)) [0]) size) (by simp [ownedContract])
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
      Holds (table := table) ((localSem M fns table).dyns a) req) :
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
      have hreq : ∀ req, req ∈ (ownedContract op.name.1).requires op.name.2.1 →
          Holds (table := table) ((localSem M fns table).dyns a) req := fun req m => holds req m
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
      op = .apply w ps → ∃ as rs, atPositions ((localSem M fns table).dyns a) ps = some as ∧
        ValidRun (localSem M fns table) (LocalReturns M table) (ValidDyn M) w as rs ∧
        rs.length = 1 := by
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
          refine ⟨(localSem M fns table).dyns a, _, ?_, localRun_domain_intro known hk a va, rfl⟩
          rw [← (localSem M fns table).dyns_length a, atPositions_range _ _ (Nat.le_refl _),
            List.take_length]
  | owned op =>
      simp only [LocalOp.print, localOpFacts] at m
      cases op
      case seqAt =>
        obtain ⟨xs, i, rfl⟩ := HList.two a
        rename_i size _
        cases size <;> simp [OwnedOp.name, ownedContract] at m <;> subst m <;>
          simp [Requirement.operands] at mo
        obtain ⟨rfl, rfl⟩ := mo
        exact ⟨_, _, rfl, localRun_length_intro ‹_› xs (HList.all_cons.mp va).1, rfl⟩
      case seqSlice =>
        obtain ⟨xs, first, second, rfl⟩ := HList.three a
        rename_i result _
        cases result <;> simp [OwnedOp.name, ownedContract] at m <;>
          rcases m with rfl | rfl | rfl <;> simp [Requirement.operands] at mo
        all_goals
          obtain ⟨rfl, rfl⟩ := mo
          exact ⟨_, _, rfl, localRun_length_intro ‹_› xs (HList.all_cons.mp va).1, rfl⟩
      case seqSized item _ free =>
        obtain ⟨xs, rfl⟩ := HList.one a
        simp [OwnedOp.name, ownedContract] at m
        subst m
        simp [Requirement.operands] at mo
        obtain ⟨rfl, rfl⟩ := mo
        exact ⟨_, _, rfl, localRun_length_intro free xs (HList.all_cons.mp va).1, rfl⟩
      all_goals simp [OwnedOp.name, ownedContract] at m
      all_goals subst m
      all_goals simp [Requirement.operands] at mo

end

end FactCheck

section
variable {V : Vocabulary} (M : Model V) {fns : List (FnHeader V)} (table : FnTable M fns)

/-- The equality of naturals as the core computes it (`Nat.beq`) does not depend on the order of
its operands. -/
theorem natEqual_symmetric (first second : Nat) : Nat.beq first second = Nat.beq second first :=
  Bool.eq_iff_iff.mpr (by simp only [Nat.beq_eq]; exact eq_comm)

/-- The local operations that are values satisfy the laws of the value form: one that is a
value returns what its printed form gives, or stops `undefined`; a printed form gives one
result; and a printed form that commutes, which is that of the sum or the product of naturals or
of an equality, whose meaning is symmetric in its two operands, gives the same result on them
exchanged. Its
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
    | true => simp [FactRules.values, localFactRules, stops] at written
    | false =>
        simp only [FactRules.values, localFactRules, stops, Bool.not_false, ↓reduceIte,
          Option.some.injEq] at written
        show (∃ results, localOp M table o values = .done results ∧ _) ∨
          ∃ stop, localOp M table o values = .halt stop ∧ stop = Stop.undefined
        have undefinedOnly := localOp_stops_undefined M table quiet o values stops
        cases ran : localOp M table o values with
        | done returned =>
            exact .inl ⟨returned, rfl, ins, res, o, values, returned, written, rfl, rfl, ran⟩
        | halt stop =>
            rw [ran] at undefinedOnly
            exact .inr ⟨stop, rfl, undefinedOnly⟩
        | call op _ => exact nomatch op
  functional := fun _ _ _ _ first second => FactCheck.localReturns_functional distinct first second
  commutative := by
    intro raw commutes first second results returns
    obtain ⟨ins, res, o, args, returned, printed, sameArgs, sameResults, ran⟩ := returns
    subst printed
    cases o with
    | row => simp [FactRules.values, localFactRules, LocalOp.print, LocalRaw.commutes] at commutes
    | literal => simp [FactRules.values, localFactRules, LocalOp.print, LocalRaw.commutes] at commutes
    | call => simp [FactRules.values, localFactRules, LocalOp.print, LocalRaw.commutes] at commutes
    | owned o =>
        cases o <;> simp [FactRules.values, localFactRules, LocalOp.print, OwnedOp.name,
          LocalRaw.commutes, ownedContract] at commutes
        all_goals
          rcases args with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
          have sameArgs : [(⟨_, a⟩ : (τ : V.Ty) × M.Val τ), ⟨_, b⟩] = [first, second] := sameArgs
          simp only [List.cons.injEq] at sameArgs
          obtain ⟨rfl, rfl, -⟩ := sameArgs
          refine ⟨_, _, .owned _, .cons b (.cons a .nil), returned, rfl, rfl, sameResults, ?_⟩
          rw [← ran]
          simp only [localOp, ownedOp, Nat.add_comm, Nat.mul_comm, Bool.beq_comm,
            natEqual_symmetric]

end

namespace Analysis

section
variable {V : Vocabulary} (M : Model V) {fns : List (FnHeader V)} (table : FnTable M fns)

/-- The law `collect` as first stated, without the length of the collected values, is false of
the function dialect: a sequence of a written size is valid only of that length. -/
theorem collect_without_length :
    ¬ ∀ (size : Option Nat) (a : V.Ty) (vs : List ((localSem M fns table).Val a)),
      (∀ v, v ∈ vs → ValidDyn M ⟨a, v⟩) →
      ValidDyn M
        ⟨(localDialect V fns).collected size a, (localSem M fns table).collect size a vs⟩ :=
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
they cannot stop (`Callees`), the rules of the function dialect are lawful for its semantics, for
any permitted replies. -/
theorem localFactRules_lawful (callees : Callees M table)
    (permitted : ∀ op, (localSem M fns table).S.Reply op → Prop) :
    (localFactRules V fns).Lawful (localSem M fns table) permitted (localReading M)
      (LocalReturns M table) (ValidDyn M) (· = .undefined) where
  binding := localFactRules_binding M table callees.distinct callees.quiet
  ops :=
    { functional := fun _ _ _ _ first second =>
        localReturns_functional callees.distinct first.1 second.1
      form := fun _ _ _ _ found run => localReturns_form found run.1
      ranges := fun _ _ _ known run hk => localRun_ranges known run hk }
  keeps := by
    intro raw operands results run valid
    obtain ⟨ins, res, o, args, returned, printed, sameArgs, sameResults, ran⟩ := run
    subst sameArgs sameResults
    exact ((localSem M fns table).dyns_valid_iff returned).mpr (localOp_valid table callees.keeps o
      args returned (((localSem M fns table).dyns_valid_iff args).mp valid) ran)
  defined := by
    intro ins res o shared key path values valid holds
    have stops : LocalOp.canStop o = false := by simpa [localFactRules] using shared
    have defined := localOp_defined callees.safe o values
      (((localSem M fns table).dyns_valid_iff values).mp valid) holds
    have onlyUndefined := localOp_stops_undefined M table callees.quiet o values stops
    show ∃ results, localOp M table o values = .done results
    cases hrun : localOp M table o values with
    | done r => exact ⟨r, rfl⟩
    | halt h =>
        rw [hrun] at defined onlyUndefined
        exact absurd onlyUndefined defined
    | call op _ => exact nomatch op
  named := fun o values valid req m operand mo w ps e =>
    localRequires_runs o values (((localSem M fns table).dyns_valid_iff values).mp valid) req m
      operand mo w ps e
  effect := by
    intro ins res o kept key path values valid _
    have va : values.All M.Valid := ((localSem M fns table).dyns_valid_iff values).mp valid
    cases o with
    | call callee =>
        have stops := callees.safe _ callee values va
        show (table _ callee values).Every permitted _ _
        cases hrun : table _ callee values with
        | done r =>
            exact ((localSem M fns table).dyns_valid_iff r).mpr
              (callees.keeps _ callee values r va hrun)
        | halt h =>
            rw [hrun] at stops
            exact stops
        | call op _ => exact nomatch op
    | row => simp [localFactRules, LocalOp.canStop] at kept
    | owned => simp [localFactRules, LocalOp.canStop] at kept
    | literal => simp [localFactRules, LocalOp.canStop] at kept
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
  pick := fun ok v valid => localPick_valid ok v valid
  index := fun _ _ => ⟨trivial, rfl⟩
  collect := localCollect_valid
  begin := fun _ _ _ => trivial
  settle := fun _ _ _ => trivial
  stop := fun _ _ _ => nofun

end

/-! ## The theorems of the analysis for a function -/

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
    (accepted : checkFacts (localFactRules V fns) (localRules fns).skel definition none inputs
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
  have safe := Analysis.analyse_safe (localFactRules V fns) (localRules fns).skel
    (localSem M fns table) (fun _ _ => True) (localReading M) (LocalReturns M table) (ValidDyn M)
    (· = .undefined)
    (localFactRules_lawful M table callees (fun _ _ => True))
    (Rules.skel_lawful (localRules_lawful callees.distinct)) definition none inputs body distinct
    refused F
    (fun p b m d r => List.mem_reverse.mp (recorded p b m d r))
    ins (((localSem M fns table).dyns_valid_iff ins).mpr valid)
  exact ⟨safe.1, Process.every_mono _ _
    (fun outs returned => ((localSem M fns table).dyns_valid_iff outs).mp returned)
    (fun _ stop => stop) safe.2⟩

open FactCheck Analysis in
/-- **A body of a function that follows a safe body is safe and means the same.** For two bodies
of the same types, of which the second has distinct addresses and follows the analysis of the
first with no refusal and no place that differs, against callees with distinct keys that never
stop `undefined` on valid inputs, keep validity and stop only `undefined` where their headers say
that they cannot stop, on valid inputs on which the first never stops `undefined`: every loop of
the second respects the bound recorded for it while it follows, the second never stops
`undefined` and returns valid values, and the two return the same (`Analysis.follow_assured`). -/
theorem localFollow_assured {table : FnTable M fns} (callees : Callees M table)
    (definition definition' : Key) {types outs : List V.Ty} (inputs inputs' : Names types)
    (body : Term (localDialect V fns) (Ctx.empty.extend inputs) outs)
    (body' : Term (localDialect V fns) (Ctx.empty.extend inputs') outs)
    (distinct' : Term.Distinct body')
    (followed : (follow (localFactRules V fns) (localRules fns).skel definition' none
      (analyse (localFactRules V fns) (localRules fns).skel definition none inputs body) inputs'
      body').accepted = true)
    (F : List (Place × Nat))
    (recorded : ∀ p b, (p, b) ∈ F → p.definition = definition' → p.role = none →
      (p, b) ∈ (follow (localFactRules V fns) (localRules fns).skel definition' none
        (analyse (localFactRules V fns) (localRules fns).skel definition none inputs body) inputs'
        body').state.st.bounds)
    (ins : HList M.Val types) (valid : ins.All M.Valid)
    (safe : (body.denote (localSem M fns table) [] (Env.empty.extend inputs ins)).Stops
      (· ≠ .undefined)) :
    body'.EveryLoop (localSem M fns table) (fun _ _ => True)
        (Annotation.Bounded ⟨F⟩ definition' none) [] [] (Env.empty.extend inputs' ins) ∧
      (body'.denote (localSem M fns table) [] (Env.empty.extend inputs' ins)).Every
        (fun _ _ => True) (fun outs => outs.All M.Valid) (· ≠ .undefined) ∧
      body.denote (localSem M fns table) [] (Env.empty.extend inputs ins) =
        body'.denote (localSem M fns table) [] (Env.empty.extend inputs' ins) := by
  have sound := follow_assured (localFactRules V fns) (localRules fns).skel (localSem M fns table)
    (fun _ _ => True) (localReading M) (LocalReturns M table) (ValidDyn M) (· = .undefined)
    (localFactRules_lawful M table callees _) (Rules.skel_lawful (localRules_lawful callees.distinct))
    definition
    definition' none inputs inputs' body body' distinct' followed F recorded ins
    (((localSem M fns table).dyns_valid_iff ins).mpr valid) safe
  exact ⟨sound.1, Process.every_mono _ _
      (fun outs returned => ((localSem M fns table).dyns_valid_iff outs).mp returned)
      (fun _ stop => stop) sound.2.1,
    sound.2.2.eq_of_noSig⟩

end

/-! ## A summary of a function is a contract -/

section
variable {V : Vocabulary} (M : Model V) {fns : List (FnHeader V)} (table : FnTable M fns)

/-- **A summary that holds of a function's entry is its contract.** For the function dialect,
read as the check of facts reads it (`localReading`, `LocalReturns`, the validity of the model
and the stop `undefined`), a summary holds of the entry of a function in a table exactly when
the entry has the contract (`Contract`, `Meaning/Call.lean`) whose precondition is valid inputs
that satisfy the requirements, whose postcondition is valid results that, with the inputs,
satisfy the guarantees, and whose stops are not `undefined`. -/
theorem localSummary_contract {hdr : FnHeader V} (callee : Member fns hdr)
    (summary : Summary (LocalRaw V)) :
    Summary.Holds (localSem M fns table) (fun _ _ => True) (localReading M) (LocalReturns M table)
        (ValidDyn M) (· = .undefined) summary (table hdr callee) ↔
      Contract M table callee
        (fun args => args.All M.Valid ∧ ∀ requirement, requirement ∈ summary.requires →
          requirement.Holds (LocalReturns M table) (localReading M)
            ((localSem M fns table).dyns args))
        (fun args results => results.All M.Valid ∧ ∀ guarantee, guarantee ∈ summary.ensures →
          guarantee.Holds (LocalReturns M table) (localReading M)
            ((localSem M fns table).dyns args ++ (localSem M fns table).dyns results))
        (fun _ stop => stop ≠ .undefined) := by
  constructor
  · intro holds
    refine ⟨fun args pre => ?_⟩
    exact Process.every_mono _ _
      (fun results returned => ⟨((localSem M fns table).dyns_valid_iff results).mp returned.1,
        returned.2⟩)
      (fun _ stop => stop)
      (holds args (((localSem M fns table).dyns_valid_iff args).mpr pre.1) pre.2)
  · intro contract inputs valid requirements
    exact Process.every_mono _ _
      (fun results returned => ⟨((localSem M fns table).dyns_valid_iff results).mpr returned.1,
        returned.2⟩)
      (fun _ stop => stop)
      (contract.holds inputs
        ⟨((localSem M fns table).dyns_valid_iff inputs).mp valid, requirements⟩)

end

end Zkc.Core
