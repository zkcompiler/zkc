module

public import Zkc.Core.Facts.Local
public import Zkc.Core.Meaning.ValidValues
public import Zkc.Core.Meaning.Validity
public import Zkc.Core.Meaning.Stops
public import Zkc.Core.Evidence.Summary
public import Zkc.Core.Evidence.Subject

@[expose] public section

namespace Zkc.Core

namespace FactCheck

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

/-- An operation that the core owns, a row and a literal guarantee nothing yet: only a call
guarantees, what the summary of its callee's header says. -/
theorem localOpFacts_ensures {V : Vocabulary} {fns : List (FnHeader V)} (w : LocalRaw V)
    (notCall : ∀ key, w ≠ .call key) : (localOpFacts fns).ensures w = [] := by
  cases w with
  | owned name _ _ => cases name <;> rfl
  | call key => exact absurd rfl (notCall key)
  | _ => rfl

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
    {f : ResultForm} (hf : (localOpFacts fns).form w = some f) (h : LocalReturns M table w as rs) :
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
    ∀ (i : Nat) (r : Range), ((localOpFacts fns).ranges w known)[i]? = some (some r) →
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

/-- What an order says of two naturals. -/
theorem relation_le {o o' : Operand (LocalRaw V)} {x y : Nat}
    (h : (Requirement.le o o').Relation (localReading M)
      [(⟨.nat, x⟩ : (τ : V.Ty) × M.Val τ), ⟨.nat, y⟩]) : x ≤ y := by
  obtain ⟨a, b, ha, hb, le⟩ := h
  have ea : x = a := Option.some.inj ha
  have eb : y = b := Option.some.inj hb
  subst ea eb
  exact le

/-- What a strict order says of two naturals. -/
theorem relation_lt {o o' : Operand (LocalRaw V)} {x y : Nat}
    (h : (Requirement.lt o o').Relation (localReading M)
      [(⟨.nat, x⟩ : (τ : V.Ty) × M.Val τ), ⟨.nat, y⟩]) : x < y := by
  obtain ⟨a, b, ha, hb, lt⟩ := h
  have ea : x = a := Option.some.inj ha
  have eb : y = b := Option.some.inj hb
  subst ea eb
  exact lt

/-- What a lower bound says of a natural. -/
theorem relation_atLeast {o : Operand (LocalRaw V)} {n x : Nat}
    (h : (Requirement.atLeast o n).Relation (localReading M)
      [(⟨.nat, x⟩ : (τ : V.Ty) × M.Val τ)]) : n ≤ x := by
  obtain ⟨a, ha, le⟩ := h
  have ea : x = a := Option.some.inj ha
  subst ea
  exact le

/-- What an upper bound says of a natural. -/
theorem relation_below {o : Operand (LocalRaw V)} {n x : Nat}
    (h : (Requirement.below o n).Relation (localReading M)
      [(⟨.nat, x⟩ : (τ : V.Ty) × M.Val τ)]) : x < n := by
  obtain ⟨a, ha, lt⟩ := h
  have ea : x = a := Option.some.inj ha
  subst ea
  exact lt

/-- What a number says of a natural. -/
theorem relation_exactly {o : Operand (LocalRaw V)} {n x : Nat}
    (h : (Requirement.exactly o n).Relation (localReading M)
      [(⟨.nat, x⟩ : (τ : V.Ty) × M.Val τ)]) : x = n := by
  obtain ⟨a, ha, same⟩ := h
  have ea : x = a := Option.some.inj ha
  subst ea
  exact same

/-- What a difference says of two naturals. -/
theorem relation_difference {o o' : Operand (LocalRaw V)} {n x y : Nat}
    (h : (Requirement.difference o o' n).Relation (localReading M)
      [(⟨.nat, x⟩ : (τ : V.Ty) × M.Val τ), ⟨.nat, y⟩]) : x - y = n := by
  obtain ⟨a, b, ha, hb, same⟩ := h
  have ea : x = a := Option.some.inj ha
  have eb : y = b := Option.some.inj hb
  subst ea eb
  exact same

theorem natSub_defined (x y : Nat)
    (holds : ∀ req, req ∈ (ownedContract (V := V) .natSub).requires [] →
      Holds (table := table) [⟨.nat, x⟩, ⟨.nat, y⟩] req) :
    ∀ h, ownedOp M (.natSub (V := V)) (.cons x (.cons y .nil)) = .halt h → h ≠ .undefined := by
  intro h e
  have le := relation_le (holds_args (u := ⟨.nat, y⟩) (v := ⟨.nat, x⟩) rfl rfl rfl
    (holds (.le (.arg 1) (.arg 0)) (by simp [ownedContract])))
  simp [ownedOp, le] at e

theorem natDiv_defined (x y : Nat)
    (holds : ∀ req, req ∈ (ownedContract (V := V) .natDiv).requires [] →
      Holds (table := table) [⟨.nat, x⟩, ⟨.nat, y⟩] req) :
    ∀ h, ownedOp M (.natDiv (V := V)) (.cons x (.cons y .nil)) = .halt h → h ≠ .undefined := by
  intro h e
  have pos := relation_atLeast (holds_arg (u := ⟨.nat, y⟩) rfl rfl
    (holds (.atLeast (.arg 1) 1) (by simp [ownedContract])))
  simp [ownedOp, pos] at e

theorem natRem_defined (x y : Nat)
    (holds : ∀ req, req ∈ (ownedContract (V := V) .natRem).requires [] →
      Holds (table := table) [⟨.nat, x⟩, ⟨.nat, y⟩] req) :
    ∀ h, ownedOp M (.natRem (V := V)) (.cons x (.cons y .nil)) = .halt h → h ≠ .undefined := by
  intro h e
  have pos := relation_atLeast (holds_arg (u := ⟨.nat, y⟩) rfl rfl
    (holds (.atLeast (.arg 1) 1) (by simp [ownedContract])))
  simp [ownedOp, pos] at e

theorem natBelow_defined (bound n : Nat)
    (holds : ∀ req, req ∈ (ownedContract (V := V) .natBelow).requires [.fin bound] →
      Holds (table := table) [⟨.nat, n⟩] req) :
    ∀ h, ownedOp M (.natBelow (V := V) bound) (.cons n .nil) = .halt h → h ≠ .undefined := by
  intro h e
  have lt := relation_below (holds_arg (u := ⟨.nat, n⟩) rfl rfl
    (holds (.below (.arg 0) bound) (by simp [ownedContract])))
  simp [ownedOp, lt] at e

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
        have := relation_below (holds_arg (u := ⟨.nat, i⟩) rfl rfl
          (holds (.below (.arg 1) size) (by simp [ownedContract])))
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
        exact relation_lt rel
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
  have ordered := relation_le (holds_args (u := ⟨.nat, first⟩) (v := ⟨.nat, second⟩) rfl rfl rfl
    (holds (.le (.arg 1) (.arg 2)) (by simp [ownedContract])))
  have within : second ≤ (xs : List (M.Val item)).length := by
    obtain ⟨vs, d, rel⟩ := holds (.le (.arg 2) (.apply (lengthOfType (.seq item size)) [0]))
      (by simp [ownedContract])
    obtain ⟨u, v, rfl, d1, d2⟩ := DenotesAll.two d
    simp only [Operand.Denotes, List.getElem?_cons_succ, List.getElem?_cons_zero,
      Option.some.injEq] at d1
    subst d1
    rw [denotes_length d2] at rel
    exact relation_le rel
  have fits : fitsSize result (second - first) = true := by
    cases result with
    | none => rfl
    | some count =>
        have := relation_difference (holds_args (u := ⟨.nat, second⟩) (v := ⟨.nat, first⟩) rfl
          rfl rfl (holds (.difference (.arg 2) (.arg 1) count) (by simp [ownedContract])))
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
    exact relation_exactly rel
  simp [ownedOp, length] at e

/-- A call uses the actual stored header, including expression pre- and postconditions. -/
theorem localCall_holds (callees : Callees M table) {hdr : FnHeader V} (callee : Member fns hdr)
    (args : HList M.Val hdr.ins) (valid : args.All M.Valid)
    (holds : FnHeader.Required M table hdr args) :
    (table hdr callee args).Every (fun _ _ => True)
      (fun results => results.All M.Valid ∧
        ∀ guarantee ∈ hdr.summary.ensures, guarantee.Holds M
          ((localSem M fns table).dyns args ++ (localSem M fns table).dyns results))
      (· ≠ .undefined) :=
  Process.every_mono _ _
    (fun results post => ⟨((localSem M fns table).dyns_valid_iff results).mp post.1, post.2⟩)
    (fun _ stop => stop)
    (callees.satisfies hdr callee args (((localSem M fns table).dyns_valid_iff args).mpr valid) holds)

/-- An operation that the core owns, applied to valid operands at whose values every requirement
of its contract holds (`ownedContract`), does not stop `undefined`. -/
theorem ownedOp_defined {ins res : List V.Ty} (o : OwnedOp V ins res) (a : HList M.Val ins)
    (va : a.All M.Valid)
    (hreq : ∀ req, req ∈ (ownedContract o.name.1).requires o.name.2.1 →
      Holds (table := table) ((localSem M fns table).dyns a) req) :
    (ownedOp M o a).Stops (· ≠ .undefined) := by
  apply Local.stops_of_halts
  intro h e
  cases o
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
  case takeSeq item count =>
    obtain ⟨xs, rfl⟩ := HList.one a
    have sized : xs.length = count := (HList.all_cons.mp va).1.2 count rfl
    simp [ownedOp, sized] at e
  case seqSized =>
    obtain ⟨xs, rfl⟩ := HList.one a
    exact seqSized_defined xs hreq h e
  all_goals first
    | (obtain ⟨x, y, z, rfl⟩ := HList.three a; simp [ownedOp] at e)
    | (obtain ⟨x, y, rfl⟩ := HList.two a; simp [ownedOp] at e)
    | (obtain ⟨x, rfl⟩ := HList.one a; simp [ownedOp] at e)
    | simp [ownedOp] at e

/-- Typed calls read the callee they reference. Builtins read their arithmetic or row domains. -/
def LocalRequired {ins res : List V.Ty} (o : LocalOp V fns ins res) (a : HList M.Val ins) : Prop :=
  match o with
  | .call (hdr := hdr) _ => FnHeader.Required M table hdr a
  | op => ∀ req ∈ (localOpFacts fns).requires op.print,
      Holds (table := table) ((localSem M fns table).dyns a) req

/-- A local operation, applied to valid operands at whose values every requirement of its
written form holds, does not stop `undefined`, against callees that satisfy their summaries. -/
theorem localOp_defined (callees : Callees M table)
    {ins res : List V.Ty} (o : LocalOp V fns ins res) (a : HList M.Val ins)
    (va : a.All M.Valid)
    (holds : LocalRequired (table := table) o a) :
    (localOp M table o a).Stops (· ≠ .undefined) := by
  cases o with
  | literal => exact trivial
  | call callee =>
      exact Process.every_mono _ _ (fun _ _ => trivial) (fun _ stop => stop)
        (localCall_holds callees callee a va holds)
  | row key sig known =>
      obtain ⟨outs, h⟩ := row_defined key sig known a (fun req m => holds req m)
      simp only [localOp, h]
      exact trivial
  | owned op => exact ownedOp_defined op a va fun req m => holds req m

end

end FactCheck

/-- The equality of naturals as the core computes it (`Nat.beq`) does not depend on the order of
its operands. -/
theorem natEqual_symmetric (first second : Nat) : Nat.beq first second = Nat.beq second first :=
  Bool.eq_iff_iff.mpr (by simp only [Nat.beq_eq]; exact eq_comm)

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

/-! ## What an operation yields -/

section
variable {V : Vocabulary} {M : Model V} {fns : List (FnHeader V)} {table : FnTable M fns}

open FactCheck in
/-- **An operation that the core owns yields its result where its requirements hold.** On the
authorized starts at which the operands' values are valid and satisfy every requirement of the
operation's contract (`ownedContract`), read with the relation of written operations, the subject
of an application returns exactly what the operation gives: the function `model` of the operands'
values, for any `model` that agrees with the operation wherever the operation returns. -/
theorem ownedOp_yields {Γ : Ctx V.Ty} {ins outs : List V.Ty} (key : Key) (o : OwnedOp V ins outs)
    (operands : HList (Var Γ) ins) (entry : Entry (localSem M fns table) Γ)
    (model : HList M.Val ins → HList M.Val outs)
    (gives : ∀ args results, ownedOp M o args = .done results → model args = results)
    (valid : ∀ path env, entry path env → (env.all operands).All M.Valid)
    (required : ∀ path env, entry path env → ∀ requirement,
      requirement ∈ (ownedContract o.name.1).requires o.name.2.1 →
        Holds (table := table) ((localSem M fns table).dyns (env.all operands)) requirement) :
    (Subject.op (localSem M fns table) key (LocalOp.owned o) operands).Yields
      (localSem M fns table) entry (fun env => model (env.all operands)) := by
  intro path env authorized
  have defined := ownedOp_defined o (env.all operands) (valid path env authorized)
    (required path env authorized)
  have onlyUndefined := Local.stops_of_halts _ (ownedOp_halts M o (env.all operands))
  show ownedOp M o (env.all operands) = .done (model (env.all operands))
  cases ran : ownedOp M o (env.all operands) with
  | done results => rw [gives _ _ ran]
  | halt stop =>
      rw [ran] at defined onlyUndefined
      exact absurd onlyUndefined defined
  | call op _ => exact nomatch op

/-- **A row of the vocabulary that is not restricted yields what the model gives**, from every
start: the model's row is defined on every input, and the subject of an application returns the
function `model` of the operands' values, for any `model` that agrees with the row wherever the
model gives it. -/
theorem row_yields {Γ : Ctx V.Ty} (key : Key) (row : V.RowKey)
    (signature : RowSignature V.TypeKey V.RowKey) (known : V.row row = some signature)
    (unrestricted : signature.kind = .pure) (operands : HList (Var Γ) signature.ins)
    (entry : Entry (localSem M fns table) Γ)
    (model : HList M.Val signature.ins → HList M.Val signature.outs)
    (gives : ∀ args results, M.apply row signature known args = some results →
      model args = results) :
    (Subject.op (localSem M fns table) key (LocalOp.row row signature known) operands).Yields
      (localSem M fns table) entry (fun env => model (env.all operands)) := by
  intro path env _
  have defined := M.defined row signature known (env.all operands)
  rw [M.total row signature known _ unrestricted] at defined
  show localOp M table (.row row signature known) (env.all operands) =
    .done (model (env.all operands))
  cases applied : M.apply row signature known (env.all operands) with
  | none =>
      rw [applied] at defined
      cases defined
  | some results =>
      simp only [localOp, applied]
      rw [gives _ _ applied]

end

end Zkc.Core
