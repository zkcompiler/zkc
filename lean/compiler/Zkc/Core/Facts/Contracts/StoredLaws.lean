module

public import Zkc.Core.Facts.Contracts.HeaderPredicates
public import Zkc.Core.Facts.Contracts.TypeLaws
public import Zkc.Core.Facts.Contracts.Stability

@[expose] public section

namespace Zkc.Core.BodyAnalysis.HeaderContracts
variable {V : Vocabulary} (M : Model V) {fns : List (FnHeader V)} (table : FnTable M fns)
variable {args : List (localSem M fns table).Dyn} {types : List V.Ty}
    (actual : ArgumentsMatch (TypedValue (localSem M fns table) (ValidDyn M)) args types)

private theorem atPosition {a : Operand Empty} {v} :
    a.Denotes Empty.elim args v ↔ args[position a]? = some v := by
  cases a with
  | arg => rfl
  | apply impossible => cases impossible

private theorem oldOne {q : Requirement Empty} {a : Operand Empty} {v} (ops : q.operands = [a])
    (read : args[position a]? = some v) :
    q.Holds Empty.elim (localReading M) args ↔ q.Relation (localReading M) [v] := by
  constructor
  · rintro ⟨_, den, rel⟩
    rw [ops] at den
    obtain ⟨w,rfl,atW⟩ := DenotesAll.one den
    obtain rfl := Option.some.inj (read.symm.trans ((atPosition M table).mp atW))
    exact rel
  · intro rel
    refine ⟨[v], ?_, rel⟩
    rw [ops]
    exact ⟨(atPosition M table).mpr read,trivial⟩

private theorem oldTwo {q : Requirement Empty} {a b : Operand Empty} {v w} (ops : q.operands = [a,b])
    (left : args[position a]? = some v) (right : args[position b]? = some w) :
    q.Holds Empty.elim (localReading M) args ↔ q.Relation (localReading M) [v,w] := by
  constructor
  · rintro ⟨_, den, rel⟩
    rw [ops] at den
    obtain ⟨x,y,rfl,ax,by_⟩ := DenotesAll.two den
    obtain rfl := Option.some.inj (left.symm.trans ((atPosition M table).mp ax))
    obtain rfl := Option.some.inj (right.symm.trans ((atPosition M table).mp by_))
    exact rel
  · intro rel
    refine ⟨[v,w], ?_, rel⟩
    rw [ops]
    exact ⟨(atPosition M table).mpr left, (atPosition M table).mpr right,trivial⟩

include actual in
private theorem natural_sound {operand : Operand Empty} {expr : Assertion V}
    (found : natural types operand = some expr) :
    ∃ v n, args[position operand]? = some v ∧ (localReading M).nat v = some n ∧
      expr.Denotes (Runs M table) args ⟨.nat,n⟩ := by
  unfold natural at found
  obtain ⟨t, atType, resolved⟩ := Option.bind_eq_some_iff.mp found
  obtain ⟨⟨u,x⟩, atValue, valid, same⟩ := actual.lookup atType
  change u = t at same
  subst u
  split at resolved
  · cases resolved
    exact ⟨_,x,atValue,rfl,.arg atValue⟩
  · cases resolved
    exact ⟨_,x,atValue,rfl,fin_denotes M table (.arg atValue) valid⟩
  · cases resolved

include actual in
/-- Exact interpretation of every successfully translated header clause on valid arguments
with their declared types. The statement includes standalone truncated differences. -/
theorem clause_value {q : Requirement Empty} {c : Clause V}
    (found : clause types q = some c) :
    ∃ b : Bool, c.assertion.Denotes (Runs M table) args ⟨.bool,b⟩ ∧
      (b = true ↔ q.Holds Empty.elim (localReading M) args) := by
  cases q with
  | le a b =>
    obtain ⟨eb, fb, ea, fa, eq⟩ := (by
      simpa only [clause, clauseWith, boolean, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] using found)
    cases eq
    obtain ⟨va,x,ra,na,da⟩ := natural_sound M table actual fa
    obtain ⟨vb,y,rb,nb,db⟩ := natural_sound M table actual fb
    refine ⟨_, (negate_denotes M table (less_denotes M table db da)), ?_⟩
    rw [oldTwo M table rfl ra rb]
    simp [Requirement.Relation, na, nb]
  | lt a b =>
    simp only [clause, clauseWith, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at found
    obtain ⟨ea,fa,eb,fb,eq⟩ := found
    cases eq
    obtain ⟨va,x,ra,na,da⟩ := natural_sound M table actual fa
    obtain ⟨vb,y,rb,nb,db⟩ := natural_sound M table actual fb
    refine ⟨_, (less_denotes M table da db), ?_⟩
    rw [oldTwo M table rfl ra rb]
    simp [Requirement.Relation, na, nb]
  | atLeast a n =>
    simp only [clause, clauseWith, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at found
    obtain ⟨ea,fa,eq⟩ := found
    cases eq
    obtain ⟨va,x,ra,na,da⟩ := natural_sound M table actual fa
    rw [oldOne M table rfl ra]
    cases n with
    | zero =>
      exact ⟨_,equal_denotes M table da da,by simp [Requirement.Relation, na]⟩
    | succ n =>
      exact ⟨_,less_denotes M table (number_denotes M table n) da,by simp [Requirement.Relation, na, Nat.succ_le_iff]⟩
  | below a n =>
    simp only [clause, clauseWith, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at found
    obtain ⟨ea,fa,eq⟩ := found
    cases eq
    obtain ⟨va,x,ra,na,da⟩ := natural_sound M table actual fa
    refine ⟨_, (less_denotes M table da (number_denotes M table n)), ?_⟩
    rw [oldOne M table rfl ra]
    simp [Requirement.Relation, na]
  | exactly a n =>
    simp only [clause, clauseWith, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at found
    obtain ⟨ea,fa,eq⟩ := found
    cases eq
    obtain ⟨va,x,ra,na,da⟩ := natural_sound M table actual fa
    refine ⟨_, (equal_denotes M table da (number_denotes M table n)), ?_⟩
    rw [oldOne M table rfl ra]
    simp [Requirement.Relation, na]
  | difference b a n =>
    simp only [clause, clauseWith, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at found
    obtain ⟨eb,fb,ea,fa,eq⟩ := found
    cases eq
    obtain ⟨vb,x,rb,nb,db⟩ := natural_sound M table actual fb
    obtain ⟨va,y,ra,na,da⟩ := natural_sound M table actual fa
    rw [oldTwo M table rfl rb ra]
    cases n with
    | zero =>
      simp only [↓reduceIte]
      refine ⟨_, (negate_denotes M table (less_denotes M table da db)), ?_⟩
      simp [Requirement.Relation, nb, na, Nat.sub_eq_zero_iff_le]
    | succ n =>
      simp only [Nat.succ_ne_zero, ↓reduceIte]
      refine ⟨_, (equal_denotes M table (add_denotes M table da (number_denotes M table (n+1))) db), ?_⟩
      simp [Requirement.Relation, nb, na]
      constructor
      · intro same
        omega
      · intro same
        omega
  | holds a =>
    simp only [clause, clauseWith, boolean, Option.bind_eq_bind, Option.bind_eq_some_iff] at found
    obtain ⟨_, ⟨ty, atType, guardOK⟩, eq⟩ := found
    cases eq
    by_cases isBool : ty = .bool
    · subst ty
      simp [guard] at guardOK
      subst_vars
      obtain ⟨⟨u,b⟩,atValue,_,same⟩ := actual.lookup atType
      change u = .bool at same
      subst u
      refine ⟨_, (Expr.Denotes.arg atValue), ?_⟩
      rw [oldOne M table rfl atValue]
      simp [Requirement.Relation, localReading]
    · simp [guard,isBool] at guardOK
  | bounded a =>
    simp only [clause, clauseWith, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at found
    obtain ⟨ea,fa,eq⟩ := found
    cases eq
    obtain ⟨va,x,ra,na,da⟩ := natural_sound M table actual fa
    refine ⟨_, (equal_denotes M table da da), ?_⟩
    rw [oldOne M table rfl ra]
    simp [Requirement.Relation, na]

include actual in
theorem clause_exact (distinct : (fns.map (·.key)).Nodup) {q : Requirement Empty} {c : Clause V}
    (found : clause types q = some c) :
    c.assertion.Holds (Runs M table) (localReading M) args ↔ q.Holds Empty.elim (localReading M) args := by
  obtain ⟨_,den,eq⟩ := clause_value M table actual found
  exact (holds_iff M table distinct den).trans eq

/-- Successful list translation preserves precisely the conjunction of the original clauses. -/
theorem mapM_all {A B : Type} (f : A → Option B) (P : A → Prop) (Q : B → Prop)
    (exactly : ∀ a b, f a = some b → (Q b ↔ P a)) :
    ∀ (xs : List A) {ys : List B}, xs.mapM f = some ys → ((∀ y ∈ ys, Q y) ↔ ∀ x ∈ xs, P x)
  | [], _, found => by cases found; simp
  | x :: xs, _, found => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at found
    obtain ⟨y, first, ys, rest, eq⟩ := found
    cases eq
    simpa only [List.mem_cons, forall_eq_or_imp] using and_congr (exactly x y first) (mapM_all f P Q exactly xs rest)

mutual
  theorem infer_stable {ctx : List V.Ty} : ∀ (e : Assertion V) {ty},
      (stableTypes V).infer ctx e = some ty → e.UsesOnly tableIndependent = true
    | .arg _, _, _ => rfl
    | .apply op operands port, _, ok => by
      obtain ⟨ins, args, outs, sig, _⟩ := (by
        simpa only [AssertionTypes.infer, Option.bind_eq_bind, Option.bind_eq_some_iff] using ok)
      apply Bool.and_eq_true_iff.mpr
      refine ⟨?_, inferAll_stable operands args⟩
      cases op <;> first | rfl | simp [stableTypes, localAssertionTypes, AssertionTypes.ofReader,
        stableAllowed, resolveLocal, Member.withKey] at sig
  theorem inferAll_stable {ctx : List V.Ty} : ∀ (es : Exprs (LocalRaw V)) {ts},
      (stableTypes V).inferAll ctx es = some ts → es.UsesOnly tableIndependent = true
    | .nil, _, _ => rfl
    | .cons e es, _, ok => by
      obtain ⟨_, head, _, tail, _⟩ := (by simpa only [AssertionTypes.inferAll,
        Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] using ok)
      exact Bool.and_eq_true_iff.mpr ⟨infer_stable e head, inferAll_stable es tail⟩
end

theorem expression_checked {ctx : List V.Ty} {source c : Clause V}
    (ok : checkClause ctx (.assertion source) = some c) :
    c = source ∧ (stableTypes V).infer ctx c.assertion = some .bool ∧
      c.staticBound.all (fun e => ((stableTypes V).infer ctx e).any numeric) = true := by
  simp only [checkClause] at ok
  split at ok
  · cases ok
    simp_all
  · cases ok

include actual in
theorem clauses_exact (distinct : (fns.map (·.key)).Nodup) {qs : List (HeaderClause V)} {cs : List (Clause V)}
    (translated : qs.mapM (checkClause types) = some cs) :
    (∀ e ∈ cs.map ContractClause.assertion, e.Holds (Runs M table) (localReading M) args) ↔
      ∀ q ∈ qs, q.Holds M args := by
  simp only [List.forall_mem_map]
  apply mapM_all _ _ _ _ qs translated
  intro q c ok
  cases q with
  | positional q => exact clause_exact M table actual distinct ok
  | assertion source =>
    obtain ⟨rfl, typed, _⟩ := expression_checked ok
    have stable := infer_stable _ typed
    exact ⟨fun h => h.transport (validRun_transport M table (headerTable M)) stable,
      fun h => Expr.Holds.transport (validRun_transport M (headerTable M) table) h stable⟩

theorem appendArguments {T A : Type} {R : A → T → Prop} {a b s t}
    (left : ArgumentsMatch R a s) (right : ArgumentsMatch R b t) :
    ArgumentsMatch R (a ++ b) (s ++ t) := by
  induction left with
  | nil => exact right
  | cons one _ ih => exact .cons one ih

/-- An entire translated function summary constrains exactly the same valid calls and returns
as the original stored summary. This holds for every body execution with the given signature. -/
theorem translate_exact (distinct : (fns.map (·.key)).Nodup) {ins outs : List V.Ty}
    {old : HeaderSummary V} {new : Contract (LocalRaw V)} (translated : translate ins outs old = some new)
    (run : HList M.Val ins → Local (HList M.Val outs)) :
    new.HoldsWith (localSem M fns table) (fun _ _ => True) (localReading M)
        (Runs M table) (ValidDyn M) (· = .undefined) run ↔
      old.Holds M table run := by
  simp only [translate, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at translated
  obtain ⟨pre, before, post, after_, eq⟩ := translated
  cases eq
  constructor <;> intro held inputs valid required
  · have ai := ArgumentsMatch.ofValues (sem := localSem M fns table) inputs valid
    apply Process.every_mono _ _ _ (fun _ h => h) (held inputs valid ((clauses_exact M table ai distinct before).mpr required))
    intro ys validPost
    have ay := ArgumentsMatch.ofValues (sem := localSem M fns table) ys validPost.1
    exact ⟨validPost.1, (clauses_exact M table (appendArguments ai ay) distinct after_).mp validPost.2⟩
  · have ai := ArgumentsMatch.ofValues (sem := localSem M fns table) inputs valid
    apply Process.every_mono _ _ _ (fun _ h => h) (held inputs valid ((clauses_exact M table ai distinct before).mp required))
    intro ys validPost
    have ay := ArgumentsMatch.ofValues (sem := localSem M fns table) ys validPost.1
    exact ⟨validPost.1, (clauses_exact M table (appendArguments ai ay) distinct after_).mpr validPost.2⟩

private theorem unary_typed {ctx : List V.Ty} {e : Assertion V} {op t out}
    (sig : (stableTypes V).signature op [t] = some [out]) (ok : (stableTypes V).infer ctx e = some t) :
    (stableTypes V).infer ctx (unary op e) = some out := by
  simp [unary, AssertionTypes.infer, AssertionTypes.inferAll, ok, sig]

private theorem binary_typed {ctx : List V.Ty} {a b : Assertion V} {op x y out}
    (sig : (stableTypes V).signature op [x,y] = some [out]) (left : (stableTypes V).infer ctx a = some x)
    (right : (stableTypes V).infer ctx b = some y) :
    (stableTypes V).infer ctx (binary op a b) = some out := by
  simp [binary, AssertionTypes.infer, AssertionTypes.inferAll, left, right, sig]

private theorem natural_typed {ctx : List V.Ty} {o e} (ok : natural ctx o = some e) :
    (stableTypes V).infer ctx e = some .nat := by
  obtain ⟨ty, pos, found⟩ := Option.bind_eq_some_iff.mp ok
  split at found <;> cases found
  · exact pos
  · apply unary_typed (e := .arg _) _ pos
    simp [stableTypes, localAssertionTypes, AssertionTypes.ofReader, stableAllowed, resolveLocal,
      localRules, LocalOp.read, LocalOp.ofOperands, OwnedOp.resolve, localOpFacts, ownedContract,
      LocalOp.canStop, Except.toOption]

/-- Both computations in a stored clause have their declared result kinds. -/
def WellTyped (ctx : List V.Ty) (c : Clause V) : Prop :=
  (stableTypes V).infer ctx c.assertion = some .bool ∧
    ∀ e, c.staticBound = some e → ∃ ty, (stableTypes V).infer ctx e = some ty ∧ numeric ty = true

private theorem legacy_typed {ctx : List V.Ty} {q c} (ok : clause ctx q = some c) : WellTyped ctx c := by
  have num (n : Nat) : (stableTypes V).infer ctx (number n) = some .nat := rfl
  have eq {a b} := @binary_typed V ctx a b (.owned .natEqual [] []) .nat .nat .bool rfl
  have lt {a b} := @binary_typed V ctx a b (.owned .natLess [] []) .nat .nat .bool rfl
  have plus {a b} := @binary_typed V ctx a b (.owned .natAdd [] []) .nat .nat .nat rfl
  have neg {a} := @unary_typed V ctx a (.owned .boolNot [] []) .bool .bool rfl
  cases q <;> simp only [clause, clauseWith, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq] at ok
  case holds =>
    obtain ⟨e, read, rfl⟩ := ok
    simp only [boolean, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at read
    obtain ⟨t, pos, pass⟩ := read
    by_cases good : t = .bool <;> simp [guard, good] at pass
    subst_vars
    exact ⟨pos, by simp⟩
  case le | lt | difference =>
    obtain ⟨x, one, y, two, rfl⟩ := ok
    have left := natural_typed one
    have right := natural_typed two
    first
    | exact ⟨neg (lt left right), by simp⟩
    | exact ⟨lt left right, by simp⟩
    | split
      · exact ⟨neg (lt right left), by simp⟩
      · exact ⟨eq (plus right (num _)) left, by simp⟩
  all_goals
    obtain ⟨x, one, rfl⟩ := ok
    have typed := natural_typed one
  case atLeast n => cases n with
    | zero => exact ⟨eq typed typed, by simp⟩
    | succ n => exact ⟨lt (num n) typed, by simp⟩
  case below => exact ⟨lt typed (num _), by simp⟩
  case exactly => exact ⟨eq typed (num _), by simp⟩
  case bounded => exact ⟨eq typed typed, fun _ h => Option.some.inj h ▸ ⟨.nat, typed, rfl⟩⟩

theorem checked_typed {ctx : List V.Ty} {q c} (ok : checkClause ctx q = some c) : WellTyped ctx c := by
  cases q with
  | positional q => exact legacy_typed ok
  | assertion source =>
    obtain ⟨_, typed, bounds⟩ := expression_checked ok
    exact ⟨typed, fun e at_ => (Option.any_eq_true ..).mp ((Option.all_eq_true ..).mp bounds e at_)⟩

theorem translate_typed {ins outs : List V.Ty} {old new} (read : translate ins outs old = some new) :
    (∀ c ∈ new.preconditions, WellTyped ins c) ∧ (∀ c ∈ new.postconditions, WellTyped (ins ++ outs) c) := by
  have clauses {ctx : List V.Ty} {qs : List (HeaderClause V)} {cs}
      (read : qs.mapM (checkClause ctx) = some cs) : ∀ c ∈ cs, WellTyped ctx c :=
    (mapM_all _ (fun _ => True) _ (fun _ _ h => iff_true_intro (checked_typed h)) qs read).mpr (by simp)
  simp only [translate, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at read
  obtain ⟨_, pre, _, post, rfl⟩ := read
  exact ⟨clauses pre, clauses post⟩

/-- Bounds are operational obligations. Their values also transport across arbitrary tables. -/
theorem bound_stable {ctx : List V.Ty} {c : Clause V} (w : WellTyped ctx c) {e}
    (bound : c.staticBound = some e) : e.UsesOnly tableIndependent = true := by
  obtain ⟨_, typed, _⟩ := w.2 e bound
  exact infer_stable _ typed

/-- Every translated predicate is independent of the surrounding function table. -/
theorem translate_stable {ins outs : List V.Ty} {old new} (found : translate ins outs old = some new) :
    new.UsesOnly tableIndependent = true := by
  obtain ⟨before, after_⟩ := translate_typed found
  simp only [Contract.UsesOnly, Contract.requires, Contract.ensures, Bool.and_eq_true,
    List.all_eq_true, List.forall_mem_map]
  exact ⟨fun c m => infer_stable _ (before c m).1, fun c m => infer_stable _ (after_ c m).1⟩

/-- On a positional header the certified translation has the same success, failure and
resulting clauses as mapping the original clause reader over each side. -/
theorem translate_ofPositional (ins outs : List V.Ty) (s : Summary Empty) :
    translate ins outs (.ofPositional s) = (do
      let before ← s.requires.mapM (clause ins)
      let after_ ← s.ensures.mapM (clause (ins ++ outs))
      pure ⟨before, after_⟩) := by
  simp [translate, HeaderSummary.ofPositional, Function.comp_def, checkClause]

/-- Equivalence to the original positional judgment for any implementation and callee table. -/
theorem positional_exact (M : Model V) {hs : List (FnHeader V)} (table : FnTable M hs)
    {ins outs : List V.Ty} (s : Summary Empty) {c : Contract (LocalRaw V)}
    (ok : translate ins outs (.ofPositional s) = some c)
    (run : HList M.Val ins → Local (HList M.Val outs)) :
    c.HoldsWith (localSem M hs table) (fun _ _ => True) (localReading M) (Runs M table)
        (ValidDyn M) (· = .undefined) run ↔
      s.Holds (localSem M hs table) (fun _ _ => True) (localReading M) Empty.elim
        (ValidDyn M) (· = .undefined) run := by
  have stable := translate_stable ok
  have fixed := translate_exact M (headerTable M) List.nodup_nil ok run
  rw [← HeaderSummary.positional_iff M table s run]
  exact ⟨fun h => HeaderSummary.holds_tables (fixed.mp
      (Contract.holds_tables M table (headerTable M) c stable run h)),
    fun h => Contract.holds_tables M (headerTable M) table c stable run
      (fixed.mpr (HeaderSummary.holds_tables h))⟩

section
variable (V : Vocabulary)
example : clause (V := V) [.fin 7] (.lt (.arg 0) (.arg 1)) = none := by rfl'
example : clause (V := V) [.nat] (.holds (.arg 0)) = none := by rfl'
example : ((clause (V := V) [.nat,.nat] (.difference (.arg 0) (.arg 1) 0)).map ContractClause.assertion) =
    some (negate (less (.arg 1) (.arg 0))) := by rfl'
example : ((clause (V := V) [.fin 4] (.bounded (.arg 0))).bind ContractClause.staticBound) =
    some (unary (.owned .finToNat [.fin 4] []) (.arg 0)) := by rfl'
example : ((translate (V := V) [.nat] [.nat] ⟨[.bounded (.arg 0)], [.bounded (.arg 1)]⟩).map
    (fun t => (t.preconditions.map ContractClause.staticBound, t.postconditions.map ContractClause.staticBound))) = some ([some (.arg 0)],[some (.arg 1)]) := by rfl'
end

#print axioms translate_stable
#print axioms translate_exact
#print axioms clause_exact
end Zkc.Core.BodyAnalysis.HeaderContracts
