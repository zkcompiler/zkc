module

public import ZkcFormal.Written.Source

@[expose] public section
set_option autoImplicit false

namespace ZkcFormal.Written
open Zkc.Core
variable {V : Vocabulary}

/-- Read the single output of a local Core execution. A stopped function has no result. -/
def functionResult {M : Model V} {t : V.Ty} : Local (HList M.Val [t]) → Option (M.Val t)
  | .done (.cons v .nil) => some v
  | .halt _ => none
  | .call op _ => nomatch op

/-- A process without effects that is judged to end with a value is that value, done: the law of
a function in the form in which a caller takes a computation by its law. -/
theorem done_of_judged {A : Type} {p : Local A} {value : A}
    (judged : p.interpret ProcessJudgment.silent (fun out _ => out = value)
      (fun _ _ => False) ()) :
    p = .done value := by
  match p, judged with
  | .done _, judged => exact congrArg Process.done judged
  | .halt _, judged => exact judged.elim
  | .call op _, _ => exact nomatch op

/-- A function whose process is judged to end with one value has that value as its result. The
judgment is of a process without effects, so the body of a function is walked as the program of
a role is, a loop by its rule (`Term.interpret_loop`) with an invariant. -/
theorem functionResult_of_judged {M : Model V} {t : V.Ty} {p : Local (HList M.Val [t])}
    {v : M.Val t}
    (judged : p.interpret ProcessJudgment.silent (fun out _ => out = .cons v .nil)
      (fun _ _ => False) ()) :
    functionResult p = some v := by
  match p, judged with
  | .done (.cons w .nil), judged =>
    have same : HList.cons w HList.nil = HList.cons v HList.nil := judged
    cases same
    rfl
  | .halt _, judged => exact judged.elim
  | .call op _, _ => exact nomatch op

variable {M : Model V} {fns : List (FnHeader V)} {Γ : Ctx V.Ty} {out : V.Ty}

theorem function_op {input mid : List V.Ty} {k : Key} {o : LocalOp V fns input mid}
    {args : HList (Var Γ) input} {ns : Names mid} {rest : Term (localDialect V fns) (Γ.extend ns) [out]}
    {table : FnTable M fns} {path : List Frame} {env : Env M.Val Γ} {goal : Option (M.Val out)}
    {values : HList M.Val mid}
    (step : localOp M table o (env.all args) = .done values)
    (tail : functionResult (rest.denote (localSem M _ table) path (env.extend ns values)) = goal) :
    functionResult ((Term.op k o args ns rest).denote (localSem M _ table) path env) = goal := by
  rw [Term.denote_op]
  change functionResult ((localOp M table o _).bind _) = _
  rw [step]
  exact tail

theorem function_row {key : V.RowKey} {sig} {known : V.row key = some sig} {table : FnTable M fns}
    {args : HList M.Val sig.ins} {values : HList M.Val sig.outs}
    (eq : M.apply key sig known args = some values) :
    localOp M table (.row key sig known) args = .done values := by simp [localOp, eq]

theorem function_guard {k : Key} {t : V.Ty} {c : Var Γ t} {ok : t = .bool} {why : Reason}
    {rest : Term (localDialect V fns) Γ [out]} {table : FnTable M fns} {path} {env : Env M.Val Γ}
    {goal : Option (M.Val out)}
    (yes : asBool M ok (env.get c) = true → functionResult (rest.denote (localSem M _ table) path env) = goal)
    (no : asBool M ok (env.get c) = false → none = goal) :
    functionResult ((Term.guard k () c ok why rest).denote (localSem M _ table) path env) = goal := by
  rw [Term.denote_guard]
  cases h : asBool M ok (env.get c) with
  | true => simpa only [localSem, h, Bool.cond_true] using yes h
  | false => simpa only [localSem, h, Bool.cond_false, functionResult] using no h

abbrev fr (row : Zkc.Vocabulary.FieldRow) (among := Zkc.Vocabulary.Among.all) : Standard.RowKey :=
  .inl (.field row .bls12381Fr among)
abbrev nzTy : Standard.Ty := .nominal (.inl (.nonzero .bls12381Fr))

/-- Laws for the scalar primitives of the compiled local functions. Nonzero elements
may have a different carrier from scalars. The round trip applies on their actual domain. -/
structure FunctionRows (M : Model Standard) (ops : Operations (M.Val scalarTy) (M.Val pointTy))
    [DecidableEq (M.Val scalarTy)] where
  pack : (x : M.Val scalarTy) → x ≠ ops.zero → M.Val nzTy
  unpack : M.Val nzTy → M.Val scalarTy
  invert : M.Val nzTy → M.Val nzTy
  sub : ∀ x y, M.apply (fr .sub) _ rfl (.cons x (.cons y .nil)) = some (.cons (ops.sub x y) .nil)
  mul : ∀ x y, M.apply (fr .mul) _ rfl (.cons x (.cons y .nil)) = some (.cons (ops.mul x y) .nil)
  equal : ∀ (x y : M.Val scalarTy), M.apply (fr .equal) _ rfl (.cons x (.cons y .nil)) =
    some (.cons (decide (x = y)) .nil)
  test : ∀ (x : M.Val scalarTy), M.apply (fr .isNonzero) _ rfl (.cons x .nil) = some (.cons (decide (x ≠ ops.zero)) .nil)
  refine : ∀ (x : M.Val scalarTy), M.apply (fr .nonzero) _ rfl (.cons x .nil) =
    (if h : x = ops.zero then none else some (.cons (pack x h) .nil) : Option (HList M.Val [nzTy]))
  inverse : ∀ x, M.apply (fr .inverse .nonzero) _ rfl (.cons x .nil) = some (.cons (invert x) .nil)
  forget : ∀ x, M.apply (fr .fromNonzero .nonzero) _ rfl (.cons x .nil) = some (.cons (unpack x) .nil)
  roundTrip : ∀ x (h : x ≠ ops.zero), unpack (pack x h) = x
  inverseScalar : ∀ x, unpack (invert x) = ops.inv (unpack x)
  zero : ∀ h, Ty.readLiteral M scalarTy [0] h = ops.zero

theorem FunctionRows.refine_of_ne {M : Model Standard} {ops} [DecidableEq (M.Val scalarTy)]
    (rows : FunctionRows M ops) {x : M.Val scalarTy} (nonzero : x ≠ ops.zero) :
    M.apply (fr .nonzero) _ rfl (.cons x .nil) = some (.cons (rows.pack x nonzero) .nil) := by
  exact (rows.refine x).trans (dite_eq_right nonzero)

end ZkcFormal.Written
