module

public import ZkcFormal.Reading
public import ZkcFormal.Application
public import PolyFun.PFunctor.Free.Basic

@[expose] public section

/-!
What the computation of a role's program is built of, beside the monad's own operations.

A role's process, read as a computation (`Reading.read`), is composed of queries, of the monad's
bind, `for` and `if`, and of three things that are said here: a callee's computation with the
roles of its effects renamed (`renamed`); a computation without effects placed among a role's
effects (`liftEmpty`), of which the application of a row of the model and the reading of an
element of a sequence are a value or a stop (`optionE`); and the values of a list of results
taken one at a time (`headV`, `tailV`), with the state of a loop read the same way (`appendV`,
`splitV`, `pushV`, `collectedV`). Each comes with the law that the reading of the
corresponding piece of a process is that computation. Nothing here is of a judgment: these are
the pieces that every reading of a role's computation, by fees or otherwise, is about.
-/

namespace ZkcFormal.Form
open Zkc.Core ProbabilisticProcess Reading

variable {S : Sig} {H A B : Type}

/-! ## Values of a list of results -/

/-- The first value of a list. -/
def headV {T : Type} {F : T → Type} {a : T} {as : List T} : HList F (a :: as) → F a
  | .cons v _ => v

/-- The values of a list after the first. -/
def tailV {T : Type} {F : T → Type} {a : T} {as : List T} : HList F (a :: as) → HList F as
  | .cons _ vs => vs

@[simp] theorem headV_cons {T : Type} {F : T → Type} {a : T} {as : List T} (v : F a)
    (vs : HList F as) : headV (HList.cons v vs) = v := rfl

@[simp] theorem tailV_cons {T : Type} {F : T → Type} {a : T} {as : List T} (v : F a)
    (vs : HList F as) : tailV (HList.cons v vs) = vs := rfl

/-- An environment extended by a list of values, one name at a time: each name gets the value
at its place, so that a list of values that is one variable is read by its places. -/
def extend {I : Type} {F : I → Type} {Γ : Ctx I} (env : Env F Γ) :
    {ts : List I} → (ns : Names ts) → HList F ts → Env F (Γ.extend ns)
  | _, .nil, _ => env
  | _, .cons n ns, vs => extend (env.insert n (headV vs)) ns (tailV vs)

theorem extend_eq {I : Type} {F : I → Type} {Γ : Ctx I} (env : Env F Γ) {ts : List I}
    (ns : Names ts) (vs : HList F ts) : env.extend ns vs = extend env ns vs := by
  induction ns generalizing Γ with
  | nil => cases vs; rfl
  | cons n ns ih => cases vs with | cons x xs => exact ih (env.insert n x) xs

/-! ## The state of a loop, read by its places

A loop carries a list of values and collects a list of lists. Where such a list is one variable
(the result of the loop's body, the state of an iteration), the core's operations on it decide
by its constructors and are stuck. These read it by its places, so that on lists of types that
are written out they are the values themselves; each is the core's operation. -/

/-- The values of two lists, one after the other. -/
def appendV {T : Type} {F : T → Type} :
    {as bs : List T} → HList F as → HList F bs → HList F (as ++ bs)
  | [], _, _, ys => ys
  | _ :: _, _, xs, ys => .cons (headV xs) (appendV (tailV xs) ys)

theorem appendV_eq {T : Type} {F : T → Type} {as bs : List T} (xs : HList F as)
    (ys : HList F bs) : appendV xs ys = xs.append ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => exact congrArg (HList.cons x) ih

/-- The values of a list that is two lists, as the values of each. -/
def splitV {T : Type} {F : T → Type} :
    (as : List T) → {bs : List T} → HList F (as ++ bs) → HList F as × HList F bs
  | [], _, ys => (.nil, ys)
  | _ :: as, _, vs => (.cons (headV vs) (splitV as (tailV vs)).1, (splitV as (tailV vs)).2)

theorem splitV_eq {T : Type} {F : T → Type} : (as : List T) → {bs : List T} →
    (vs : HList F (as ++ bs)) → splitV as vs = HList.split as vs
  | [], _, _ => rfl
  | _ :: as, _, .cons x rest => by
    show (HList.cons x (splitV as rest).1, (splitV as rest).2) = _
    rw [splitV_eq as rest]
    rfl

/-- One more value of each type, before those collected. -/
def pushV {T : Type} {F : T → Type} :
    {items : List T} → HList (fun a => List (F a)) items → HList F items →
      HList (fun a => List (F a)) items
  | [], _, _ => .nil
  | _ :: _, lists, vs => .cons (headV vs :: headV lists) (pushV (tailV lists) (tailV vs))

theorem pushV_eq {T : Type} {F : T → Type} : {items : List T} →
    (lists : HList (fun a => List (F a)) items) → (vs : HList F items) →
    pushV lists vs = lists.push vs
  | [], .nil, .nil => rfl
  | _ :: _, .cons l lists, .cons v vs => by
    show HList.cons (v :: l) (pushV lists vs) = HList.cons (v :: l) (lists.push vs)
    rw [pushV_eq lists vs]

/-- What a loop collected, each list as one value. -/
def collectedV {D : Dialect} (s : Semantics D) (size : Option Nat) :
    {each : List D.Ty} → HList (fun a => List (s.Val a)) each →
      HList s.Val (each.map (D.collected size))
  | [], _ => .nil
  | a :: _, lists => .cons (s.collect size a (headV lists).reverse) (collectedV s size (tailV lists))

theorem collectedV_eq {D : Dialect} (s : Semantics D) (size : Option Nat) : {each : List D.Ty} →
    (lists : HList (fun a => List (s.Val a)) each) → collectedV s size lists = s.collected size lists
  | [], .nil => rfl
  | a :: _, .cons l lists => by
    show HList.cons (s.collect size a l.reverse) (collectedV s size lists) =
      HList.cons (s.collect size a l.reverse) (s.collected size lists)
    rw [collectedV_eq s size lists]

/-! ## A choice among the alternatives of a variant -/

/-- The payload of the one alternative of a variant with one. -/
def onlyPayload {I : Type} {F : I → Type} {a : I} : Pick F [a] → F a
  | .here v => v
  | .there q => nomatch q

/-- A choice between the first alternative and the others. -/
def splitPick {I : Type} {F : I → Type} {a : I} {as : List I} {C : Type}
    (p : Pick F (a :: as)) (first : F a → C) (other : Pick F as → C) : C :=
  match p with
  | .here v => first v
  | .there q => other q

/-- A choice among the alternatives: the last alternative is taken without a test. -/
def branch {I : Type} {F : I → Type} {a : I} {C : Type} :
    {ps : List I} → Pick F (a :: ps) → (F a → C) → (Pick F ps → C) → C
  | [], p, first, _ => first (onlyPayload p)
  | _ :: _, p, first, other => splitPick p first other

/-! ## A computation without effects, among effects -/

/-- A value or a stop: the application of a partial operation, with what is made of its
result. -/
def optionE (o : Option A) (f : A → B) : Comp S Stop B :=
  match o with
  | some a => pure (f a)
  | none => throw Stop.undefined

/-- A computation without effects, placed in a computation over a signature, with its stop
mapped. -/
def liftEmpty (S : Sig) (f : Stop → H) (p : Comp NoSig Stop A) : Comp S H A :=
  ExceptT.mk (simulateQ (fun op => nomatch op) (Except.mapError f <$> p.run))

/-- A local process lifted among effects reads as its reading lifted. -/
theorem read_liftLocal (f : Stop → H) (p : Local A) :
    read (liftLocal (S := S) f p) = liftEmpty S f (read p) := by
  cases p with
  | done a => rfl
  | halt h => rfl
  | call op => exact nomatch op

variable {V : Vocabulary} {M : Model V}

/-- The application of a row of the model reads as a value or a stop. -/
theorem read_row {fns : List (FnHeader V)} (table : FnTable M fns) (k : V.RowKey)
    (σ : RowSignature V.TypeKey V.RowKey) (h : V.row k = some σ) (args : HList M.Val σ.ins) :
    read (localOp M table (.row k σ h) args) = optionE (S := NoSig) (M.apply k σ h args) id := by
  change read (match M.apply k σ h args with
    | some v => Process.done v
    | none => Process.halt Stop.undefined) = _
  cases M.apply k σ h args <;> rfl

/-- The element of a sequence at a position reads as a value or a stop. -/
theorem read_seqAt {fns : List (FnHeader V)} (table : FnTable M fns) (item : V.Ty)
    (size : Option Nat) (h : _) (v : List (M.Val item)) (i : Nat) :
    read (localOp M table (.owned (.seqAt item size h)) (.cons v (.cons i .nil))) =
      optionE (S := NoSig) (v[i]?) (fun x => HList.cons x HList.nil) := by
  change read (match v[i]? with
    | some x => Process.done (HList.cons x HList.nil : HList M.Val [item])
    | none => Process.halt Stop.undefined) = _
  cases v[i]? <;> rfl

/-! ## A callee's computation at a call -/

/-- The renaming of a role's effects, as a map of the operations. -/
def renameLens (M : Model V) (ρ : Role → Role) :
    PFunctor.Lens (specOf (RSig M)).toPFunctor (specOf (RSig M)).toPFunctor :=
  ⟨renameOp ρ, fun op => carryReply ρ op id⟩

/-- A computation with the roles of its effects renamed: what a callee's computation is at a
call. -/
def renamed (ρ : Role → Role) (form : Comp (RSig M) Stop A) : Comp (RSig M) Stop A :=
  ExceptT.mk (PFunctor.FreeM.mapLens (renameLens M ρ) form.run)

/-- A process with its roles renamed reads as the reading renamed. -/
theorem read_mapR (ρ : Role → Role) (p : Program M A) :
    read (mapR M ρ p) = renamed ρ (read p) := by
  induction p with
  | done | halt => rfl
  | call op next ih =>
    cases op <;> apply ExceptT.ext <;>
      change OracleComp.queryBind _ _ = OracleComp.queryBind _ _ <;>
      congr 1 <;> funext reply <;> exact congrArg ExceptT.run (ih reply)

end ZkcFormal.Form
