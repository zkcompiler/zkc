module

public import ZkcFormal.Interactive.SequenceMeaning

@[expose] public section
namespace ZkcFormal.Interactive.Sumcheck.ReductionRound.PointReturn
open Zkc.Core
variable {V : Vocabulary} {hs : Headers V} {t residual : V.Ty} {Γ : Ctx (LTy V)}

abbrev point (t : V.Ty) (k : Nat) : LTy V := shared (.seq t (some k))
abbrev ports (t residual : V.Ty) (k : Nat) : List (LTy V) := [point t k,shared t,⟨residual,[0]⟩]

def values (M : Model V) (t residual : V.Ty) (k : Nat) (xs : List (M.Val t)) (v : M.Val t) :
    HList (RV M 1) (ports t residual k) :=
  .cons (hide M 1 (point t k) xs) (.cons (hide M 1 (shared t) v) (.cons (nothing M (by simp)) .nil))

def boundVar {T : Type} (Γ : Ctx T) (n : Name) (ty : T) : Var (Γ.insert n ty) ty :=
  ⟨n,by simp [Ctx.find?_insert]⟩

def older {T : Type} {Γ : Ctx T} {a : T} (v : Var Γ a) (n : Name) (ty : T) (distinct : v.name ≠ n) :
    Var (Γ.insert n ty) a := ⟨v.name,by simpa [Ctx.find?_insert,distinct] using v.typed⟩

theorem bound_get {T : Type} {F : T → Type} {Γ : Ctx T} (env : Env F Γ) (n : Name) {a : T} (v : F a) :
    (env.insert n v).get (boundVar Γ n a) = v := eq_of_heq (Env.insert_at_bound _ _ _ rfl _)

theorem older_get {T : Type} {F : T → Type} {Γ : Ctx T} (env : Env F Γ) {a b : T} (v : Var Γ a) (n : Name)
    (w : F b) (distinct : v.name ≠ n) :
    (env.insert n w).get (older v n b distinct) = env.get v := Env.insert_at_other _ _ _ distinct _

def locations (xs : List (Var Γ (shared t))) : HList (Var Γ) (List.replicate xs.length (shared t)) :=
  match xs with
  | [] => .nil
  | v::rest => .cons v (locations rest)

theorem operandTypes (n : Nat) :
    (List.replicate n (shared t)).map LTy.ty = List.replicate n t := by simp

theorem held (n : Nat) : ∀ a, a ∈ List.replicate n (shared t) → 1 ∈ a.holders := by
  intro a mem
  obtain ⟨_,rfl⟩ := List.mem_replicate.mp mem
  simp

def assemble (t : V.Ty) (n : Nat) : RoleOp V hs 1 (List.replicate n (shared t)) [point t n] :=
  .compute [0,1] (.owned (.makeSeq t n)) _ (operandTypes n) (by simp) (held n)

private theorem compute_cons (M : Model V) {a : LTy V} {as : List (LTy V)} {ts : List V.Ty}
    (types : as.map LTy.ty = ts) (v : LVal M a) (vs : HList (LVal M) as) :
    computeArgs M (operands := a::as) (congrArg (List.cons a.ty) types) (.cons v vs) = .cons v (computeArgs M types vs) := by
  subst ts
  rfl

theorem items (M : Model V) (env : Env (RV M 1) Γ) (xs : List (Var Γ (shared t))) :
    HList.toItems M xs.length (computeArgs M (operandTypes _) (revealAll M (held _) (env.all (locations xs)))) =
      xs.map (Sequence.scalar M env) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    change HList.toItems M (xs.length+1) (computeArgs M _ (.cons _ _)) = _
    rw [compute_cons M (operandTypes xs.length)]
    exact congrArg (List.cons (Sequence.scalar M env a)) ih

theorem assembled (M : Model V) (fns : FnTable M hs.fns) (roles : RTable M hs.protocols) (path : List Frame)
    (key : Key) (env : Env (RV M 1) Γ) (xs : List (Var Γ (shared t))) :
    roleOp M 1 fns roles key (assemble t xs.length) path (env.all (locations xs)) =
      .done (.cons (hide M 1 (point t xs.length) (xs.map (Sequence.scalar M env))) .nil) := by
  change Process.done (A := HList (RV M 1) [point t xs.length]) (.cons (hide M 1 (point t xs.length) (HList.toItems M xs.length _)) .nil) = _
  rw [items]

def slot {a b : LTy V} (x : Var Γ a) (y : Var Γ b) : Name := max x.name y.name + 1

theorem beforeSlot {a b : LTy V} (x : Var Γ a) (y : Var Γ b) : x.name < slot x y ∧ y.name < slot x y := by
  exact ⟨Nat.lt_succ_of_le (Nat.le_max_left _ _),Nat.lt_succ_of_le (Nat.le_max_right _ _)⟩

def exports {n : Nat} (joined : Var Γ (point t n)) (running : Var Γ (shared t)) (keys : Nat → Key) :
    Term (roleDialect V hs 1) Γ (ports t residual n) :=
  let b : Nat := slot joined running
  let b1 : Nat := b+1
  let b2 : Nat := b+2
  let saved := older running b (point t n) (Nat.ne_of_lt (beforeSlot joined running).2)
  let p := boundVar Γ b (point t n)
  let v := boundVar (Γ.insert b (point t n)) b1 (shared t)
  let p' := older p b1 (shared t) (Nat.ne_of_lt (Nat.lt_succ_self b))
  let p'' := older p' b2 ⟨residual,[0]⟩ (Nat.ne_of_lt (Nat.lt_trans (Nat.lt_succ_self b) (Nat.lt_succ_self b1)))
  let v' := older v b2 ⟨residual,[0]⟩ (Nat.ne_of_lt (Nat.lt_succ_self b1))
  .op (keys 2) (.keep (τ := .seq t (some n)) (H := [0,1]) [0,1] Iff.rfl) (.cons joined .nil) (.cons b .nil) <|
  .op (keys 3) (.keep (τ := t) (H := [0,1]) [0,1] Iff.rfl) (.cons saved .nil) (.cons b1 .nil) <|
  .op (keys 4) (.absent [⟨residual,[0]⟩] (by simp)) .nil (.cons b2 .nil) <|
  .ret (.cons p'' (.cons v' (.cons (boundVar _ b2 _) .nil)))

theorem exported {n : Nat} (joined : Var Γ (point t n)) (running : Var Γ (shared t)) (keys : Nat → Key)
    (M : Model V) (fns : FnTable M hs.fns) (roles : RTable M hs.protocols) (path : List Frame) (env : Env (RV M 1) Γ) :
    (exports (residual := residual) joined running keys).denote (roleSem M 1 fns roles) path env =
      .done (values M t residual n (reveal M (a := point t n) (by simp) (env.get joined)) (Sequence.scalar M env running)) := by
  let b := slot joined running
  let e1 := env.insert b (env.get joined)
  let saved := older running b (point t n) (Nat.ne_of_lt (beforeSlot joined running).2)
  let e2 := e1.insert (b+1) (e1.get saved)
  let e3 := e2.insert (b+2) (nothing M (r := 1) (a := ⟨residual,[0]⟩) (by simp))
  let p := boundVar Γ b (point t n)
  let v := boundVar (Γ.insert b (point t n)) (b+1) (shared t)
  let p' := older p (b+1) (shared t) (Nat.ne_of_lt (Nat.lt_succ_self b))
  let p'' := older p' (b+2) ⟨residual,[0]⟩ (Nat.ne_of_lt (Nat.lt_trans (Nat.lt_succ_self b) (Nat.lt_succ_self (b+1))))
  let v' := older v (b+2) ⟨residual,[0]⟩ (Nat.ne_of_lt (Nat.lt_succ_self (b+1)))
  change Process.done (HList.cons (e3.get p'') (.cons (e3.get v') (.cons (e3.get (boundVar _ (b+2) _)) .nil))) = _
  simp only [e3,e2,e1,p'',p',p,v',v,saved,older_get,bound_get]
  rfl

def concatenate {k n : Nat} (initial : Var Γ (point t k)) (draws : Var Γ (point t n)) (running : Var Γ (shared t))
    (keys : Nat → Key) : Term (roleDialect V hs 1) Γ (ports t residual (k+n)) :=
  let b : Nat := slot initial running
  .op (keys 1) (.compute [0,1] (.owned (.seqConcat t (some k) (some n))) [point t k,point t n] rfl (by simp) (by
    intro a mem
    rcases List.mem_cons.mp mem with rfl | tail
    · simp
    · obtain rfl := List.mem_singleton.mp tail
      simp)) (.cons initial (.cons draws .nil)) (.cons b .nil) <|
  exports (boundVar _ b (point t (k+n))) (older running b _ (Nat.ne_of_lt (beforeSlot initial running).2)) keys

theorem concatenated {k n : Nat} (initial : Var Γ (point t k)) (draws : Var Γ (point t n)) (running : Var Γ (shared t))
    (keys : Nat → Key) (M : Model V) (fns : FnTable M hs.fns) (roles : RTable M hs.protocols)
    (path : List Frame) (env : Env (RV M 1) Γ) :
    (concatenate (residual := residual) initial draws running keys).denote (roleSem M 1 fns roles) path env =
    .done (values M t residual (k+n) (reveal M (a := point t k) (by simp) (env.get initial) ++
      reveal M (a := point t n) (by simp) (env.get draws)) (Sequence.scalar M env running)) := by
  let xs := reveal M (a := point t k) (by simp) (env.get initial) ++ reveal M (a := point t n) (by simp) (env.get draws)
  let b := slot initial running
  let e := env.insert b (hide M 1 (point t (k+n)) xs)
  let p := boundVar Γ b (point t (k+n))
  let v := older running b (point t (k+n)) (Nat.ne_of_lt (beforeSlot initial running).2)
  refine (exported (residual := residual) p v keys M fns roles path e).trans ?_
  simp only [e,p,v,bound_get,reveal_hide,Sequence.scalar,older_get]
  rfl

def body {k : Nat} (initial : Var Γ (point t k)) (running : Var Γ (shared t)) (xs : List (Var Γ (shared t)))
    (keys : Nat → Key) : Term (roleDialect V hs 1) Γ (ports t residual (k+xs.length)) :=
  let b : Nat := slot initial running
  .op (keys 0) (assemble t xs.length) (locations xs) (.cons b .nil) <|
  concatenate (older initial b _ (Nat.ne_of_lt (beforeSlot initial running).1)) (boundVar _ b _)
    (older running b _ (Nat.ne_of_lt (beforeSlot initial running).2)) keys

theorem result {k : Nat} (initial : Var Γ (point t k)) (running : Var Γ (shared t)) (xs : List (Var Γ (shared t)))
    (keys : Nat → Key) (M : Model V) (fns : FnTable M hs.fns) (roles : RTable M hs.protocols)
    (path : List Frame) (env : Env (RV M 1) Γ) :
    (body (residual := residual) initial running xs keys).denote (roleSem M 1 fns roles) path env =
    .done (values M t residual (k+xs.length)
      (reveal M (a := point t k) (by simp) (env.get initial) ++ xs.map (Sequence.scalar M env)) (Sequence.scalar M env running)) := by
  simp only [body,Term.denote_step,Instr.denote_op]
  change (roleOp M 1 fns roles _ (assemble t xs.length) path (env.all (locations xs))).bind _ = _
  rw [assembled]
  let b := slot initial running
  let ty := point t xs.length
  let e := env.insert b (hide M 1 ty (xs.map (Sequence.scalar M env)))
  let p := older initial b ty (Nat.ne_of_lt (beforeSlot initial running).1)
  let v := older running b ty (Nat.ne_of_lt (beforeSlot initial running).2)
  refine (concatenated (residual := residual) p (boundVar Γ b ty) v keys M fns roles path e).trans ?_
  simp only [e,p,v,older_get,Sequence.scalar]
  rw [bound_get env b (hide M 1 ty (xs.map (Sequence.scalar M env)))]
  rfl

#print axioms result
end ZkcFormal.Interactive.Sumcheck.ReductionRound.PointReturn
