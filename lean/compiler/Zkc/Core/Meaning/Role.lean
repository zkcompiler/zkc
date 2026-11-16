module

public import Zkc.Core.Meaning.Protocol

@[expose] public section

/-!
The meaning of a role program: the semantics of the role dialect.

A role program is typed in the protocol's contexts; a value of a located type is what the
role holds of it: the value when the role is a holder, nothing otherwise. A computation runs
the local operation on the values that the role holds. The role's part of an event names its
peers; the owner of an attempt marks its beginning and the end of its body, with effects.
An application runs the callee's program of the role that the role plays there, which
is the role `ρ.back r` of the callee: what the role holds of the arguments enters as what that
role holds of the ports, and what it holds of the results leaves as what the role holds of
them.
-/

namespace Zkc.Core

section
variable {V : Vocabulary} (M : Model V)

/-! ## What a role holds of a value -/

/-- The value that a holder has. -/
def reveal {r : Role} {a : LTy V} (h : r ∈ a.holders) (v : RV M r a) : M.Val a.ty :=
  cast (by simp [RV, h]) v

/-- What a role that does not hold a value has of it. -/
def nothing {r : Role} {a : LTy V} (h : r ∉ a.holders) : RV M r a := cast (by simp [RV, h]) ()

theorem reveal_hide {r : Role} {a : LTy V} (h : r ∈ a.holders) (v : LVal M a) :
    reveal M h (hide M r a v) = v := by
  simp [reveal, hide, h]

theorem hide_out {r : Role} {a : LTy V} (h : r ∉ a.holders) (v : LVal M a) :
    hide M r a v = nothing M h := by
  simp [hide, nothing, h]

/-- What a role that holds none of the values has of them. -/
def nothings {r : Role} : {items : List (LTy V)} → (∀ a, a ∈ items → r ∉ a.holders) →
    HList (RV M r) items
  | [], _ => .nil
  | a :: _, out =>
      .cons (nothing M (out a (by simp))) (nothings fun b hb => out b (by simp [hb]))

theorem hideAll_nothings {r : Role} :
    ∀ {items : List (LTy V)} (out : ∀ a, a ∈ items → r ∉ a.holders) (vs : HList (LVal M) items),
      hideAll M r vs = nothings M out
  | [], _, .nil => rfl
  | a :: _, out, .cons v rest => by
      show HList.cons (hide M r a v) (hideAll M r rest) = _
      rw [hide_out M (out a (by simp)) v, hideAll_nothings (fun b hb => out b (by simp [hb])) rest]
      rfl

/-- The values that a role holds, each by the proof that it holds it. -/
def revealAll {r : Role} : {items : List (LTy V)} → (∀ a, a ∈ items → r ∈ a.holders) →
    HList (RV M r) items → HList (LVal M) items
  | [], _, .nil => .nil
  | a :: _, here, .cons v rest =>
      .cons (reveal M (here a (by simp)) v) (revealAll (fun b hb => here b (by simp [hb])) rest)

theorem revealAll_hideAll {r : Role} :
    ∀ {items : List (LTy V)} (here : ∀ a, a ∈ items → r ∈ a.holders) (vs : HList (LVal M) items),
      revealAll M here (hideAll M r vs) = vs
  | [], _, .nil => rfl
  | a :: _, here, .cons v rest => by
      show HList.cons (V := LVal M) (reveal M _ (hide M r a v)) (revealAll M _ (hideAll M r rest)) = _
      rw [reveal_hide, revealAll_hideAll]

/-- What a role has of a value whose holders change, the role being a holder before exactly
when it is one after. -/
def carry {r : Role} {τ : V.Ty} {H H' : Holders} (same : r ∈ H ↔ r ∈ H')
    (v : RV M r ⟨τ, H⟩) : RV M r ⟨τ, H'⟩ :=
  cast (by simp [RV, same]) v

theorem carry_hide {r : Role} {τ : V.Ty} {H H' : Holders} (same : r ∈ H ↔ r ∈ H')
    (v : M.Val τ) : carry M same (hide M r ⟨τ, H⟩ v) = hide M r ⟨τ, H'⟩ v := by
  by_cases h : r ∈ H
  · have h' : r ∈ H' := same.mp h
    simp [carry, hide, h, h']
  · have h' : r ∉ H' := fun m => h (same.mpr m)
    simp [carry, hide, h, h']

/-- What a role has of a value used where a located type that it covers is asked. -/
def coverRV {r : Role} {a b : LTy V} (h : a.Covers b) (v : RV M r a) : RV M r b :=
  if hb : r ∈ b.holders then hide M r b (cover M h (reveal M (h.2 r hb) v)) else nothing M hb

theorem coverRV_hide {r : Role} {a b : LTy V} (h : a.Covers b) (v : LVal M a) :
    coverRV M h (hide M r a v) = hide M r b (cover M h v) := by
  unfold coverRV
  split
  · next hb => rw [reveal_hide]
  · next hb => rw [hide_out M hb]

/-- What a role has of the operands of an application, at its ports. -/
def fitAllRV {r : Role} : {as bs : List (LTy V)} → Fits as bs → HList (RV M r) as →
    HList (RV M r) bs
  | [], [], _, .nil => .nil
  | _ :: _, _ :: _, h, .cons v rest => .cons (coverRV M h.1 v) (fitAllRV h.2 rest)
  | [], _ :: _, h, _ => nomatch h
  | _ :: _, [], h, _ => nomatch h

theorem fitAllRV_hide {r : Role} :
    ∀ {as bs : List (LTy V)} (fits : Fits as bs) (vs : HList (LVal M) as),
      fitAllRV M fits (hideAll M r vs) = hideAll M r (fitAll M fits vs)
  | [], [], _, .nil => rfl
  | a :: _, b :: _, fits, .cons v rest => by
      show HList.cons (coverRV M fits.1 (hide M r a v)) (fitAllRV M fits.2 (hideAll M r rest)) =
        HList.cons (hide M r b (cover M fits.1 v)) (hideAll M r (fitAll M fits.2 rest))
      rw [coverRV_hide, fitAllRV_hide]
  | [], _ :: _, fits, _ => nomatch fits
  | _ :: _, [], fits, _ => nomatch fits

/-! ## What a role holds across a role map -/

theorem RoleMap.mem_map (ρ : RoleMap) {r : Role} {holders : Holders} :
    r ∈ Holders.map ρ.to holders ↔ ρ.back r ∈ holders := by
  rw [Holders.map, Holders.mem_ofList]
  constructor
  · intro m
    obtain ⟨i, hi, e⟩ := List.mem_map.mp m
    rw [← e, ρ.left]
    exact hi
  · intro m
    exact List.mem_map.mpr ⟨_, m, ρ.right r⟩

/-- What the caller's role has of an argument, as what the callee's role has of its port. -/
def enter (ρ : RoleMap) (r : Role) (a : LTy V) (v : RV M r (a.map ρ.to)) : RV M (ρ.back r) a :=
  if h : ρ.back r ∈ a.holders then
    hide M (ρ.back r) a (reveal M (a := a.map ρ.to) (ρ.mem_map.mpr h) v)
  else nothing M h

/-- What the callee's role has of a result, as what the caller's role has of it. -/
def leave (ρ : RoleMap) (r : Role) (a : LTy V) (v : RV M (ρ.back r) a) : RV M r (a.map ρ.to) :=
  if h : ρ.back r ∈ a.holders then hide M r (a.map ρ.to) (reveal M (a := a) h v)
  else nothing M (a := a.map ρ.to) fun m => h (ρ.mem_map.mp m)

theorem enter_hide (ρ : RoleMap) (r : Role) (a : LTy V) (v : LVal M a) :
    enter M ρ r a (hide M r (a.map ρ.to) v) = hide M (ρ.back r) a v := by
  unfold enter
  split
  · next h => rw [reveal_hide M (a := a.map ρ.to)]
  · next h => rw [hide_out M h]

theorem leave_hide (ρ : RoleMap) (r : Role) (a : LTy V) (v : LVal M a) :
    leave M ρ r a (hide M (ρ.back r) a v) = hide M r (a.map ρ.to) v := by
  unfold leave
  split
  · next h => rw [reveal_hide]
  · next h => rw [hide_out M (a := a.map ρ.to)]

def enterAll (ρ : RoleMap) (r : Role) : {items : List (LTy V)} →
    HList (RV M r) (items.map (LTy.map ρ.to)) → HList (RV M (ρ.back r)) items
  | [], .nil => .nil
  | a :: _, .cons v rest => .cons (enter M ρ r a v) (enterAll ρ r rest)

def leaveAll (ρ : RoleMap) (r : Role) : {items : List (LTy V)} →
    HList (RV M (ρ.back r)) items → HList (RV M r) (items.map (LTy.map ρ.to))
  | [], .nil => .nil
  | a :: _, .cons v rest => .cons (leave M ρ r a v) (leaveAll ρ r rest)

theorem enterAll_hide (ρ : RoleMap) (r : Role) :
    ∀ {items : List (LTy V)} (vs : HList (LVal M) (items.map (LTy.map ρ.to))),
      enterAll M ρ r (hideAll M r vs) = hideAll M (ρ.back r) (unmapAll M ρ.to vs)
  | [], .nil => rfl
  | a :: _, .cons v rest => by
      show HList.cons (enter M ρ r a (hide M r (a.map ρ.to) v)) (enterAll M ρ r (hideAll M r rest)) =
        HList.cons (hide M (ρ.back r) a v) (hideAll M (ρ.back r) (unmapAll M ρ.to rest))
      rw [enter_hide, enterAll_hide]

theorem leaveAll_hide (ρ : RoleMap) (r : Role) :
    ∀ {items : List (LTy V)} (vs : HList (LVal M) items),
      leaveAll M ρ r (hideAll M (ρ.back r) vs) = hideAll M r (remapAll M ρ.to vs)
  | [], .nil => rfl
  | a :: _, .cons v rest => by
      show HList.cons (leave M ρ r a (hide M (ρ.back r) a v))
          (leaveAll M ρ r (hideAll M (ρ.back r) rest)) =
        HList.cons (hide M r (a.map ρ.to) v) (hideAll M r (remapAll M ρ.to rest))
      rw [leave_hide, leaveAll_hide]

/-! ## A role map on a role's process -/

/-- The program of a callee's role as the caller's role performs it: every peer is renamed. -/
def mapR (ρ : Role → Role) {B : Type} : Program M B → Program M B
  | .done b => .done b
  | .halt why => .halt why
  | .call (.give kind getters at_ τ x) k =>
      .call (.give kind (getters.map ρ) at_ τ x) fun u => mapR ρ (k u)
  | .call (.get kind giver at_ τ) k => .call (.get kind (ρ giver) at_ τ) fun y => mapR ρ (k y)
  | .call (.own kind hearers at_ ins payload τ) k =>
      .call (.own kind (hearers.map ρ) at_ ins payload τ) fun y => mapR ρ (k y)
  | .call (.hear kind owner at_ τ) k => .call (.hear kind (ρ owner) at_ τ) fun y => mapR ρ (k y)
  | .call (.begin at_) k => .call (.begin at_) fun n => mapR ρ (k n)
  | .call (.settle at_) k => .call (.settle at_) fun u => mapR ρ (k u)

/-! ## The semantics -/

/-- The programs of the roles of the protocols that a region may apply. -/
abbrev RTable (protocols : List (ProtocolHeader V)) : Type :=
  ∀ hdr, Member protocols hdr → (j : Role) → List Frame → HList (RV M j) hdr.ins →
    Program M (HList (RV M j) hdr.outs)

/-- The meaning of an operation of a role program, at its key. -/
def roleOp {hs : Headers V} (r : Role) (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) (key : Key) :
    {ins res : List (LTy V)} → RoleOp V hs r ins res → List Frame → HList (RV M r) ins →
      Program M (HList (RV M r) res)
  | _, _, .compute R o _ types _ here, _, vs =>
      (liftLocal id (localOp M fnTable o (computeArgs M types (revealAll M here vs)))).map
        fun outs => hideAll M r (HList.located M R outs)
  | _, _, .absent _ out, _, _ => .done (nothings M out)
  | _, _, .give (τ := τ) (H := H) kind getters here, path, .cons v .nil =>
      .call (.give kind getters ⟨path, key⟩ τ (reveal M (a := ⟨τ, H⟩) here v)) fun _ =>
        .done (.cons (hide M r ⟨τ, Holders.ofList (getters ++ H)⟩
          (reveal M (a := ⟨τ, H⟩) here v)) .nil)
  | _, _, .get τ H kind giver getters _, path, _ =>
      .call (.get kind giver ⟨path, key⟩ τ) fun x =>
        .done (.cons (hide M r ⟨τ, Holders.ofList (getters ++ H)⟩ x) .nil)
  | _, _, .keep _ same, _, .cons v .nil => .done (.cons (carry M same v) .nil)
  | _, _, .own kind hearers operands τ _ here, path, vs =>
      .call (.own kind hearers ⟨path, key⟩ (operands.map LTy.ty)
          (HList.ofLocated M (revealAll M here vs)) τ) fun x =>
        .done (.cons (hide M r ⟨τ, Holders.ofList (r :: hearers)⟩ x) .nil)
  | _, _, .hear kind owner hearers τ _, path, _ =>
      .call (.hear kind owner ⟨path, key⟩ τ) fun x =>
        .done (.cons (hide M r ⟨τ, Holders.ofList (owner :: hearers)⟩ x) .nil)
  | _, _, .apply callee roles distinct _ _ fits, path, vs =>
      (mapR M (RoleMap.ofList roles distinct).to
        (rTable _ callee ((RoleMap.ofList roles distinct).back r) (path ++ [.application key])
          (enterAll M (RoleMap.ofList roles distinct) r (fitAllRV M fits vs)))).map
        (leaveAll M (RoleMap.ofList roles distinct) r)

/-- The alternative of a variant that the role holds, with what it holds of the payload. -/
def rolePick (r : Role) {ps : Holders} {t : LTy V} {payloads : List (LTy V)}
    (ok : ∃ key alternatives, t.ty = .variant key alternatives ∧
      payloads = alternatives.toList.map (fun τ => ⟨τ, ps⟩) ∧ r ∈ t.holders ∧ r ∈ ps)
    (v : RV M r t) : Pick (RV M r) payloads :=
  locatedPick M ps (W := RV M r) (fun τ u => hide M r ⟨τ, ps⟩ u)
    (by obtain ⟨key, alternatives, e, p, _⟩ := ok; exact ⟨key, alternatives, e, p⟩)
    (reveal M (by obtain ⟨_, _, _, _, h, _⟩ := ok; exact h) v)

/-- What a role holds of the sequence of the values that the iterations gave. -/
def collectRV (r : Role) (size : Option Nat) (a : LTy V) (vs : List (RV M r a)) :
    RV M r (LTy.collected size a) :=
  if h : r ∈ a.holders then hide M r (LTy.collected size a) (vs.map (reveal M h))
  else nothing M (a := LTy.collected size a) h

theorem collectRV_hide (r : Role) (size : Option Nat) (a : LTy V) (vs : List (LVal M a)) :
    collectRV M r size a (vs.map (hide M r a)) = hide M r (LTy.collected size a) vs := by
  unfold collectRV
  split
  · next h =>
      rw [List.map_map]
      have e : (reveal M h ∘ hide M r a) = fun v => v := by
        funext v
        exact reveal_hide M h v
      rw [e, List.map_id']
  · next h => rw [hide_out M (a := LTy.collected size a) h]

/-- The semantics of the role dialect of the role `r`. -/
@[reducible] def roleSem {hs : Headers V} (r : Role) (fnTable : FnTable M hs.fns)
    (rTable : RTable M hs.protocols) : Semantics (roleDialect V hs r) where
  Val := RV M r
  S := RSig M
  H := Stop
  op := fun {_ _} key o path vs => roleOp M r fnTable rTable key o path vs
  holds := fun {_ _} ok v => asBool M ok.1 (reveal M ok.2.1 v)
  stop := fun _ why at_ => .declared why at_
  pick := fun {_ _ _} ok v => rolePick M r ok v
  count := fun {_ _} ok v => asNat M ok.1 (reveal M ok.2.1 v)
  index := fun ps i => hide M r (LTy.index ps) i
  begin := fun w key path =>
    if r ∈ w then .call (.begin ⟨path, key⟩) fun n => .done (hide M r (LTy.index w) n)
    else .done (hide M r (LTy.index w) (0 : Nat))
  settle := fun w key path =>
    if r ∈ w then .call (.settle ⟨path, key⟩) fun _ => .done () else .done ()
  collect := fun size a vs => collectRV M r size a vs

/-! ## What a role holds of an environment -/

/-- What a role holds of the value of every name in scope. -/
def restrict (r : Role) {Γ : Ctx (LTy V)} (env : Env (LVal M) Γ) : Env (RV M r) Γ :=
  fun name a found => hide M r a (env name a found)

/-- Of no value, a role holds no value. -/
theorem restrict_empty (r : Role) :
    restrict M r (Env.empty : Env (LVal M) Ctx.empty) = Env.empty := by
  funext name a found
  exact nomatch (Ctx.find?_empty name).symm.trans found

/-- What a role holds of an environment with a name bound to a value is what it holds of the
environment with the name bound to what it holds of the value. -/
theorem restrict_insert (r : Role) {Γ : Ctx (LTy V)} (env : Env (LVal M) Γ) (bound : Name)
    {a : LTy V} (v : LVal M a) :
    restrict M r (env.insert bound v) = (restrict M r env).insert bound (hide M r a v) := by
  funext name b found
  by_cases same : name = bound
  · have typed : a = b := by
      rw [Ctx.find?_insert, ite_eq_left same] at found
      exact Option.some.inj found
    subst typed
    show hide M r a (env.insert bound v name a found) = _
    rw [eq_of_heq (Env.insert_at_bound env bound v same found),
      eq_of_heq (Env.insert_at_bound _ bound _ same found)]
  · show hide M r b (env.insert bound v name b found) = _
    rw [Env.insert_at_other env bound v same, Env.insert_at_other _ bound _ same]
    rfl

/-- The same for the names of a binding, in order, whatever the names: a name bound again is
bound again on both sides. -/
theorem restrict_extend (r : Role) :
    ∀ {Γ : Ctx (LTy V)} (env : Env (LVal M) Γ) {items : List (LTy V)} (bound : Names items)
      (vs : HList (LVal M) items),
      restrict M r (env.extend bound vs) = (restrict M r env).extend bound (hideAll M r vs)
  | _, _, [], .nil, .nil => rfl
  | _, env, _ :: _, .cons name rest, .cons v more => by
      show restrict M r ((env.insert name v).extend rest more) = _
      rw [restrict_extend r (env.insert name v) rest more, restrict_insert]
      rfl

theorem restrict_all (r : Role) {Γ : Ctx (LTy V)} (env : Env (LVal M) Γ) :
    ∀ {items : List (LTy V)} (xs : HList (Var Γ) items),
      (restrict M r env).all xs = hideAll M r (env.all xs)
  | [], .nil => rfl
  | _ :: _, .cons _ rest => by
      show HList.cons _ ((restrict M r env).all rest) = HList.cons _ (hideAll M r (env.all rest))
      rw [restrict_all r env rest]
      rfl

end

end Zkc.Core
