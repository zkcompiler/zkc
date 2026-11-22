module

public import ZkcFormal.WorldObservation
public import Zkc.Core.Meaning.Program

@[expose] public section
set_option autoImplicit false

namespace ZkcFormal
open Zkc.Core

/-- An operation match includes the relation on its dependent reply types. This lets one
constructor identify the request, its operands and the representation of its answer. -/
abbrev EffectRelation (S T : Sig) :=
  (o : S.Op) → (t : T.Op) → (S.Reply o → T.Reply t → Prop) → Prop

/-- Every allowed concrete step has an allowed abstract representative. Stops preserve their
entire payload. The relation on returns belongs to the caller. -/
inductive SupportSimulation {S T : Sig} (effects : EffectRelation S T)
    (abstractAllows : ∀ op, S.Reply op → Prop) (concreteAllows : ∀ op, T.Reply op → Prop)
    {H A B : Type} (result : A → B → Prop) : Process S H A → Process T H B → Prop where
  | done {a b} : result a b → SupportSimulation effects abstractAllows concreteAllows result (.done a) (.done b)
  | halt (reason : H) : SupportSimulation effects abstractAllows concreteAllows result (.halt reason) (.halt reason)
  | call {o t k l} {answers : S.Reply o → T.Reply t → Prop} : effects o t answers →
      (∀ y, concreteAllows t y → ∃ x, abstractAllows o x ∧ answers x y) →
      (∀ x y, abstractAllows o x → concreteAllows t y → answers x y →
        SupportSimulation effects abstractAllows concreteAllows result (k x) (l y)) →
      SupportSimulation effects abstractAllows concreteAllows result (.call o k) (.call t l)

namespace SupportSimulation
variable {S T : Sig} {H A B C D : Type} {effects : EffectRelation S T}
  {abstractAllows : ∀ op, S.Reply op → Prop} {concreteAllows : ∀ op, T.Reply op → Prop}
  {result : A → B → Prop} {p : Process S H A} {q : Process T H B}

/-- Transfer an every-path property using coverage at each reached operation. -/
theorem every (sim : SupportSimulation effects abstractAllows concreteAllows result p q)
    {first : A → Prop} {second : B → Prop} {stop : H → Prop}
    (transfer : ∀ a b, result a b → first a → second b) (all : p.Every abstractAllows first stop) :
    q.Every concreteAllows second stop := by
  induction sim with
  | done holds => exact transfer _ _ holds all
  | halt => exact all
  | call _ covers _ ih =>
    intro y hy
    obtain ⟨x, hx, hxy⟩ := covers y hy
    exact ih x y hx hy hxy (all x hx)

/-- A concrete return has an abstract run with a related return value. A model with fewer
concrete outcomes may still simulate, so the direction of this witness matters. -/
theorem canReturn (sim : SupportSimulation effects abstractAllows concreteAllows result p q)
    {b : B} (run : q.CanReturn concreteAllows b) : ∃ a, p.CanReturn abstractAllows a ∧ result a b := by
  induction sim with
  | done h => cases run; exact ⟨_, .done _, h⟩
  | halt => cases run
  | call _ covers _ ih =>
    cases run with
    | call _ y hy rest =>
      obtain ⟨x, hx, hxy⟩ := covers y hy
      obtain ⟨a, ran, hab⟩ := ih x y hx hy hxy rest
      exact ⟨a, .call _ x hx ran, hab⟩

/-- A caller can change the representation of intermediate values at a bind boundary. -/
theorem bind (sim : SupportSimulation effects abstractAllows concreteAllows result p q)
    {post : C → D → Prop} {next : A → Process S H C} {next' : B → Process T H D}
    (after : ∀ a b, result a b →
      SupportSimulation effects abstractAllows concreteAllows post (next a) (next' b)) :
    SupportSimulation effects abstractAllows concreteAllows post (p.bind next) (q.bind next') := by
  induction sim with
  | done holds => exact after _ _ holds
  | halt reason => exact .halt reason
  | call ops covers _ ih => exact .call ops covers ih

end SupportSimulation

namespace ModelComparison
variable {V : Vocabulary} {M N : Model V}

/-- A representation relation for the types of the shared vocabulary. -/
abbrev Values (M N : Model V) := ∀ t, M.Val t → N.Val t → Prop

/-- Lift an indexed representation relation to ordered request, input or output values. -/
inductive Arguments {I : Type} {F G : I → Type} (r : ∀ i, F i → G i → Prop) :
    {types : List I} → HList F types → HList G types → Prop where
  | nil : Arguments r .nil .nil
  | cons {t ts x y} {xs : HList F ts} {ys : HList G ts} :
      r t x y → Arguments r xs ys → Arguments r (.cons x xs) (.cons y ys)

/-- Joint operations agree on every source address, participant, operation kind and type.
The represented values may differ. -/
inductive JointOperations (r : Values M N) : EffectRelation (GSig M) (GSig N) where
  | flow {k who peers at_ t x y} : r t x y →
      JointOperations r (.flow k who peers at_ t x) (.flow k who peers at_ t y) Eq
  | given {k who peers at_ ins t xs ys} : Arguments r xs ys →
      JointOperations r (.given k who peers at_ ins xs t) (.given k who peers at_ ins ys t) (r t)

/-- A role sees the original request payload only when it owns the request. Attempt numbers
and acknowledgments have the representations fixed by Core. -/
inductive RoleOperations (r : Values M N) : EffectRelation (RSig M) (RSig N) where
  | give {k peers at_ t x y} : r t x y →
      RoleOperations r (.give k peers at_ t x) (.give k peers at_ t y) Eq
  | get {k who at_ t} :
      RoleOperations r (.get k who at_ t) (.get k who at_ t) (r t)
  | own {k peers at_ ins t xs ys} : Arguments r xs ys →
      RoleOperations r (.own k peers at_ ins xs t) (.own k peers at_ ins ys t) (r t)
  | hear {k who at_ t} :
      RoleOperations r (.hear k who at_ t) (.hear k who at_ t) (r t)
  | begin {at_} : RoleOperations r (.begin at_) (.begin at_) Eq
  | settle {at_} : RoleOperations r (.settle at_) (.settle at_) Eq

/-- Match both the operation and its actual reply at one observed trace entry. -/
def entries {S T : Sig} (ops : EffectRelation S T)
    (x : (o : S.Op) × S.Reply o) (y : (t : T.Op) × T.Reply t) : Prop :=
  ∃ answers, ops x.1 y.1 answers ∧ answers x.2 y.2

/-- Projecting related joint observations preserves the exact view of any named role. The
owner sees the request operands, a listener sees only the answer and bystanders see no entry. -/
theorem roleEntry_related {r : Values M N} (who : Role) {a b}
    (same : entries (JointOperations r) a b) :
    Option.Rel (entries (RoleOperations r)) (World.roleEntry who a) (World.roleEntry who b) := by
  obtain ⟨o, x⟩ := a
  obtain ⟨t, y⟩ := b
  obtain ⟨answers, ops, replies⟩ := same
  cases ops with
  | flow value =>
    simp only [World.roleEntry]
    split
    · exact .some ⟨_, .give value, rfl⟩
    · split
      · exact .some ⟨_, .get, value⟩
      · exact .none
  | given payload =>
    simp only [World.roleEntry]
    split
    · exact .some ⟨_, .own payload, replies⟩
    · split
      · exact .some ⟨_, .hear, replies⟩
      · exact .none

/-- Joint support uses Core's validity and sampling-law support at the original payload. -/
def permitted (M : Model V) : (op : GOp M) → (GSig M).Reply op → Prop
  | .flow .., _ => True
  | .given k _ _ _ ins xs t, x => Allows M k ins xs t x

/-- Simulation between joint meanings of protocols in two models of one vocabulary. -/
abbrev ProtocolSimulation (r : Values M N) {A B : Type} (result : A → B → Prop)
    (p : Protocol M A) (q : Protocol N B) :=
  SupportSimulation (JointOperations r) (permitted M) (permitted N) result p q

/-- Simulation between projected (or otherwise authored) role processes. Each side uses its
own permitted replies. A caller comparing two projections fixes their roles at the roots. -/
abbrev RoleSimulation (r : Values M N) {A B : Type} (result : A → B → Prop)
    (p : Program M A) (q : Program N B) :=
  SupportSimulation (RoleOperations r) (Permitted M) (Permitted N) result p q

/-- Located values correspond at precisely the ports the role can read. -/
def held (r : Values M N) (role : Role) (t : LTy V) (a : RV M role t) (b : RV N role t) : Prop :=
  ∀ seen : role ∈ t.holders, r t.ty (reveal M seen a) (reveal N seen b)

/-- Compare the two meanings of the same installed protocol member, at the same in-roster
role and occurrence path, for all related valid inputs. A client establishes this property
for its program and representation before transferring safety or returning witnesses.
Deriving this correspondence from compatibility laws for the accessed vocabulary rows
requires a separate program-induction theorem. -/
def atRole (r : Values M N) (p : Typed V) {hdr : ProtocolHeader V}
    (root : Member p.headers.protocols hdr) (role : Fin hdr.roles) (path : List Frame) : Prop :=
  ∀ (a : HList (RV M role.val) hdr.ins) (b : HList (RV N role.val) hdr.ins),
    a.All (RV.Valid M role.val) → b.All (RV.Valid N role.val) → Arguments (held r role.val) a b →
    RoleSimulation r (Arguments (held r role.val))
      (roleMeaning M p root role.val path a) (roleMeaning N p root role.val path b)

end ModelComparison
end ZkcFormal
