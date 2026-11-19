module

public import Zkc.Core.Program.Erase
public import Zkc.Core.Meaning.Fold

@[expose] public section
namespace Zkc.Core.StraightLine
open Zkc.Core

/-- Pairs of simultaneously visible SSA names in two contexts. A new binding hides
prior pairs that refer to either overwritten name. -/
abbrev NamesMap := List (Name × Name)

def bindName (map : NamesMap) (a b : Name) : NamesMap :=
  (a,b) :: map.filter fun p => p.1 != a && p.2 != b

def bindNames {T : Type} (map : NamesMap) : {ts : List T} → Names ts → Names ts → NamesMap
  | _, .nil, .nil => map
  | _, .cons a left, .cons b right => bindNames (bindName map a b) left right

def Agrees {T : Type} {F : T → Type} {Γ Δ : Ctx T} (map : NamesMap) (left : Env F Γ) (right : Env F Δ) : Prop :=
  ∀ a b, (a,b) ∈ map → ∀ t ha hb, left a t ha = right b t hb

theorem Agrees.insert {T : Type} {F : T → Type} {Γ Δ : Ctx T} {left : Env F Γ} {right : Env F Δ}
    {map : NamesMap} (agree : Agrees map left right) (a b : Name) {t : T} (v : F t) :
    Agrees (bindName map a b) (left.insert a v) (right.insert b v) := by
  intro x y mem ty hx hy
  rcases List.mem_cons.mp mem with same | kept
  · obtain ⟨rfl,rfl⟩ := Prod.mk.inj same
    exact eq_of_heq ((Env.insert_at_bound left _ v rfl hx).trans (Env.insert_at_bound right _ v rfl hy).symm)
  · obtain ⟨mem,good⟩ := List.mem_filter.mp kept
    have different : x ≠ a ∧ y ≠ b := by simpa using good
    rw [Env.insert_at_other left _ v different.1,Env.insert_at_other right _ v different.2]
    apply agree _ _ mem

theorem Agrees.extend {T : Type} {F : T → Type} {Γ Δ : Ctx T} {left : Env F Γ} {right : Env F Δ}
    {map : NamesMap} (agree : Agrees map left right) :
    ∀ {ts : List T} (as bs : Names ts) (vs : HList F ts),
      Agrees (bindNames map as bs) (left.extend as vs) (right.extend bs vs)
  | _, .nil, .nil, .nil => agree
  | _, .cons a as, .cons b bs, .cons v vs => (agree.insert a b v).extend as bs vs

def arguments {T : Type} {Γ Δ : Ctx T} (map : NamesMap) :
    {xs : List T} → HList (Var Γ) xs → HList (Var Δ) xs → Bool
  | _, .nil, .nil => true
  | _, .cons a as, .cons b bs => decide ((a.name,b.name) ∈ map) && arguments map as bs

theorem Agrees.arguments {T : Type} {F : T → Type} {Γ Δ : Ctx T} {left : Env F Γ} {right : Env F Δ}
    {map : NamesMap} (agree : Agrees map left right) : ∀ {ts : List T} (as : HList (Var Γ) ts)
      (bs : HList (Var Δ) ts), arguments map as bs = true → left.all as = right.all bs
  | _, .nil, .nil, _ => rfl
  | _, .cons a as, .cons b bs, ok => by
    obtain ⟨head,tail⟩ := Bool.and_eq_true_iff.mp ok
    simp only [Env.all,Env.get,agree _ _ (of_decide_eq_true head) _ a.typed b.typed,agree.arguments as bs tail]

/-- Extending just the right environment shadows every correspondence to one of its new names. -/
def forgetRight {T : Type} (map : NamesMap) : {ts : List T} → Names ts → NamesMap
  | _, .nil => map
  | _, .cons b bs => forgetRight (map.filter fun p => p.2 != b) bs

theorem Agrees.extendRight {T : Type} {F : T → Type} {Γ Δ : Ctx T} {left : Env F Γ}
    {right : Env F Δ} {map : NamesMap} (agree : Agrees map left right) :
    ∀ {ts : List T} (ns : Names ts) (vs : HList F ts),
      Agrees (forgetRight map ns) left (right.extend ns vs)
  | _, .nil, .nil => agree
  | _, .cons b bs, .cons v vs => by
    have kept : Agrees (map.filter fun p => p.2 != b) left (right.insert b v) := by
      intro x y mem ty hx hy
      obtain ⟨old, different⟩ := List.mem_filter.mp mem
      rw [Env.insert_at_other right b v (show y ≠ b by simpa using different)]
      apply agree _ _ old
    exact kept.extendRight bs vs

variable {D : Dialect}
def Same {Γ Δ : Ctx D.Ty} {outs : List D.Ty} (map : NamesMap) (a : Term D Γ outs) (b : Term D Δ outs) : Prop :=
  ∀ (sem : Semantics D) path left right, Agrees map left right → a.denote sem path left = b.denote sem path right

/-- The same comparison restricted to a specified family of interpretations. -/
def SameIn (allowed : Semantics D → Prop) {Γ Δ : Ctx D.Ty} {outs : List D.Ty}
    (map : NamesMap) (a : Term D Γ outs) (b : Term D Δ outs) : Prop :=
  ∀ sem, allowed sem → ∀ path left right, Agrees map left right →
    a.denote sem path left = b.denote sem path right

variable {allowed : Semantics D → Prop}

theorem op_sameIn {Γ Δ : Ctx D.Ty} {ins mid outs : List D.Ty} {map : NamesMap}
    (key : Key) (op : D.Op ins mid) (as : HList (Var Γ) ins) (bs : HList (Var Δ) ins)
    (aa : Names mid) (bb : Names mid) (left : Term D (Γ.extend aa) outs) (right : Term D (Δ.extend bb) outs)
    (args : arguments map as bs = true) (rest : SameIn allowed (bindNames map aa bb) left right) :
    SameIn allowed map (.op key op as aa left) (.op key op bs bb right) := by
  intro sem okSem path env env' agree
  simp only [Term.denote_step,Instr.denote_op,agree.arguments as bs args]
  exact congrArg (Process.bind _) (funext fun vs => rest sem okSem path _ _ (agree.extend aa bb vs))

theorem guard_sameIn {Γ Δ : Ctx D.Ty} {t : D.Ty} {outs : List D.Ty} {map : NamesMap}
    (key : Key) (who : D.Who) (a : Var Γ t) (b : Var Δ t) (ok : D.Condition who t) (why : Reason)
    (left : Term D Γ outs) (right : Term D Δ outs) (args : (a.name,b.name) ∈ map) (rest : SameIn allowed map left right) :
    SameIn allowed map (.guard key who a ok why left) (.guard key who b ok why right) := by
  intro sem okSem path env env' agree
  simp only [Term.denote_guard,Env.get,agree _ _ args _ a.typed b.typed]
  rw [rest sem okSem path env env' agree]

/-- Evidence for passing an unmatched instruction. Its execution must return at every path and
environment in the specified semantics. The resulting values still extend the right environment. -/
def ReturnsDirectly (allowed : Semantics D → Prop) {Δ mid} (key : Key) (i : Instr D Δ mid) : Prop :=
  ∀ sem, allowed sem → ∀ path env, ∃ vs, i.denote sem key path env = .done vs

theorem skipRight {Γ Δ outs mid} {map : NamesMap} (a : Term D Γ outs) (key : Key)
    (i : Instr D Δ mid) (ns : Names mid) (b : Term D (Δ.extend ns) outs)
    (silent : ReturnsDirectly allowed key i) (rest : SameIn allowed (forgetRight map ns) a b) :
    SameIn allowed map a (.step key i ns b) := by
  intro sem ok path left right agree
  obtain ⟨vs, run⟩ := silent sem ok path right
  rw [Term.denote_step,run]
  exact rest sem ok path left _ (agree.extendRight ns vs)

/-- Compare in execution order. The caller may supply a checked interpretation of extra
instructions. All matched operations, guards, operands, keys and returns are checked. -/
def compareIn (checks : SkelRules D) (lawful : checks.Lawful) (allowed : Semantics D → Prop)
    (skip : ∀ {Δ mid} (key : Key) (i : Instr D Δ mid), Option (PLift (ReturnsDirectly allowed key i)))
    {Γ Δ : Ctx D.Ty} {outs : List D.Ty} (map : NamesMap) (a : Term D Γ outs) (b : Term D Δ outs) :
    Option (PLift (SameIn allowed map a b)) :=
  match b with
  | .ret bs => match a with
    | .ret as => if ok : arguments map as bs then
        some ⟨fun _ _ _ _ _ agree => congrArg Process.done (agree.arguments as bs ok)⟩
      else none
    | _ => none
  | .step key' i bb right =>
    let next {Γ' : Ctx D.Ty} (m : NamesMap) (l : Term D Γ' outs) :=
      compareIn checks lawful allowed skip m l right
    match skip key' i with
    | some ⟨silent⟩ => do
      let ⟨rest⟩ ← next (forgetRight map bb) a
      return ⟨skipRight a key' i bb right silent rest⟩
    | none => match a,i,bb,right,@next with
      | .op (ins := xs) key op as aa left,.op (ins := ys) op' bs,bb,right,recur => by
        letI := checks.sameTy
        exact if inputs : xs = ys then by
          subst ys
          exact if equalKeys : key = key' then by
            subst key'
            exact if ops : checks.sameOp op op' then by
              obtain ⟨rfl,same⟩ := lawful op op' ops
              cases eq_of_heq same
              exact if args : arguments map as bs then do
                let ⟨next⟩ ← recur (bindNames map aa bb) left
                return ⟨op_sameIn key op as bs aa bb left right args next⟩
              else none
            else none
          else none
        else none
      | .guard (t := t) key who x ok why left,.guard (t := u) who' y _ why',.nil,right,recur => by
        letI := checks.sameTy
        letI := checks.sameWho
        exact if same : t = u ∧ key = key' ∧ who = who' ∧ why = why' then by
          obtain ⟨rfl,rfl,rfl,rfl⟩ := same
          exact if arg : (x.name,y.name) ∈ map then do
            let ⟨next⟩ ← recur map left
            return ⟨guard_sameIn key who x y ok why left right arg next⟩
          else none
        else none
      | _,_,_,_,_ => none
termination_by structural b

theorem op_same {Γ Δ : Ctx D.Ty} {ins mid outs : List D.Ty} {map : NamesMap}
    (key : Key) (op : D.Op ins mid) (as : HList (Var Γ) ins) (bs : HList (Var Δ) ins)
    (aa : Names mid) (bb : Names mid) (left : Term D (Γ.extend aa) outs) (right : Term D (Δ.extend bb) outs)
    (args : arguments map as bs = true) (rest : Same (bindNames map aa bb) left right) :
    Same map (.op key op as aa left) (.op key op bs bb right) :=
  fun sem => op_sameIn (allowed := fun _ => True) key op as bs aa bb left right args
    (fun s _ => rest s) sem trivial

theorem guard_same {Γ Δ : Ctx D.Ty} {t : D.Ty} {outs : List D.Ty} {map : NamesMap}
    (key : Key) (who : D.Who) (a : Var Γ t) (b : Var Δ t) (ok : D.Condition who t) (why : Reason)
    (left : Term D Γ outs) (right : Term D Δ outs) (args : (a.name,b.name) ∈ map) (rest : Same map left right) :
    Same map (.guard key who a ok why left) (.guard key who b ok why right) :=
  fun sem => guard_sameIn (allowed := fun _ => True) key who a b ok why left right args
    (fun s _ => rest s) sem trivial

/-- Structural comparison, valid for every interpretation of the dialect. -/
def compare (checks : SkelRules D) (lawful : checks.Lawful) {Γ Δ : Ctx D.Ty} {outs : List D.Ty}
    (map : NamesMap) (a : Term D Γ outs) (b : Term D Δ outs) : Option (PLift (Same map a b)) := do
  let ⟨same⟩ ← compareIn checks lawful (fun _ => True) (fun _ _ => none) map a b
  return ⟨fun sem => same sem trivial⟩

#print axioms compare
end Zkc.Core.StraightLine
