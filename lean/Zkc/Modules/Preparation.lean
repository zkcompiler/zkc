import Zkc.Modules.ImmutableCache

/-! Immutable preparation with explicit work, avoided work and storage prices.
The common cache laws justify returned values and cache validity. This module
accounts for costs separately from the client-visible result and emitted trace.
-/

set_option autoImplicit false
namespace Zkc.Modules.Preparation
variable {K V A E : Type} [DecidableEq K]
/-- Total immutable preparation interpretation, returning value and charged work. -/
abbrev Provider (K V : Type) := K → V × Nat
abbrev Cache (K V : Type) := ImmutableCache.Cache K (V × Nat)
abbrev Valid (p : Provider K V) (c : Cache K V) : Prop := ImmutableCache.Valid p c
inductive Mode where | direct | memo deriving DecidableEq, Repr
structure Acquired (K V : Type) where
  value : V
  cache : Cache K V
  work : Nat
  saved : Nat
  overhead : Nat
/-- Lookup and insertion prices belong to the implementation contract. They are
    charged separately; no claim of constant-time maps or total speedup. -/
structure Prices (K V : Type) where
  lookup : Cache K V → K → Nat
  insert : Cache K V → K → Nat

def acquire (p : Provider K V) (prices : Prices K V) (mode : Mode)
    (c : Cache K V) (k : K) : Acquired K V :=
  match mode with
  | .direct => let pv := p k; ⟨pv.1,c,pv.2,0,0⟩
  | .memo => match c k with
    | some v => ⟨v.1,c,0,v.2,prices.lookup c k⟩
    | none => let pv := p k; ⟨pv.1,ImmutableCache.insert c k pv,pv.2,0,prices.lookup c k + prices.insert c k⟩

theorem acquire_law (p : Provider K V) (pr : Prices K V) (m : Mode)
    (c : Cache K V) (k : K) (h : Valid p c) :
    (acquire p pr m c k).value = (p k).1 ∧
    Valid p (acquire p pr m c k).cache ∧
    (acquire p pr m c k).work + (acquire p pr m c k).saved = (p k).2 := by
  cases m with
  | direct => exact ⟨rfl,h,by simp [acquire]⟩
  | memo =>
    cases hk : c k with
    | none => simpa [acquire,hk] using And.intro (Eq.refl (p k).1) (And.intro (ImmutableCache.insert_valid p c h k) (Nat.add_zero (p k).2))
    | some v =>
      have hv := h k v hk
      simpa [acquire,hk,hv] using h

/-- Well-founded request/emit tree: continuation may adapt to preparation values and
    prior events, but cannot inspect handler work, hits, addresses or cache. -/
inductive Program (K V E A : Type) where
  | done : A → Program K V E A
  | emit : E → Program K V E A → Program K V E A
  | request : K → (V → Program K V E A) → Program K V E A

structure Result (K V E A : Type) where
  value : A
  trace : List E
  cache : Cache K V
  work : Nat
  saved : Nat
  overhead : Nat

def run (p : Provider K V) (pr : Prices K V) (mode : Mode) :
    Program K V E A → Cache K V → Result K V E A
  | .done a,c => ⟨a,[],c,0,0,0⟩
  | .emit e rest,c => let r := run p pr mode rest c; {r with trace := e :: r.trace}
  | .request k next,c =>
    let a := acquire p pr mode c k
    let r := run p pr mode (next a.value) a.cache
    {r with work := a.work + r.work, saved := a.saved + r.saved, overhead := a.overhead + r.overhead}

/-- Semantic reference executes every request, without any cache bookkeeping. -/
def denote (p : Provider K V) : Program K V E A → A × List E × Nat
  | .done a => (a,[],0)
  | .emit e rest => let r := denote p rest; (r.1,e :: r.2.1,r.2.2)
  | .request k next => let r := denote p (next (p k).1); (r.1,r.2.1,(p k).2 + r.2.2)

theorem simulation (p : Provider K V) (pr : Prices K V) (m : Mode)
    (prog : Program K V E A) (c : Cache K V) (h : Valid p c) :
    (run p pr m prog c).value = (denote p prog).1 ∧
    (run p pr m prog c).trace = (denote p prog).2.1 ∧
    Valid p (run p pr m prog c).cache ∧
    (run p pr m prog c).work + (run p pr m prog c).saved = (denote p prog).2.2 := by
  induction prog generalizing c with
  | done a => exact ⟨rfl,rfl,h,rfl⟩
  | emit e rest ih =>
    obtain ⟨hv,ht,hc,hw⟩ := ih c h
    exact ⟨hv,congrArg (List.cons e) ht,hc,hw⟩
  | request k next ih =>
    obtain ⟨ha,hc,hw⟩ := acquire_law p pr m c k h
    have hi := ih (acquire p pr m c k).value (acquire p pr m c k).cache hc
    simp only [run,denote]
    rw [ha] at hi ⊢
    refine ⟨hi.1,hi.2.1,hi.2.2.1,?_⟩
    have cost := hi.2.2.2
    omega

abbrev empty : Cache K V := ImmutableCache.empty

/-- Any observer factoring through return value and ordered emitted trace. -/
theorem observer (p : Provider K V) (pr : Prices K V)
    (prog : Program K V E A) {O : Type} (obs : A → List E → O) :
    obs (run p pr .direct prog empty).value (run p pr .direct prog empty).trace =
    obs (run p pr .memo prog empty).value (run p pr .memo prog empty).trace := by
  have hd := simulation p pr .direct prog empty (ImmutableCache.empty_valid p)
  have hm := simulation p pr .memo prog empty (ImmutableCache.empty_valid p)
  rw [hd.1,hd.2.1,hm.1,hm.2.1]

/-- Exact cost relation: memo total + avoided preparation = direct preparation
    + cache overhead. Preparation work alone is nonincreasing. -/
theorem work_bound (p : Provider K V) (pr : Prices K V) (prog : Program K V E A) :
    let r := run p pr .memo prog empty
    (r.work + r.overhead) + r.saved = (denote p prog).2.2 + r.overhead ∧
    r.work ≤ (denote p prog).2.2 := by
  have h := (simulation p pr .memo prog empty (ImmutableCache.empty_valid p)).2.2.2
  dsimp
  omega

def Program.bind {B : Type} : Program K V E A → (A → Program K V E B) → Program K V E B
  | .done a,f => f a
  | .emit e rest,f => .emit e (rest.bind f)
  | .request k next,f => .request k (fun v => (next v).bind f)

omit [DecidableEq K] in
theorem denote_bind_value {B : Type} (p : Provider K V) (prog : Program K V E A)
    (f : A → Program K V E B) :
    (denote p (prog.bind f)).1 = (denote p (f (denote p prog).1)).1 := by
  induction prog with
  | done a => rfl
  | emit e rest ih => exact ih
  | request k next ih => exact ih (p k).1

theorem direct_saved_zero (p : Provider K V) (pr : Prices K V)
    (prog : Program K V E A) (c : Cache K V) :
    (run p pr .direct prog c).saved = 0 := by
  induction prog generalizing c with
  | done a => rfl
  | emit e rest ih => exact ih c
  | request k next ih => simpa [run,acquire] using ih (p k).1 c

theorem direct_work (p : Provider K V) (pr : Prices K V) (prog : Program K V E A) :
    (run p pr .direct prog empty).work = (denote p prog).2.2 := by
  have h := (simulation p pr .direct prog empty (ImmutableCache.empty_valid p)).2.2.2
  simpa [direct_saved_zero] using h

theorem exact_cost_relation (p : Provider K V) (pr : Prices K V) (prog : Program K V E A) :
    (run p pr .memo prog empty).work + (run p pr .memo prog empty).saved =
      (run p pr .direct prog empty).work := by
  rw [direct_work]
  exact (simulation p pr .memo prog empty (ImmutableCache.empty_valid p)).2.2.2

theorem priced_improvement_iff (p : Provider K V) (pr : Prices K V) (prog : Program K V E A) :
    let m := run p pr .memo prog empty
    m.work + m.overhead ≤ (run p pr .direct prog empty).work ↔ m.overhead ≤ m.saved := by
  have h := exact_cost_relation p pr prog
  dsimp
  omega

omit [DecidableEq K] in
theorem denote_bind_trace {B : Type} (p : Provider K V) (prog : Program K V E A)
    (f : A → Program K V E B) :
    (denote p (prog.bind f)).2.1 =
      (denote p prog).2.1 ++ (denote p (f (denote p prog).1)).2.1 := by
  induction prog with
  | done a => rfl
  | emit e rest ih => simp [Program.bind, denote, ih]
  | request k next ih => exact ih (p k).1

def emitAll : List E → Program K V E A → Program K V E A
  | [], p => p
  | e :: es, p => .emit e (emitAll es p)

omit [DecidableEq K] in
theorem denote_emitAll_value (p : Provider K V) (es : List E)
    (prog : Program K V E A) :
    (denote p (emitAll es prog)).1 = (denote p prog).1 := by
  induction es with
  | nil => rfl
  | cons e es ih => exact ih

omit [DecidableEq K] in
theorem denote_emitAll_trace (p : Provider K V) (es : List E)
    (prog : Program K V E A) :
    (denote p (emitAll es prog)).2.1 = es ++ (denote p prog).2.1 := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [emitAll, denote, ih]

end Zkc.Modules.Preparation
