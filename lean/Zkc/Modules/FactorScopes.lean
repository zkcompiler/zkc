import Zkc.Modules.Allocation

set_option autoImplicit false

namespace Zkc.Modules.FactorScopes
open Zkc.Modules.Factor Zkc.Modules.FactorState Zkc.Modules.FactorBinding Zkc.Modules.Installation Zkc.Modules.Allocation
variable {K : Type}

/-- Lexical indices are not runtime identities. No default name is invented. -/
abbrev Names := Nat → Option Namespace
abbrev Facts := Nat → Option Fact
def emptyNames : Names := fun _ => none
def emptyFacts : Facts := fun _ => none
def push (n : Namespace) (ns : Names) : Names
  | 0 => some n
  | i+1 => ns i

/-- This first pass conservatively kills older facts on allocation. In particular,
    it requires no false global-freshness premise for an imported namespace. -/
def entered (f : Fact) : Facts
  | 0 => some f
  | _+1 => none
def Sound (fs : Facts) (ns : Names) (s : World K) : Prop :=
  ∀ i f n, fs i = some f → ns i = some n → Means s.values (fact n f)

theorem empty_sound (ns : Names) (s : World K) : Sound emptyFacts ns s := by
  intro i f n hf _
  simp [emptyFacts] at hf

def localState (n : Namespace) (s : State K) : State K :=
  ⟨fun k => s.base (key n k),fun h => s.view (addr n h),fun i => s.challenge (addr n i)⟩
def relocate (n : Namespace) : Plan → Plan
  | .direct => .direct
  | .reuse f tail => .reuse (fact n f) (tail.map (addr n))

theorem local_means (n : Namespace) (s : State K) (f : Fact)
    (h : Means s (fact n f)) : Means (localState n s) f := by
  intro tail ht
  simpa [Means,localState,fact,List.map_map,Function.comp_def] using h tail ht

theorem relocated_query (n : Namespace) (s : State K) (q : Query) :
    runQuery s (query n q) = runQuery (localState n s) q := by
  simp [runQuery,query,localState,List.map_map,Function.comp_def]

theorem relocated_plan (n : Namespace) (s : State K) (q : Query) (p : Plan) :
    runPlan s (query n q) (relocate n p) = runPlan (localState n s) q p := by
  cases p <;> simp [runPlan,relocate,fact,localState,List.map_map,Function.comp_def,relocated_query]

theorem entered_sound (quota cap : Nat) (p : Pool) (r : Request K) (s : World K)
    (ns : Names) (n : Namespace) (h : (allocate quota cap p r s).allocated = some n) :
    Sound (entered (Zkc.Source.FactorInputs.fact r.source r.handle)) (push n ns)
      (allocate quota cap p r s).returned.world := by
  obtain ⟨rfl,hw,hg⟩ := allocated_some quota cap p r s n h
  intro i f m hf hm
  cases i with
  | zero =>
    simp only [entered,Option.some.injEq] at hf
    simp only [push,Option.some.injEq] at hm
    subst f; subst m
    rw [hw]
    exact patch_means (renamed p r) s hg
  | succ i => simp [entered] at hf

inductive Source (K : Type) where
  | stop
  | demand (slot : Nat) (q : Query) (next : Source K)
  | bind (request : Request K) (success failure : Source K)
  | clobber (slot handle : Nat) (value : List K → K) (next : Source K)

inductive Code (K : Type) where
  | stop
  | demand (slot : Nat) (q : Query) (plan : Plan) (next : Code K)
  | bind (request : Request K) (success failure : Code K)
  | clobber (slot handle : Nat) (value : List K → K) (next : Code K)

def direct : Source K → Code K
  | .stop => .stop
  | .demand i q next => .demand i q .direct (direct next)
  | .bind r yes no => .bind r (direct yes) (direct no)
  | .clobber i h v next => .clobber i h v (direct next)

inductive Notice where
  | allocation (event : Event)
  | missing (slot : Nat)
  | unavailable (namespaceId : Namespace) (q : Query)
  | changed (namespaceId : Namespace) (handle : Nat)
  deriving DecidableEq, Repr

structure Result (K : Type) where
  pool : Pool
  world : World K
  values : List K
  events : List Notice

def run (quota cap : Nat) : Code K → Names → Pool → World K → Result K
  | .stop, _, p, s => ⟨p,s,[],[]⟩
  | .demand i q plan next, ns, p, s =>
    match ns i with
    | none => ⟨p,s,[],[.missing i]⟩
    | some n =>
      if checkReady s.known (query n q) then
        let out := run quota cap next ns p s
        {out with values := runPlan s.values (query n q) (relocate n plan) :: out.values}
      else ⟨p,s,[],[.unavailable n q]⟩
  | .bind r yes no, ns, p, s =>
    let out := allocate quota cap p r s
    let rest := match out.allocated with
      | none => run quota cap no ns out.pool out.returned.world
      | some n => run quota cap yes (push n ns) out.pool out.returned.world
    {rest with events := out.returned.events.map Notice.allocation ++ rest.events}
  | .clobber i h v next, ns, p, s =>
    match ns i with
    | none => ⟨p,s,[],[.missing i]⟩
    | some n =>
      let out := run quota cap next ns p {s with values := overwrite s.values (addr n h) v}
      {out with events := .changed n h :: out.events}

end Zkc.Modules.FactorScopes
