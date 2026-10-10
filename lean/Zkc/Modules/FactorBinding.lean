import Zkc.Modules.FactorContract
import Zkc.Source.FactorInputs
import Mathlib.Data.Nat.Pairing

set_option autoImplicit false

namespace Zkc.Modules.FactorBinding
open Zkc.Modules.Factor Zkc.Modules.FactorState
variable {K E : Type}

/-- Runtime identities are structural naturals, never field elements. The local
    source key remains distinct from this instance/incarnation namespace. -/
structure Namespace where
  instanceId : Nat
  incarnation : Nat
  deriving DecidableEq, Repr

def Namespace.tag (n : Namespace) := Nat.pair n.instanceId n.incarnation
def addr (n : Namespace) (localId : Nat) := Nat.pair n.tag localId
def key (n : Namespace) (k : Key) : Key := ⟨addr n k.origin,k.axes⟩
def fact (n : Namespace) (f : Fact) : Fact :=
  ⟨key n f.key,addr n f.handle,f.applied.map (addr n),f.remaining⟩
def query (n : Namespace) (q : Query) : Query := ⟨key n q.key,q.point.map (addr n)⟩

theorem tag_injective : Function.Injective Namespace.tag := by
  intro n m h
  cases n; cases m
  simp only [Namespace.tag,Nat.pair_eq_pair] at h
  cases h.1; cases h.2; rfl

theorem addr_eq (n m : Namespace) (i j : Nat) :
    addr n i = addr m j ↔ n = m ∧ i = j := by
  simp only [addr,Nat.pair_eq_pair]
  exact and_congr tag_injective.eq_iff Iff.rfl

theorem instances_disjoint (n m : Namespace) (different : n ≠ m) (i j : Nat) :
    addr n i ≠ addr m j := fun h => different ((addr_eq n m i j).mp h).1

def source (n : Namespace) : Zkc.Source.FactorInputs.Source → Zkc.Source.FactorInputs.Source
  | .base k => .base (key n k)
  | .fix e i => .fix (source n e) (addr n i)

theorem source_key (n : Namespace) (e : Zkc.Source.FactorInputs.Source) :
    (source n e).key = key n e.key := by
  induction e <;> simp_all [source,Zkc.Source.FactorInputs.Source.key]

theorem source_prefix (n : Namespace) (e : Zkc.Source.FactorInputs.Source) :
    (source n e).prefix = e.prefix.map (addr n) := by
  induction e <;> simp_all [source,Zkc.Source.FactorInputs.Source.prefix]

/-- This relation names exactly what a namespace interpretation must establish.
    The concrete link operation below establishes it, including actual values. -/
structure Interprets (n : Namespace) (localState globalState : State K) : Prop where
  base : ∀ k, globalState.base (key n k) = localState.base k
  view : ∀ h, globalState.view (addr n h) = localState.view h
  challenge : ∀ i, globalState.challenge (addr n i) = localState.challenge i

/-- Replace one complete semantic namespace with an immutable local snapshot.
    This is a pure map model, not a claim about native heap disjointness. -/
def linkValues (n : Namespace) (localState outer : State K) : State K where
  base := fun k => if (Nat.unpair k.origin).1 = n.tag then
    localState.base ⟨(Nat.unpair k.origin).2,k.axes⟩ else outer.base k
  view := fun h => if (Nat.unpair h).1 = n.tag then
    localState.view (Nat.unpair h).2 else outer.view h
  challenge := fun i => if (Nat.unpair i).1 = n.tag then
    localState.challenge (Nat.unpair i).2 else outer.challenge i

def link (n : Namespace) (localWorld outer : World K) : World K where
  values := linkValues n localWorld.values outer.values
  known := localWorld.known.map (addr n) ++
    outer.known.filter (fun i => decide ((Nat.unpair i).1 ≠ n.tag))

theorem link_interprets (n : Namespace) (l outer : World K) :
    Interprets n l.values (link n l outer).values := by
  constructor <;> intro x <;> simp [link,linkValues,key,addr]

theorem link_known (n : Namespace) (l outer : World K) :
    Known (link n l outer) (l.known.map (addr n)) := by
  intro i hi
  exact List.mem_append_left _ hi

theorem other_interpretation (n m : Namespace) (different : n ≠ m)
    (l outer old : World K) (before : Interprets m old.values outer.values) :
    Interprets m old.values (link n l outer).values := by
  have tags : m.tag ≠ n.tag := fun h => different (tag_injective h).symm
  constructor
  · intro k; simpa [link,linkValues,key,addr,tags] using before.base k
  · intro h; simpa [link,linkValues,addr,tags] using before.view h
  · intro i; simpa [link,linkValues,addr,tags] using before.challenge i

theorem other_known (n m : Namespace) (different : n ≠ m)
    (l outer : World K) (available : List Nat)
    (before : Known outer (available.map (addr m))) :
    Known (link n l outer) (available.map (addr m)) := by
  intro i hi
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi
  have tags : m.tag ≠ n.tag := fun h => different (tag_injective h).symm
  apply List.mem_append_right
  apply List.mem_filter.mpr
  exact ⟨before _ (List.mem_map.mpr ⟨j,hj,rfl⟩),by simp [addr,tags]⟩

theorem source_eval (n : Namespace) (l g : State K) (rel : Interprets n l g)
    (e : Zkc.Source.FactorInputs.Source) (tail : List K) :
    (source n e).eval g tail = e.eval l tail := by
  induction e generalizing tail with
  | base k => exact congrFun (rel.base k) tail
  | fix e i ih =>
    simpa [source,Zkc.Source.FactorInputs.Source.eval,rel.challenge] using (ih (l.challenge i :: tail))

theorem means_transport (n : Namespace) (l g : State K) (rel : Interprets n l g)
    (f : Fact) (valid : Means l f) : Means g (fact n f) := by
  intro tail ht
  have mapped : (f.applied.map (addr n)).map g.challenge = f.applied.map l.challenge := by
    simp only [List.map_map]
    apply List.map_congr_left
    intro i _; exact rel.challenge i
  simpa only [fact,rel.view,rel.base,mapped] using valid tail ht

theorem query_transport (n : Namespace) (l g : State K) (rel : Interprets n l g)
    (q : Query) : runQuery g (query n q) = runQuery l q := by
  have mapped : (q.point.map (addr n)).map g.challenge = q.point.map l.challenge := by
    simp only [List.map_map]
    apply List.map_congr_left
    intro i _; exact rel.challenge i
  simp [runQuery,query,rel.base,mapped]

theorem source_admitted (n : Namespace) (available : List Nat)
    (e : Zkc.Source.FactorInputs.Source) (good : Zkc.Source.FactorInputs.check available e = true) :
    Zkc.Source.FactorInputs.check (available.map (addr n)) (source n e) = true := by
  apply decide_eq_true
  have hg : Zkc.Source.FactorInputs.Good available e := of_decide_eq_true good
  constructor
  · simpa [source_prefix,source_key,key] using hg.1
  · intro i hi
    rw [source_prefix] at hi
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi
    exact List.mem_map.mpr ⟨j,hg.2 j hj,rfl⟩

/-- A concrete local input binding: captured values supply exactly range(length)
    as available slots. Later invocation cannot reinterpret this stored list. -/
def snapshot (base : Key → List K → K) (fallback : K) (captured : List K) : World K where
  values := ⟨base,fun _ _ => fallback,fun i => captured[i]?.getD fallback⟩
  known := List.range captured.length

theorem captured_slot (base : Key → List K → K) (fallback : K)
    (captured : List K) (i : Nat) (h : i < captured.length) :
    (snapshot base fallback captured).values.challenge i = captured[i] := by
  simp [snapshot,List.getElem?_eq_getElem h]

structure Prepared (K : Type) where
  world : World K
  exported : Fact
  available : List Nat

/-- Executable checked instantiation: check the source against the snapshot's
    actual slots, materialize its view, then bind all names into the namespace. -/
def instantiate (n : Namespace) (l outer : World K) (e : Zkc.Source.FactorInputs.Source)
    (handle : Nat) : Option (Prepared K) :=
  if Zkc.Source.FactorInputs.check l.known e then
    some ⟨link n {l with values := Zkc.Source.FactorInputs.install l.values e handle} outer,
      fact n (Zkc.Source.FactorInputs.fact e handle),l.known.map (addr n)⟩
  else none

theorem instantiated_valid (n : Namespace) (l outer : World K)
    (e : Zkc.Source.FactorInputs.Source) (handle : Nat) (p : Prepared K)
    (accepted : instantiate n l outer e handle = some p) :
    Valid p.world.values [p.exported] ∧ Known p.world p.available ∧
      Zkc.Source.FactorInputs.check p.available (source n e) = true := by
  unfold instantiate at accepted
  split at accepted
  · rename_i good
    cases Option.some.inj accepted
    refine ⟨?_,link_known _ _ _,source_admitted n _ e good⟩
    intro f hf
    have he : f = fact n (Zkc.Source.FactorInputs.fact e handle) := by simpa using hf
    subst f
    exact means_transport n _ _ (link_interprets _ _ _)
      _ (Zkc.Source.FactorInputs.installed_means l.values e handle)
  · contradiction

/-- Trusted state rebinding preserves an existing cache without its producer.
    Passing decoded untrusted values as the local World does not supply valid. -/
theorem trusted_relink (n : Namespace) (l outer : World K) (f : Fact)
    (valid : Means l.values f) :
    Means (link n l outer).values (fact n f) ∧
    Known (link n l outer) (l.known.map (addr n)) :=
  ⟨means_transport n _ _ (link_interprets n l outer) f valid,link_known n l outer⟩

end Zkc.Modules.FactorBinding
