import Zkc.Transformations.Memoization

/-! Finite-slot immutable caching with full-key comparison and explicit bypass.

Collisions replace entries; they do not identify distinct keys. The work law
charges selected primitive work only. Observer access to cache cost is a separate
permission, and total runtime can increase despite this work bound.
-/

set_option autoImplicit false
namespace Zkc.Modules.BoundedCache

section
variable {K V E O : Type} {n : Nat} [DecidableEq K]

abbrev Slots (n : Nat) (K V : Type) := Fin n → Option (K × V)
def Valid (f : K → V) (s : Slots n K V) : Prop :=
  ∀ i k v, s i = some (k,v) → v = f k

def insert {K V : Type} {n : Nat} (s : Slots n K V) (i : Fin n) (entry : K × V) : Slots n K V :=
  fun j => if j = i then some entry else s j

def lookup (f : K → V) (slot : K → Fin n) (s : Slots n K V) (k : K) : V × Slots n K V :=
  match s (slot k) with
  | some (j,v) => if j=k then (v,s) else (f k,insert s (slot k) (k,f k))
  | none => (f k,insert s (slot k) (k,f k))

omit [DecidableEq K] in
theorem insert_valid (f : K → V) (s : Slots n K V) (h : Valid f s)
    (i : Fin n) (k : K) : Valid f (insert s i (k,f k)) := by
  intro j a v hv
  by_cases hj : j=i
  · subst j
    have hp : k=a ∧ f k=v := by simpa [insert] using hv
    rcases hp with ⟨rfl,hp⟩
    exact hp.symm
  · exact h j a v (by simpa [insert,hj] using hv)

theorem lookup_value (f : K → V) (slot : K → Fin n) (s : Slots n K V)
    (k : K) (h : Valid f s) : (lookup f slot s k).1 = f k := by
  cases hs : s (slot k) with
  | none => simp [lookup,hs]
  | some pair =>
    rcases pair with ⟨j,v⟩
    by_cases he : j=k
    · subst j; simpa [lookup,hs] using h (slot k) k v hs
    · simp [lookup,hs,he]

theorem lookup_valid (f : K → V) (slot : K → Fin n) (s : Slots n K V)
    (k : K) (h : Valid f s) : Valid f (lookup f slot s k).2 := by
  cases hs : s (slot k) with
  | none => simpa [lookup,hs] using insert_valid f s h (slot k) k
  | some pair =>
    rcases pair with ⟨j,v⟩
    by_cases he : j=k
    · simpa [lookup,hs,he] using h
    · simpa [lookup,hs,he] using insert_valid f s h (slot k) k

-- None explicitly bypasses memoization (including a capacity-zero policy).
def query (f : K → V) (slot : K → Option (Fin n)) (s : Slots n K V) (k : K) : V × Slots n K V :=
  match slot k with
  | none => (f k,s)
  | some i => lookup f (fun _ => i) s k

theorem query_value (f : K → V) (slot : K → Option (Fin n)) (s : Slots n K V)
    (k : K) (h : Valid f s) : (query f slot s k).1 = f k := by
  cases hs : slot k with
  | none => simp [query,hs]
  | some i => simpa [query,hs] using lookup_value f (fun _ => i) s k h

theorem query_valid (f : K → V) (slot : K → Option (Fin n)) (s : Slots n K V)
    (k : K) (h : Valid f s) : Valid f (query f slot s k).2 := by
  cases hs : slot k with
  | none => simpa [query,hs] using h
  | some i => simpa [query,hs] using lookup_valid f (fun _ => i) s k h

def run (f : K → V) (slot : K → Option (Fin n)) (s : Slots n K V) :
    Zkc.Transformations.Memoization.Client K V E O → (List E × O) × Slots n K V
  | .done o => (([],o),s)
  | .emit e p => let r := run f slot s p; ((e::r.1.1,r.1.2),r.2)
  | .call k next => let r := query f slot s k; run f slot r.2 (next r.1)

theorem preservation (f : K → V) (slot : K → Option (Fin n))
    (p : Zkc.Transformations.Memoization.Client K V E O) (s : Slots n K V) (h : Valid f s) :
    (run f slot s p).1 = Zkc.Transformations.Memoization.run f p ∧ Valid f (run f slot s p).2 := by
  induction p generalizing s with
  | done o => exact ⟨rfl,h⟩
  | emit e p ih =>
    obtain ⟨hv,hc⟩ := ih s h
    constructor
    · simp only [run,Zkc.Transformations.Memoization.run]; rw [hv]
    · exact hc
  | call k next ih =>
    have hc := query_valid f slot s k h
    have hv := query_value f slot s k h
    simpa only [run,Zkc.Transformations.Memoization.run,hv] using ih (f k) (query f slot s k).2 hc

omit [DecidableEq K] in
theorem empty_valid (f : K → V) : Valid f (fun (_ : Fin n) => none) := by
  intro i k v h; contradiction

-- Collision resistance and an injective slot function are not premises.
theorem policy_independent {m : Nat} (f : K → V) (a : K → Option (Fin n))
    (b : K → Option (Fin m)) (p : Zkc.Transformations.Memoization.Client K V E O) :
    (run f a (fun _ => none) p).1 = (run f b (fun _ => none) p).1 :=
  (preservation f a p _ (empty_valid f)).1.trans
    (preservation f b p _ (empty_valid f)).1.symm

-- One physical slot, three distinct requests: replacement still preserves data.
def oneSlot (_ : Nat) : Option (Fin 1) := some 0
def collisionClient : Zkc.Transformations.Memoization.Client Nat Nat Unit (Nat × Nat × Nat) :=
  .call 1 (fun a => .call 2 (fun b => .call 1 (fun c => .done (a,b,c))))
theorem collision_control :
    (run (fun k => k+1) oneSlot (fun _ => none) collisionClient).1 = ([],(2,3,2)) := by decide


end

section
variable {K V E O : Type} {n : Nat} [DecidableEq K]

-- Only the chosen primitive work is charged. Lookup, allocation and equality
-- are not free in the implementation; they are outside this particular metric.
def charge (weight : K → Nat) (slot : K → Option (Fin n)) (s : Slots n K V) (k : K) : Nat :=
  match slot k with
  | none => weight k
  | some i => match s i with
    | none => weight k
    | some (j,_) => if j=k then 0 else weight k

def plainWork (f : K → V) (weight : K → Nat) : Zkc.Transformations.Memoization.Client K V E O → Nat
  | .done _ => 0
  | .emit _ p => plainWork f weight p
  | .call k next => weight k + plainWork f weight (next (f k))

def work (f : K → V) (weight : K → Nat) (slot : K → Option (Fin n))
    (s : Slots n K V) : Zkc.Transformations.Memoization.Client K V E O → Nat
  | .done _ => 0
  | .emit _ p => work f weight slot s p
  | .call k next => let r := query f slot s k
                   charge weight slot s k + work f weight slot r.2 (next r.1)

theorem charge_le (weight : K → Nat) (slot : K → Option (Fin n))
    (s : Slots n K V) (k : K) : charge weight slot s k ≤ weight k := by
  unfold charge
  split
  · exact Nat.le_refl _
  · split
    · exact Nat.le_refl _
    · split
      · exact Nat.zero_le _
      · exact Nat.le_refl _

-- Even an adversarially collision-heavy input cannot increase this selected
-- primitive-work measure. It can still increase total wall time.
theorem work_le_plain (f : K → V) (weight : K → Nat) (slot : K → Option (Fin n))
    (p : Zkc.Transformations.Memoization.Client K V E O) (s : Slots n K V) (h : Valid f s) :
    work f weight slot s p ≤ plainWork f weight p := by
  induction p generalizing s with
  | done _ => exact Nat.le_refl _
  | emit _ p ih => exact ih s h
  | call k next ih =>
    have rest := ih (f k) (query f slot s k).2 (query_valid f slot s k h)
    have hv := query_value f slot s k h
    simpa only [work,plainWork,hv] using Nat.add_le_add (charge_le weight slot s k) rest

theorem bypass_work (f : K → V) (weight : K → Nat)
    (p : Zkc.Transformations.Memoization.Client K V E O) (s : Slots n K V) :
    work f weight (fun _ => none) s p = plainWork f weight p := by
  induction p with
  | done _ => rfl
  | emit _ p ih => exact ih
  | call k next ih => simpa [work,charge,query,plainWork] using congrArg (weight k + ·) (ih (f k))

-- Pure result preservation alone does not authorize memoization under an
-- observer that can see private-key equality through execution cost.
def privateClient (secret : Bool) : Zkc.Transformations.Memoization.Client Nat Nat Unit Unit :=
  .call 0 (fun _ => .call (if secret then 0 else 1) (fun _ => .done ()))

theorem cost_observer_control :
    Zkc.Transformations.Memoization.run (fun _ => 0) (privateClient true) =
      Zkc.Transformations.Memoization.run (fun _ => 0) (privateClient false) ∧
    plainWork (fun _ => 0) (fun _ => 1) (privateClient true) = 2 ∧
    plainWork (fun _ => 0) (fun _ => 1) (privateClient false) = 2 ∧
    work (fun _ => 0) (fun _ => 1) oneSlot (fun _ => none) (privateClient true) = 1 ∧
    work (fun _ => 0) (fun _ => 1) oneSlot (fun _ => none) (privateClient false) = 2 := by decide


end

end Zkc.Modules.BoundedCache
