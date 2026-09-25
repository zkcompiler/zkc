import Zkc.Probability.FiniteKernel

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
namespace Tests.ProviderSampling


/-- A seed is sampled ONCE from one of the explicit uniform populations below. -/
abbrev Tape := List Nat
structure Provider where
  tape : Tape
  cursor : Nat
  deriving Repr, DecidableEq

def next (s : Provider) : Option (Nat × Provider) :=
  match s.tape[s.cursor]? with
  | none => none
  | some x => some (x, {s with cursor := s.cursor + 1})

def iid : List Tape := (List.range 3).flatMap fun a =>
  (List.range 3).flatMap fun b => (List.range 3).map fun c => [a,b,c]
def urn : List Tape := iid.filter fun t => t.Nodup

def count (pop : List Tape) (p : Tape → Bool) : Nat := (pop.filter p).length
def hasPrefix (h t : Tape) : Bool := t.take h.length == h
def fiber (pop : List Tape) (h : Tape) : Nat := count pop (hasPrefix h)
def hit (pop : List Tape) (h : Tape) (d : Nat) : Nat :=
  count pop fun t => hasPrefix h t && (t[h.length]? == some d)

/-- Conditional equality in cross-multiplied form; all 3^3 seeds, all prefixes. -/
theorem iid_conditional : ∀ t ∈ iid, ∀ k : Fin 3, ∀ d : Fin 3,
    3 * hit iid (t.take k.val) d.val = fiber iid (t.take k.val) := by decide

/-- Exact depletion law: zero for a used symbol, 1/(3-k) for an unused one. -/
theorem urn_conditional : ∀ t ∈ urn, ∀ k : Fin 3, ∀ d : Fin 3,
    hit urn (t.take k.val) d.val * (3-k.val) =
      if d.val ∈ t.take k.val then 0 else fiber urn (t.take k.val) := by decide

theorem populations : iid.length = 27 ∧ urn.length = 6 := by decide
theorem positive_fibers : ∀ pop ∈ [iid,urn], ∀ t ∈ pop, ∀ k : Fin 3,
    0 < fiber pop (t.take k.val) := by decide

def missing (a b : Nat) : Nat := if a != 0 && b != 0 then 0
  else if a != 1 && b != 1 then 1 else 2

/-- Actual adaptive controller: after first output 0, attack the second with
    guess 1. Otherwise consume the second, then attack the third with missing.
    The chosen target is frozen before the target call. No new randomness. -/
def adaptive (s : Provider) : Bool :=
  match next s with
  | none => false
  | some (a,s1) =>
    if a == 0 then
      match next s1 with
      | none => false
      | some (d,_) => d == 1
    else
      match next s1 with
      | none => false
      | some (b,s2) =>
        let guess := missing a b
        match next s2 with
        | none => false
        | some (d,_) => d == guess

theorem adaptive_exact :
    count iid (fun t => adaptive ⟨t,0⟩) = 9 ∧
    count urn (fun t => adaptive ⟨t,0⟩) = 5 := by decide

theorem no_wraparound : ∀ t ∈ iid, next ⟨t,3⟩ = none := by decide

/-- Smallest nondegenerate marginal separator: one uniform bit, two uses. -/
def repeatBit : List Tape := [[0,0],[1,1]]
def binaryIid : List Tape := [[0,0],[0,1],[1,0],[1,1]]
theorem repeat_marginals : ∀ k : Fin 2, ∀ d : Fin 2,
    count repeatBit (fun t => t[k.val]? == some d.val) = 1 := by decide
theorem repeat_predictable : ∀ t ∈ repeatBit,
    hit repeatBit (t.take 1) (t[0]?.getD 0) = fiber repeatBit (t.take 1) := by decide

/-- Setup is XOR of both independent bits. Public first-output conditioning
    remains uniform, but setup plus that output determines the second. -/
def setup (t : Tape) : Nat := (t[0]?.getD 0 + t[1]?.getD 0) % 2
def jointFiber (z a : Nat) : Nat := count binaryIid fun t =>
  setup t == z && t[0]? == some a
def jointHit (z a d : Nat) : Nat := count binaryIid fun t =>
  setup t == z && t[0]? == some a && t[1]? == some d

theorem setup_public_uniform : ∀ a d : Fin 2,
    2 * hit binaryIid [a.val] d.val = fiber binaryIid [a.val] := by decide
theorem setup_joint_predictable : ∀ z a : Fin 2,
    jointFiber z.val a.val = 1 ∧
    jointHit z.val a.val ((z.val+a.val)%2) = 1 := by decide

theorem setup_alone_uniform : ∀ z d : Fin 2,
    count binaryIid (fun t => setup t == z.val && t[1]? == some d.val) = 1 := by decide

/-- Revealing the whole seed collapses even IID's next-output cap to one. -/
theorem full_seed_predictable : ∀ t ∈ iid, ∀ k : Fin 3,
    next ⟨t,k.val⟩ = some (t[k.val]?.getD 0,⟨t,k.val+1⟩) := by decide

-- The actual populations these laws are stated over, and one conditional
-- fibre of the urn, so a change in the fixture shows up here first.
#guard (iid.length, urn.length,
  count iid (fun t => adaptive ⟨t,0⟩), count urn (fun t => adaptive ⟨t,0⟩)) = (27, 6, 9, 5)
#guard (hit urn [0] 1, fiber urn [0], hit urn [0,1] 2, fiber urn [0,1]) = (1, 2, 1, 1)


/-- Exact rational point masses; positive_fibers separately excludes null views. -/
theorem iid_point_mass : ∀ t ∈ iid, ∀ k : Fin 3, ∀ d : Fin 3,
    (hit iid (t.take k.val) d.val : ℚ) / fiber iid (t.take k.val) = 1/3 := by decide +kernel

theorem urn_point_mass : ∀ t ∈ urn, ∀ k : Fin 3, ∀ d : Fin 3,
    (hit urn (t.take k.val) d.val : ℚ) / fiber urn (t.take k.val) =
      if d.val ∈ t.take k.val then 0 else 1/(3-k.val : ℚ) := by decide +kernel

theorem adaptive_probabilities :
    (count iid (fun t => adaptive ⟨t,0⟩) : ℚ) / iid.length = 1/3 ∧
    (count urn (fun t => adaptive ⟨t,0⟩) : ℚ) / urn.length = 5/6 := by decide +kernel

/-- Conditional bounds lose information monotonically: the full setup view
    violates 1/2 although the public-prefix view has that exact point mass. -/
theorem setup_cap_violation : ∀ z a : Fin 2,
    (1/2 : ℚ) < (jointHit z.val a.val ((z.val+a.val)%2) : ℚ) /
      jointFiber z.val a.val := by decide +kernel


end Tests.ProviderSampling
