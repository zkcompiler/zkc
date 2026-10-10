import Zkc.Compiler.Blocks.Typing

/-! Replacement at an ordered export boundary, composed with immutable sharing and the actual continuation. -/

set_option autoImplicit false
namespace Zkc.Compiler.Blocks

section
variable {V A O S E : Type}

def exports (slots : List Nat) (env : Nat → V) : List V := slots.map env

-- Callee locals are encapsulated: the client receives only ordered exports.
-- Source adapters must separately establish that this is the actual boundary.
def moduleCall (truth : V → Bool) (block : Block V) (slots : List Nat)
    (env : Nat → V) (next : List V → Program V A O) : Program V A O :=
  compileBlock truth block env (fun locals => next (exports slots locals))

def EquivalentOn (f : Key V → V) (truth : V → Bool) (pre : (Nat → V) → Prop)
    (source target : Block V) (sourceSlots targetSlots : List Nat) : Prop :=
  ∀ env, pre env → exports sourceSlots (runBlock f truth source env) =
    exports targetSlots (runBlock f truth target env)

-- A transformation and sharing can compose, with different local scratch shapes.
-- The continuation is arbitrary in the stated Program semantics, including state
-- actions and their complete trace. The cache and local scratch are not exported.
theorem replacement_with_sharing [DecidableEq V]
    (f : Key V → V) (truth : V → Bool) (handler : A → S → V × S × List E)
    (pre : (Nat → V) → Prop) (source target : Block V) (ss ts : List Nat)
    (relation : EquivalentOn f truth pre source target ss ts)
    (env : Nat → V) (hp : pre env) (next : List V → Program V A O) (s : S)
    (store : Zkc.Modules.ImmutableCache.Cache (Key V) V → Key V → Bool)
    (cache : Zkc.Modules.ImmutableCache.Cache (Key V) V) (valid : Zkc.Modules.ImmutableCache.Valid f cache) :
    (Zkc.Transformations.Memoization.runMemo f store cache (lower handler (moduleCall truth target ts env next) s)).1 =
      runProgram f handler (moduleCall truth source ss env next) s ∧
    Zkc.Modules.ImmutableCache.Valid f (Zkc.Transformations.Memoization.runMemo f store cache
      (lower handler (moduleCall truth target ts env next) s)).2 := by
  obtain ⟨ho,hv⟩ := memoized_block_correct f truth handler target env
    (fun locals => next (exports ts locals)) s store cache valid
  refine ⟨?_,hv⟩
  change _ = runProgram f handler (compileBlock truth source env _) s
  rw [compile_block_correct]
  exact ho.trans (congrArg (fun x => runProgram f handler (next x) s) (relation env hp).symm)

-- Typed admission supplies formation, while the relation supplies meaning.
-- Neither component can replace the other.
theorem admitted_replacement_with_sharing {T : Type} [DecidableEq T] [DecidableEq V]
    (registry : String → Option (Signature T)) (typeOf : V → T) (flag : T)
    (f : Key V → V) (truth : V → Bool) (law : Respects registry typeOf f)
    (handler : A → S → V × S × List E) (source target : Block V)
    (ctx sout tout : Context T) (ss ts : List (Nat × T))
    (hs : inferBlock registry typeOf flag source ctx = some sout)
    (ht : inferBlock registry typeOf flag target ctx = some tout)
    (hse : exportsCheck sout ss = true) (hte : exportsCheck tout ts = true)
    (relation : EquivalentOn f truth (Fits typeOf ctx) source target
      (ss.map Prod.fst) (ts.map Prod.fst))
    (env : Nat → V) (fit : Fits typeOf ctx env)
    (next : List V → Program V A O) (s : S)
    (store : Zkc.Modules.ImmutableCache.Cache (Key V) V → Key V → Bool)
    (cache : Zkc.Modules.ImmutableCache.Cache (Key V) V) (valid : Zkc.Modules.ImmutableCache.Valid f cache) :
    (∀ i t, (i,t) ∈ ss → typeOf (runBlock f truth source env i) = t) ∧
    (∀ i t, (i,t) ∈ ts → typeOf (runBlock f truth target env i) = t) ∧
    (Zkc.Transformations.Memoization.runMemo f store cache
      (lower handler (moduleCall truth target (ts.map Prod.fst) env next) s)).1 =
      runProgram f handler (moduleCall truth source (ss.map Prod.fst) env next) s ∧
    Zkc.Modules.ImmutableCache.Valid f (Zkc.Transformations.Memoization.runMemo f store cache
      (lower handler (moduleCall truth target (ts.map Prod.fst) env next) s)).2 := by
  exact ⟨checked_exports registry typeOf flag f truth law source ctx sout env ss fit hs hse,
    checked_exports registry typeOf flag f truth law target ctx tout env ts fit ht hte,
    replacement_with_sharing f truth handler (Fits typeOf ctx) source target _ _
      relation env fit next s store cache valid⟩


end

end Zkc.Compiler.Blocks
