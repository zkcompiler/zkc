import Zkc.Compiler.Blocks.Replacement
import Mathlib.Tactic.Ring

/-! Symbolic expansion, semiring rewrite laws, literal transport and source-relative rule admission. -/

set_option autoImplicit false
namespace Zkc.Compiler.Blocks

section
variable {V : Type}

def expand (sym : Nat → Expr V) : Expr V → Expr V
  | .input i => sym i
  | .literal v => .literal v
  | .apply op a b => .apply op (expand sym a) (expand sym b)
  | .choose c a b => .choose (expand sym c) (expand sym a) (expand sym b)

theorem eval_expand (f : Key V → V) (truth : V → Bool) (env : Nat → V)
    (sym : Nat → Expr V) (e : Expr V) :
    eval f truth env (expand sym e) = eval f truth (fun i => eval f truth env (sym i)) e := by
  induction e with
  | input i => rfl
  | literal v => rfl
  | apply op a b iha ihb => simp only [expand,eval,iha,ihb]
  | choose c a b ihc iha ihb => simp only [expand,eval,ihc,iha,ihb]

def expandBlock : Block V → (Nat → Expr V) → (Nat → Expr V)
  | [], sym => sym
  | (dst,e) :: rest, sym => expandBlock rest (Function.update sym dst (expand sym e))

theorem expansion_sound (f : Key V → V) (truth : V → Bool) (env : Nat → V)
    (block : Block V) (sym : Nat → Expr V) (i : Nat) :
    eval f truth env (expandBlock block sym i) =
      runBlock f truth block (fun j => eval f truth env (sym j)) i := by
  induction block generalizing sym with
  | nil => rfl
  | cons step rest ih =>
    simp only [expandBlock,runBlock]
    rw [ih]
    congr 2
    funext j
    by_cases hj : j = step.1
    · subst j; simp [assign,eval_expand]
    · simp [assign,Function.update_of_ne hj]

def quadratic {V : Type} : Expr V :=
  .apply "field.add" (.input 0)
    (.apply "field.add" (.apply "field.mul" (.input 1) (.input 3))
      (.apply "field.mul" (.input 2) (.apply "field.mul" (.input 3) (.input 3))))
def horner {V : Type} : Expr V :=
  .apply "field.add" (.input 0)
    (.apply "field.mul" (.apply "field.add" (.input 1)
      (.apply "field.mul" (.input 2) (.input 3))) (.input 3))

-- Weakest algebra here: a semiring suffices; commutativity and field inverses
-- are not used because Horner keeps the challenge on the right.
def arithmetic {F : Type} [Semiring F] (k : Key F) : F :=
  if k.1 = "field.add" then k.2.1 + k.2.2
  else if k.1 = "field.mul" then k.2.1 * k.2.2 else 0

theorem horner_semiring {F : Type} [Semiring F] (truth : F → Bool) (env : Nat → F) :
    eval arithmetic truth env quadratic = eval arithmetic truth env horner := by
  simp [eval,quadratic,horner,arithmetic,add_mul,mul_assoc]

def hornerCheck [DecidableEq V] (source target : Block V) (ss ts : Nat) : Bool :=
  decide (expandBlock source Expr.input ss = quadratic ∧
    expandBlock target Expr.input ts = horner)

theorem checked_horner {F : Type} [Semiring F] [DecidableEq F]
    (truth : F → Bool) (source target : Block F) (ss ts : Nat)
    (ok : hornerCheck source target ss ts = true) :
    EquivalentOn arithmetic truth (fun _ => True) source target [ss] [ts] := by
  have h := of_decide_eq_true ok
  intro env _
  have hs := expansion_sound arithmetic truth env source Expr.input ss
  have ht := expansion_sound arithmetic truth env target Expr.input ts
  simp only [h.1,h.2] at hs ht
  simp only [exports,List.map_cons,List.map_nil,List.cons.injEq,and_true]
  exact hs.symm.trans ((horner_semiring truth env).trans ht)


end

section
variable {V W : Type}

def mapExpr (conv : V → W) : Expr V → Expr W
  | .input i => .input i
  | .literal v => .literal (conv v)
  | .apply op a b => .apply op (mapExpr conv a) (mapExpr conv b)
  | .choose c a b => .choose (mapExpr conv c) (mapExpr conv a) (mapExpr conv b)

def mapBlock (conv : V → W) (block : Block V) : Block W :=
  block.map fun step => (step.1,mapExpr conv step.2)

theorem map_expand (conv : V → W) (sym : Nat → Expr V) (e : Expr V) :
    mapExpr conv (expand sym e) = expand (fun i => mapExpr conv (sym i)) (mapExpr conv e) := by
  induction e with
  | input i => rfl
  | literal v => rfl
  | apply op a b iha ihb => simp only [expand,mapExpr,iha,ihb]
  | choose c a b ihc iha ihb => simp only [expand,mapExpr,ihc,iha,ihb]

theorem map_expand_block (conv : V → W) (block : Block V) (sym : Nat → Expr V) (i : Nat) :
    mapExpr conv (expandBlock block sym i) =
      expandBlock (mapBlock conv block) (fun j => mapExpr conv (sym j)) i := by
  induction block generalizing sym with
  | nil => rfl
  | cons step rest ih =>
    simp only [expandBlock,mapBlock,List.map_cons]
    rw [ih]
    congr 2
    funext j
    by_cases hj : j = step.1
    · subst j; simp [map_expand]
    · simp [Function.update_of_ne hj]

-- The executed raw checker is literal-representation independent. A successful
-- template check transports to every semiring, not merely the checker carrier.
theorem horner_check_transport [DecidableEq V] [DecidableEq W]
    (conv : V → W) (source target : Block V) (ss ts : Nat)
    (ok : hornerCheck source target ss ts = true) :
    hornerCheck (mapBlock conv source) (mapBlock conv target) ss ts = true := by
  have h := of_decide_eq_true ok
  apply decide_eq_true
  constructor
  · have x := map_expand_block conv source Expr.input ss
    rw [h.1] at x
    exact x.symm
  · have x := map_expand_block conv target Expr.input ts
    rw [h.2] at x
    exact x.symm

theorem admitted_template_any_semiring {F : Type} [Semiring F] [DecidableEq V] [DecidableEq F]
    (conv : V → F) (truth : F → Bool) (source target : Block V) (ss ts : Nat)
    (ok : hornerCheck source target ss ts = true) :
    EquivalentOn arithmetic truth (fun _ => True) (mapBlock conv source)
      (mapBlock conv target) [ss] [ts] :=
  checked_horner truth _ _ ss ts (horner_check_transport conv source target ss ts ok)

-- Fully joined model corollary: the same raw check executed by the admission
-- tool justifies an actual compiled module replacement, also with optional
-- sharing, under every interpreted semiring and state-action continuation.
theorem checked_template_context {F A O S E : Type} [Semiring F]
    [DecidableEq V] [DecidableEq F] (conv : V → F) (truth : F → Bool)
    (source target : Block V) (ss ts : Nat) (ok : hornerCheck source target ss ts = true)
    (handler : A → S → F × S × List E) (env : Nat → F)
    (next : List F → Program F A O) (s : S)
    (store : Zkc.Modules.ImmutableCache.Cache (Key F) F → Key F → Bool)
    (cache : Zkc.Modules.ImmutableCache.Cache (Key F) F) (valid : Zkc.Modules.ImmutableCache.Valid arithmetic cache) :
    (Zkc.Transformations.Memoization.runMemo arithmetic store cache
      (lower handler (moduleCall truth (mapBlock conv target) [ts] env next) s)).1 =
      runProgram arithmetic handler (moduleCall truth (mapBlock conv source) [ss] env next) s ∧
    Zkc.Modules.ImmutableCache.Valid arithmetic (Zkc.Transformations.Memoization.runMemo arithmetic store cache
      (lower handler (moduleCall truth (mapBlock conv target) [ts] env next) s)).2 :=
  replacement_with_sharing arithmetic truth handler (fun _ => True) _ _ [ss] [ts]
    (admitted_template_any_semiring conv truth source target ss ts ok)
    env trivial next s store cache valid

theorem infer_map (registry : String → Option (Signature String))
    (vt : V → String) (wt : W → String) (conv : V → W) (types : ∀ v, wt (conv v) = vt v)
    (flag : String) (ctx : Context String) (e : Expr V) :
    infer registry wt flag ctx (mapExpr conv e) = infer registry vt flag ctx e := by
  induction e with
  | input i => rfl
  | literal v => exact congrArg some (types v)
  | apply op a b iha ihb => simp only [mapExpr,infer,iha,ihb]
  | choose c a b ihc iha ihb => simp only [mapExpr,infer,ihc,iha,ihb]

theorem infer_block_map (registry : String → Option (Signature String))
    (vt : V → String) (wt : W → String) (conv : V → W) (types : ∀ v, wt (conv v) = vt v)
    (flag : String) (ctx : Context String) (block : Block V) :
    inferBlock registry wt flag (mapBlock conv block) ctx = inferBlock registry vt flag block ctx := by
  induction block generalizing ctx with
  | nil => rfl
  | cons step rest ih =>
    simp only [mapBlock,List.map_cons,inferBlock,infer_map registry vt wt conv types]
    split
    · rfl
    · split
      · rfl
      · exact ih _

def HornerMeaning (f : Key V → V) (truth : V → Bool) (pre : (Nat → V) → Prop) : Prop :=
  ∀ env, pre env → eval f truth env quadratic = eval f truth env horner

-- Unrelated operations of the same provider are arbitrary. Only the interpreted
-- field operations at reachable scalar values need the algebraic equations.
theorem boxed_horner {F : Type} [Semiring F] (box : F → V)
    (f : Key V → V) (truth : V → Bool)
    (addLaw : ∀ a b, f ("field.add",box a,box b) = box (a+b))
    (mulLaw : ∀ a b, f ("field.mul",box a,box b) = box (a*b))
    (env : Nat → V) (a b c r : F)
    (h0 : env 0 = box a) (h1 : env 1 = box b) (h2 : env 2 = box c) (h3 : env 3 = box r) :
    eval f truth env quadratic = eval f truth env horner := by
  simp only [quadratic,horner,eval,h0,h1,h2,h3,addLaw,mulLaw]
  rw [add_mul,mul_assoc]

theorem checked_horner_provider [DecidableEq V] (f : Key V → V) (truth : V → Bool)
    (pre : (Nat → V) → Prop) (meaning : HornerMeaning f truth pre)
    (source target : Block V) (ss ts : Nat) (ok : hornerCheck source target ss ts = true) :
    EquivalentOn f truth pre source target [ss] [ts] := by
  have h := of_decide_eq_true ok
  intro env hp
  have hs := expansion_sound f truth env source Expr.input ss
  have ht := expansion_sound f truth env target Expr.input ts
  simp only [h.1,h.2] at hs ht
  simp only [exports,List.map_cons,List.map_nil,List.cons.injEq,and_true]
  exact hs.symm.trans ((meaning env hp).trans ht)

theorem equivalent_weaken (f : Key V → V) (truth : V → Bool)
    (p q : (Nat → V) → Prop) (source target : Block V) (ss ts : List Nat)
    (h : EquivalentOn f truth p source target ss ts) (sub : ∀ env, q env → p env) :
    EquivalentOn f truth q source target ss ts := fun env hp => h env (sub env hp)


end

section
variable {V : Type} [DecidableEq V]

inductive Rule where | identity | horner
  deriving DecidableEq, Repr

def formation (registry : String → Option (Signature String)) (typeOf : V → String)
    (flag : String) (ctx : Context String) (block : Block V) (ex : List (Nat × String)) : Bool :=
  match inferBlock registry typeOf flag block ctx with
  | none => false
  | some out => exportsCheck out ex

def lawCheck (rule : Rule) (source target : Block V) (ss ts : List (Nat × String)) : Bool :=
  match rule with
  | .identity => decide (source = target ∧ ss = ts)
  | .horner => match ss,ts with
    | [(si,_)],[(ti,_)] => hornerCheck source target si ti
    | _,_ => false

def admission (registry : String → Option (Signature String)) (typeOf : V → String)
    (flag : String) (ctx : Context String) (source target : Block V)
    (ss ts : List (Nat × String)) (rule : Rule) : Bool :=
  formation registry typeOf flag ctx source ss && formation registry typeOf flag ctx target ts &&
    decide (ss.map Prod.snd = ts.map Prod.snd) && lawCheck rule source target ss ts

theorem law_check_sound (f : Key V → V) (truth : V → Bool) (pre : (Nat → V) → Prop)
    (rule : Rule) (meaning : rule = .horner → HornerMeaning f truth pre)
    (source target : Block V) (ss ts : List (Nat × String))
    (ok : lawCheck rule source target ss ts = true) :
    EquivalentOn f truth pre source target (ss.map Prod.fst) (ts.map Prod.fst) := by
  cases rule with
  | identity =>
    have h := of_decide_eq_true ok
    rcases h with ⟨rfl,rfl⟩
    intro env _; rfl
  | horner =>
    simp only [lawCheck] at ok
    split at ok <;> try contradiction
    next si st ti tt => exact checked_horner_provider f truth pre (meaning rfl) source target si ti ok

-- Soundness of the pure decision actually called by the JSON tool. Parsing and
-- source binding are external adapters. One single f is deliberately used for
-- signatures, the selected semantic law, cache validity, and execution.
theorem admission_sound {A O S E : Type}
    (registry : String → Option (Signature String)) (typeOf : V → String) (flag : String)
    (f : Key V → V) (truth : V → Bool) (types : Respects registry typeOf f)
    (handler : A → S → V × S × List E) (ctx : Context String)
    (source target : Block V) (ss ts : List (Nat × String)) (rule : Rule)
    (meaning : rule = .horner → HornerMeaning f truth (Fits typeOf ctx))
    (ok : admission registry typeOf flag ctx source target ss ts rule = true)
    (env : Nat → V) (fit : Fits typeOf ctx env) (next : List V → Program V A O) (s : S)
    (store : Zkc.Modules.ImmutableCache.Cache (Key V) V → Key V → Bool)
    (cache : Zkc.Modules.ImmutableCache.Cache (Key V) V) (valid : Zkc.Modules.ImmutableCache.Valid f cache) :
    (∀ i t, (i,t) ∈ ss → typeOf (runBlock f truth source env i) = t) ∧
    (∀ i t, (i,t) ∈ ts → typeOf (runBlock f truth target env i) = t) ∧
    (Zkc.Transformations.Memoization.runMemo f store cache
      (lower handler (moduleCall truth target (ts.map Prod.fst) env next) s)).1 =
      runProgram f handler (moduleCall truth source (ss.map Prod.fst) env next) s ∧
    Zkc.Modules.ImmutableCache.Valid f (Zkc.Transformations.Memoization.runMemo f store cache
      (lower handler (moduleCall truth target (ts.map Prod.fst) env next) s)).2 := by
  simp only [admission,Bool.and_eq_true] at ok
  obtain ⟨⟨⟨hs,ht⟩,_⟩,hl⟩ := ok
  simp only [formation] at hs ht
  split at hs <;> try contradiction
  next sout hsi =>
    split at ht <;> try contradiction
    next tout hti =>
      exact admitted_replacement_with_sharing registry typeOf flag f truth types handler
        source target ctx sout tout ss ts hsi hti hs ht
        (law_check_sound f truth (Fits typeOf ctx) rule meaning source target ss ts hl)
        env fit next s store cache valid


end

end Zkc.Compiler.Blocks
