import Zkc.Source.LocalArithmetic
import Zkc.Semantics.OperationContract

/-! Source-relative arithmetic DAG certificates with explicit occurrence binding.

Nodes refer into the tail of the reversed instruction list. `wellFormed` checks
those indices and nonzero moduli; total evaluators use defaults on malformed
references, so evaluator equality alone does not establish admission.
`check` also binds the source and site, compares the expanded root with the
retained source expression, and checks raw inputs even in dead nodes.
Raw input scanning preserves sharing. Root comparison still expands the DAG;
no linear certificate-checking or end-to-end resource bound is claimed here.
-/

set_option autoImplicit false

namespace Zkc.Compiler.Arithmetic.Dag
-- An occurrence key is source-local and is paired with a source/site below.
inductive Instr where
 | lit : Nat → Instr
 | input : Nat → Instr
 | add : Nat → Nat → Instr
 | mul : Nat → Nat → Instr
 | mod : Nat → Nat → Instr
 deriving Repr, DecidableEq
abbrev DAG := List Instr

def expandOne (es : List Zkc.Source.LocalArithmetic.Expr) : Instr → Zkc.Source.LocalArithmetic.Expr
 | .lit n => .lit n
 | .input k => .input k
 | .add i j => .add (es[i]?.getD (.lit 0)) (es[j]?.getD (.lit 0))
 | .mul i j => .mul (es[i]?.getD (.lit 0)) (es[j]?.getD (.lit 0))
 | .mod i q => .mod (es[i]?.getD (.lit 0)) q

def runOne (ρ : Zkc.Source.LocalArithmetic.Env) (vs : List Nat) : Instr → Nat
 | .lit n => n
 | .input k => ρ k
 | .add i j => vs[i]?.getD 0 + vs[j]?.getD 0
 | .mul i j => vs[i]?.getD 0 * vs[j]?.getD 0
 | .mod i q => vs[i]?.getD 0 % q

def expand : DAG → List Zkc.Source.LocalArithmetic.Expr
 | [] => []
 | i::is => let es := expand is; expandOne es i :: es

/-- Scan raw inputs, including dead nodes, without revisiting expanded subtrees. -/
def Instr.checkInputs (available : Nat → Bool) : Instr → Bool
 | .input k => available k
 | _ => true

/-- Raw input availability agrees with checking every expanded expression,
    even before imposing well-formed references. -/
theorem expand_all_check (available : Nat → Bool) (d : DAG) :
    (expand d).all (fun e => e.check available) = d.all (Instr.checkInputs available) := by
  induction d with
  | nil => rfl
  | cons i ds ih =>
      simp only [expand, List.all_cons]
      rw [ih]
      cases hs : ds.all (Instr.checkInputs available) with
      | false => simp
      | true =>
          have checked : (expand ds).all (fun e => e.check available) = true := ih.trans hs
          have lookup (k : Nat) :
              ((expand ds)[k]?.getD (.lit 0)).check available = true := by
            cases hk : (expand ds)[k]? with
            | none => simp [Zkc.Source.LocalArithmetic.Expr.check]
            | some e =>
                simpa [hk] using
                  (List.all_eq_true.mp checked) e (List.mem_of_getElem? hk)
          cases i <;>
            simp [Instr.checkInputs, expandOne, Zkc.Source.LocalArithmetic.Expr.check, lookup]

def runDAG (ρ : Zkc.Source.LocalArithmetic.Env) : DAG → List Nat
 | [] => []
 | i::is => let vs := runDAG ρ is; runOne ρ vs i :: vs

def bounded (n : Nat) : Instr → Bool
 | .lit _ | .input _ => true
 | .add i j | .mul i j => decide (i < n ∧ j < n)
 | .mod i q => decide (i < n ∧ 0 < q)
def wellFormed : DAG → Bool
 | [] => true
 | i::is => bounded is.length i && wellFormed is

theorem get_eval (es : List Zkc.Source.LocalArithmetic.Expr) (ρ : Zkc.Source.LocalArithmetic.Env) (m : Zkc.Source.LocalArithmetic.Memory) (i : Nat) :
 ((es.map (Zkc.Source.LocalArithmetic.Expr.eval ρ m))[i]?).getD 0 =
 (es[i]?.getD (.lit 0)).eval ρ m := by
 simp only [List.getElem?_map]
 cases es[i]? <;> rfl

theorem one_sound (es : List Zkc.Source.LocalArithmetic.Expr) (ρ : Zkc.Source.LocalArithmetic.Env) (m : Zkc.Source.LocalArithmetic.Memory) (i : Instr) :
 runOne ρ (es.map (Zkc.Source.LocalArithmetic.Expr.eval ρ m)) i = (expandOne es i).eval ρ m := by
 cases i <;> simp only [runOne, expandOne, Zkc.Source.LocalArithmetic.Expr.eval, get_eval]

theorem dag_sound (d : DAG) (ρ : Zkc.Source.LocalArithmetic.Env) (m : Zkc.Source.LocalArithmetic.Memory) :
 runDAG ρ d = (expand d).map (Zkc.Source.LocalArithmetic.Expr.eval ρ m) := by
 induction d with
 | nil => rfl
 | cons i is ih => simp [runDAG, expand, ih, one_sound]

structure Subject where
 source : String
 site : Zkc.Semantics.OperationContract.Site
 expr : Zkc.Source.LocalArithmetic.Expr
 deriving DecidableEq
structure Certificate where
 source : String
 site : Zkc.Semantics.OperationContract.Site
 dag : DAG
 deriving DecidableEq

-- Raw input checking also rules out unavailable inputs in dead nodes.
def check (s : Subject) (c : Certificate) (v : Zkc.Source.LocalArithmetic.View) : Bool :=
 decide (s.source = c.source ∧ s.site = c.site) && wellFormed c.dag &&
 decide ((expand c.dag).head? = some s.expr) &&
 c.dag.all (Instr.checkInputs (fun k => (v k).isSome))

theorem check_sound (s : Subject) (c : Certificate) (v : Zkc.Source.LocalArithmetic.View)
 (h : check s c v = true) :
 s.source = c.source ∧ s.site = c.site ∧
 (runDAG (fun k => (v k).getD 0) c.dag).head? =
   some (s.expr.eval (fun k => (v k).getD 0) []) := by
 simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
 refine ⟨h.1.1.1.1, h.1.1.1.2, ?_⟩
 rw [dag_sound c.dag _ []]
 simp [List.head?_map, h.1.2]

theorem source_available (s : Subject) (c : Certificate) (v : Zkc.Source.LocalArithmetic.View)
 (h : check s c v = true) : s.expr.check (fun k => (v k).isSome) = true := by
 simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
 have hm : s.expr ∈ expand c.dag := List.mem_of_head? h.1.2
 exact (List.all_eq_true.mp ((expand_all_check _ c.dag).trans h.2)) _ hm

-- Exact source occurrence table; values are a global environment, not a supplied
-- factorization/equivalence premise. No availability callback is accepted.
structure Occ where
 key : Nat
 release : Nat
 role : Nat
 deriving Repr, DecidableEq
def available (os : List Occ) (role site k : Nat) : Bool :=
 os.any (fun o => decide (o.key = k ∧ o.role = role ∧ o.release < site))
def view (os : List Occ) (role site : Nat) (ρ : Zkc.Source.LocalArithmetic.Env) : Zkc.Source.LocalArithmetic.View :=
 Zkc.Source.LocalArithmetic.project (available os role site) ρ

theorem local_source (s : Subject) (c : Certificate) (os : List Occ)
 (role : Nat) (ρ : Zkc.Source.LocalArithmetic.Env) (h : check s c (view os role s.site ρ) = true) :
 (runDAG (fun k => (view os role s.site ρ k).getD 0) c.dag).head? =
   some (s.expr.eval ρ []) := by
 have hs := (check_sound s c _ h).2.2
 have ha := source_available s c _ h
 have agree : ∀ k, ((view os role s.site ρ) k).isSome = true →
     ((view os role s.site ρ) k).getD 0 = ρ k := by
   intro k hk
   simp only [view, Zkc.Source.LocalArithmetic.project] at hk ⊢
   split <;> simp_all
 rw [Zkc.Source.LocalArithmetic.expr_confinement s.expr _ _ ρ agree ha []] at hs
 exact hs

end Zkc.Compiler.Arithmetic.Dag
