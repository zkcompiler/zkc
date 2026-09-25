import Zkc.Source.Availability
import Zkc.Protocols.CorrelatedSetup.Source
import Zkc.Protocols.Sumcheck.LocalProver.Code

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace Zkc.Protocols.CapturedPrograms
open Zkc.Source.Availability Zkc.Source.Expressions
open Zkc.Protocols.Sumcheck.LocalProver (codeInputs)

/-- Literal payloads are first-order values, with no code-producing callback. -/
structure Literal where
  service : Zkc.Protocols.CorrelatedSetup.Source.Program
  causal : Zkc.Protocols.Sumcheck.LocalProver.Code
  deriving DecidableEq

/-- Five captures construct the complete Zkc.Protocols.CorrelatedSetup setup. The causal source receives
    that same vector; additional captures are permitted. -/
def Literal.OK (c : Literal) (n : Nat) : Prop :=
  c.service.Good ∧ 5 ≤ n ∧ ∀ i ∈ codeInputs c.causal, i < n
instance (c : Literal) (n : Nat) : Decidable (c.OK n) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

inductive Tree where
  | leaf : Literal → List (Expr Nat) → Tree
  | ifz : Expr Nat → Tree → Tree → Tree
  deriving DecidableEq

def Tree.deps : Tree → List Nat
  | .leaf _ es => es.flatMap Expr.deps
  | .ifz e p q => e.deps ++ p.deps ++ q.deps

def Tree.valid : Tree → Bool
  | .leaf c es => decide (c.OK es.length)
  | .ifz _ p q => p.valid && q.valid

structure Issued (F : Type) where
  code : Literal
  inputs : List F
  deriving DecidableEq

variable {F : Type} [CommRing F] [DecidableEq F]

def select (s : Env F) : Tree → Issued F
  | .leaf c es => ⟨c, es.map (fun e => e.eval (total s))⟩
  | .ifz e p q => if e.eval (total s) = 0 then select s p else select s q

/-- Check the whole finite tree before selection, including dormant captures.
    This conservative policy makes rejection part of the agreement result. -/
def issue (scope : List Nat) (s : Env F) (p : Tree) : Option (Issued F) :=
  if ready scope s p.deps && p.valid then some (select s p) else none

theorem select_agreement (p : Tree) (s t : Env F)
    (h : ∀ i ∈ p.deps, s i = t i) : select s p = select t p := by
  induction p with
  | leaf c es =>
    simp only [select]
    congr 1
    apply List.map_congr_left
    intro e he
    apply eval_agreement
    intro i hi
    exact congrArg (fun x : Option F => x.getD 0) (h i (List.mem_flatMap.mpr ⟨e,he,hi⟩))
  | ifz e p q ihp ihq =>
    have he : e.eval (total s) = e.eval (total t) := eval_agreement e _ _ (by
      intro i hi
      exact congrArg (fun x : Option F => x.getD 0) (h i (by simp [Tree.deps,hi])))
    have hp := ihp (fun i hi => h i (by simp [Tree.deps,hi]))
    have hq := ihq (fun i hi => h i (by simp [Tree.deps,hi]))
    simp only [select,he,hp,hq]

/-- Equality of selected literal code AND actual captured values, including
    equal refusals. No equality witness or host generator is an input to issue. -/
theorem issue_agreement (scope : List Nat) (s t : Env F) (p : Tree)
    (h : Agree scope s t) : issue scope s p = issue scope t p := by
  have hr := ready_agreement scope s t p.deps h
  by_cases hs : ready scope s p.deps = true
  · have hv := select_agreement p s t (fun i hi =>
      h i (((ready_iff scope s p.deps).mp hs i hi).1))
    simp [issue,← hr,hs,hv]
  · simp [issue,← hr,hs]

theorem select_ok (p : Tree) (s : Env F) (h : p.valid = true) :
    (select s p).code.OK (select s p).inputs.length := by
  induction p with
  | leaf c es => simpa [Tree.valid,select] using h
  | ifz e p q ihp ihq =>
    have hh := Bool.and_eq_true_iff.mp h
    simp only [select]
    split
    · exact ihp hh.1
    · exact ihq hh.2

theorem issued_ok (scope : List Nat) (s : Env F) (p : Tree) (x : Issued F)
    (h : issue scope s p = some x) : x.code.OK x.inputs.length := by
  unfold issue at h
  split at h
  · rename_i hg
    have hx : select s p = x := Option.some.inj h
    rw [← hx]
    exact select_ok p s (Bool.and_eq_true_iff.mp hg).2
  · contradiction

theorem issued_reads_bound (scope : List Nat) (s : Env F) (p : Tree) (x : Issued F)
    (h : issue scope s p = some x) (i : Nat) (hi : i ∈ p.deps) :
    i ∈ scope ∧ ∃ v, s i = some v := by
  unfold issue at h
  split at h
  · rename_i hg
    have hr := (ready_iff scope s p.deps).mp (Bool.and_eq_true_iff.mp hg).1 i hi
    exact ⟨hr.1, Option.isSome_iff_exists.mp hr.2⟩
  · contradiction

theorem issued_input_bound (scope : List Nat) (s : Env F) (p : Tree) (x : Issued F)
    (h : issue scope s p = some x) (i : Nat) (hi : i ∈ codeInputs x.code.causal) :
    ∃ v, x.inputs[i]? = some v := by
  have hb := (issued_ok scope s p x h).2.2 i hi
  exact ⟨x.inputs[i], List.getElem?_eq_getElem hb⟩

/-- Capture at creation: invocation uses the retained vector, never a live Env. -/
def setup (x : Issued F) : Zkc.Protocols.CorrelatedSetup.Setup F :=
  ⟨x.inputs[0]?.getD 0,x.inputs[1]?.getD 0,x.inputs[2]?.getD 0,
   x.inputs[3]?.getD 0,x.inputs[4]?.getD 0⟩

def controller (x : Issued F) (w : Zkc.Protocols.CorrelatedSetup.Witness F) : Zkc.Protocols.CorrelatedSetup.Service.Controller F :=
  x.code.service.denote (setup x) w

/-- The actual Zkc.Source.Expressions controller law after checked, potentially varying issuance. -/
theorem issued_same_controller (scope : List Nat) (s t : Env F) (p : Tree)
    (x y : Issued F) (hx : issue scope s p = some x) (hy : issue scope t p = some y)
    (agree : Agree scope s t) (w v : Zkc.Protocols.CorrelatedSetup.Witness F) : controller x w = controller y v := by
  have hxy : x = y := Option.some.inj (hx.symm.trans ((issue_agreement scope s t p agree).trans hy))
  subst y
  exact Zkc.Protocols.CorrelatedSetup.Source.same_controller x.code.service (issued_ok scope s p x hx).1 (setup x) w v

/-- Complete finite repeated-service joint mass, with the captured common setup. -/
theorem issued_service_mass [Fintype F] (scope : List Nat) (s t : Env F) (p : Tree)
    (x y : Issued F) (hx : issue scope s p = some x) (hy : issue scope t p = some y)
    (agree : Agree scope s t) (w v : Zkc.Protocols.CorrelatedSetup.Witness F) (n : Nat)
    (out : Zkc.Protocols.CorrelatedSetup.Triple F × Zkc.Protocols.CorrelatedSetup.Service.History F) :
    (Fintype.card {r : Zkc.Protocols.CorrelatedSetup.Triple F × Zkc.Probability.AdaptiveTape.Tape F n //
      Zkc.Protocols.CorrelatedSetup.Source.sourceCompiled x.code.service (setup x) w n r = out} : ℚ) /
        Fintype.card (Zkc.Protocols.CorrelatedSetup.Triple F × Zkc.Probability.AdaptiveTape.Tape F n) =
    (Fintype.card {r : Zkc.Protocols.CorrelatedSetup.Triple F × Zkc.Probability.AdaptiveTape.Tape F n //
      Zkc.Protocols.CorrelatedSetup.Source.sourceCompiled y.code.service (setup y) v n r = out} : ℚ) /
        Fintype.card (Zkc.Protocols.CorrelatedSetup.Triple F × Zkc.Probability.AdaptiveTape.Tape F n) := by
  have hxy : x = y := Option.some.inj (hx.symm.trans ((issue_agreement scope s t p agree).trans hy))
  subst y
  exact Zkc.Protocols.CorrelatedSetup.Source.source_compiled_witness_mass _ (issued_ok scope s p x hx).1 _ w v n out


end Zkc.Protocols.CapturedPrograms
