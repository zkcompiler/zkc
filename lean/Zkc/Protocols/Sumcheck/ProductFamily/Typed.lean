import Zkc.Protocols.Sumcheck.ProductFamily.Locality

set_option autoImplicit false

namespace Zkc.Protocols.Sumcheck.ProductFamily
open Zkc.Protocols.AlgebraicRounds.Scalar

open Zkc.Protocols.AlgebraicRounds.Scalar Zkc.Protocols.Sumcheck.ProductFamily

abbrev TE (n : Nat) := Expr (Ref n)
def lower {n : Nat} (e : TE n) : E := e.rename origin
def tc {n} (i : Fin n) (j : Fin 3) : TE n := .var (.coeff i j)
def td {n} (i : Fin n) : TE n := .var (.draw i)
def tb {n} (i : Fin n) : TE n :=
  .add (.add (.add (tc i 0) (tc i 0)) (tc i 1)) (tc i 2)
def tv {n} (i : Fin n) : TE n :=
  .add (tc i 0) (.add (.mul (tc i 1) (td i)) (.mul (tc i 2) (.mul (td i) (td i))))
def tr {n} (i : Fin n) : Nat × TE n × TE n :=
  (4+5*i.val, tb i, if h : i.val=0 then .var .claim else
    tv ⟨i.val-1, by have hi:=i.isLt; omega⟩)
def tp {n} (acc : TE n) : List (Fin n) → TE n
  | [] => acc
  | i :: is => tp (.mul acc (td i)) is
def successors (m : Nat) : List (Fin (m+1)) :=
  List.ofFn (fun i : Fin m => (⟨i.val+1, by have hi:=i.isLt; omega⟩ : Fin (m+1)))
def tf (m : Nat) : Nat × TE (m+1) × TE (m+1) :=
  (1+5*(m+1), tv ⟨m,by omega⟩, .add (tp (td 0) (successors m)) (td 0))
def typedChecks (m : Nat) : List (Nat × TE (m+1) × TE (m+1)) :=
  List.ofFn (fun i : Fin (m+1) => tr i) ++ [tf m]
def lowerCheck {n} (c : Nat × TE n × TE n) : Nat × E × E :=
  (c.1,lower c.2.1,lower c.2.2)

@[simp] theorem lower_tb {n} (i : Fin n) : lower (tb i)=bound i.val := rfl
@[simp] theorem lower_tv {n} (i : Fin n) : lower (tv i)=atRound i.val := rfl
@[simp] theorem lower_td {n} (i : Fin n) : lower (td i)=dr i.val := rfl
@[simp] theorem lower_add {n} (a b : TE n) :
    lower (.add a b)=.add (lower a) (lower b) := rfl
@[simp] theorem lower_mul {n} (a b : TE n) :
    lower (.mul a b)=.mul (lower a) (lower b) := rfl
@[simp] theorem lower_claim {n} : lower (n:=n) (.var .claim)=.var 0 := rfl
theorem lower_tr {n} (i : Fin n) : lowerCheck (tr i)=roundCheck i.val := by
  by_cases h : i.val=0 <;> simp [lowerCheck,tr,roundCheck,h]
theorem lower_tp {n} (acc : TE n) (is : List (Fin n)) :
    lower (tp acc is)=productExpr (lower acc) (is.map Fin.val) := by
  induction is generalizing acc with
  | nil => rfl
  | cons i is ih => simp only [tp,List.map_cons,productExpr,ih,lower_mul,lower_td]
theorem successor_values (m : Nat) :
    (successors m).map Fin.val=(List.range m).map (·+1) := by
  apply List.ext_getElem
  · simp [successors]
  · intro i hi hj; simp [successors]
theorem lower_tf (m : Nat) : lowerCheck (tf m)=finalCheck m := by
  simp [lowerCheck,tf,finalCheck,lower_tp,successor_values]

-- An executable typed authoring function has a uniform lowering theorem.
-- There are no string binders, JSON values, MLIR parsers or native code here.
theorem typed_elaboration (m : Nat) :
    (typedChecks m).map lowerCheck=checks m := by
  simp only [typedChecks, List.map_append, List.map_singleton, lower_tf,checks]
  congr 1
  apply List.ext_getElem
  · simp only [List.length_map,List.length_ofFn,List.length_range]
  · intro i hi hj
    simp only [List.getElem_map,List.getElem_ofFn,List.getElem_range,lower_tr]

theorem elaborated_scope (m : Nat) (c : Nat × E × E)
    (h : c ∈ (typedChecks m).map lowerCheck) :
    Before c.1 c.2.1 ∧ Before c.1 c.2.2 := by
  rw [typed_elaboration] at h; exact scoped_checks m c h
theorem elaborated_meaning {F : Type} [CommRing F] [DecidableEq F]
    (env : Nat → F) (m : Nat) :
    (∀ c ∈ (typedChecks m).map lowerCheck, c.2.1.eval env=c.2.2.eval env) ↔
      runIndexed env 0 (m+1) (env 0)=some (finalTarget env m) := by
  rw [typed_elaboration]
  exact source_iff_endpoint env m


end Zkc.Protocols.Sumcheck.ProductFamily
