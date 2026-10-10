import Zkc.Compiler.Role.Runner

/-! A structural relation between different finite effect trees. Erasure keeps
an endpoint continuation fixed for every joint reply; request projection retains
its actual head and relates only the replies delivered at the selected cut.
This is neither equality of trees nor equality of terminal outcomes. -/
set_option autoImplicit false
namespace Zkc.Compiler.Role.Simulation

inductive View (I J : PIR.Signature) (op : I.Op) where
  | silent
  | request (action : J.Op) (reply : I.Reply op → J.Reply action)
  | terminal (reason : PIR.Stop) (noReply : I.Reply op → False)

variable {I J : PIR.Signature} {A B C D : Type}

def Aligned (view : (op : I.Op) → View I J op) (result : A → B) :
    PIR.Proc I A → PIR.Proc J B → Prop
  | .done a, q => q = .done (result a)
  | .halt reason, q => q = .halt reason
  | .call op next, q =>
      match view op with
      | .silent => ∀ reply, Aligned view result (next reply) q
      | .request action map => ∃ tail, q = .call action tail ∧
          ∀ reply, Aligned view result (next reply) (tail (map reply))
      | .terminal reason _ => q = .halt reason

theorem aligned_bind (view : (op : I.Op) → View I J op) (result : A → B)
    (output : C → D) (p : PIR.Proc I A) (q : PIR.Proc J B)
    (related : Aligned view result p q)
    (k : A → PIR.Proc I C) (l : B → PIR.Proc J D)
    (tails : ∀ a, Aligned view output (k a) (l (result a))) :
    Aligned view output (p.bind k) (q.bind l) := by
  induction p generalizing q with
  | done a =>
      change q = .done (result a) at related
      subst q
      exact tails a
  | halt reason =>
      change q = .halt reason at related
      subst q
      rfl
  | call op next ih =>
      simp only [PIR.Proc.bind, Aligned] at related ⊢
      cases h : view op with
      | silent =>
          simp only [h] at related ⊢
          exact fun reply => ih reply q (related reply)
      | request action map =>
          simp only [h] at related ⊢
          obtain ⟨tail, rfl, related⟩ := related
          exact ⟨fun reply => (tail reply).bind l, rfl,
            fun reply => ih reply _ (related reply)⟩
      | terminal reason noReply =>
          simp only [h] at related ⊢
          subst q
          rfl

theorem aligned_repeat (view : (op : I.Op) → View I J op) (result : A → B)
    (step : A → PIR.Proc I A) (localStep : B → PIR.Proc J B)
    (related : ∀ a, Aligned view result (step a) (localStep (result a)))
    (count : Nat) (initial : A) :
    Aligned view result (PIR.repeatN count step initial)
      (PIR.repeatN count localStep (result initial)) := by
  induction count generalizing initial with
  | zero => rfl
  | succ count ih =>
      exact aligned_bind view result result _ _ (related initial) _ _ ih

end Zkc.Compiler.Role.Simulation
