import Zkc.Source.Mathematical.ProtocolAdmission

/-! Exact syntactic invocation sites in intrinsic and resolved protocols.
Loops contribute their body once, independently of their iteration count.
-/

set_option autoImplicit false
namespace Zkc.Source.Mathematical.Protocol

structure Invocation where
  site : Nat
  callee : Nat
  capabilities : List Nat
  deriving DecidableEq, Repr

variable {Role : Type} [DecidableEq Role] {vocabulary : Vocabulary}

def Raw.invocations : Raw Role vocabulary → List Invocation
  | .ret _ | .stop .. => []
  | .pure _ _ next | .local _ _ _ _ _ next | .query _ _ _ _ next |
    .guard _ _ _ next | .message _ _ _ _ _ next => next.invocations
  | .invoke site callee capabilities _ next => ⟨site, callee, capabilities⟩ :: next.invocations
  | .repeat _ _ _ _ _ body next => body.invocations ++ next.invocations

def Program.invocations {parties capabilities scope Γ results start finish} :
    Program (Role := Role) parties vocabulary capabilities scope Γ results start finish → List Invocation
  | .ret _ | .stop .. => []
  | .pure _ _ next | .local _ _ _ _ _ _ next | .query _ _ _ _ _ _ next |
    .guard _ _ _ next | .message _ _ _ _ _ _ _ next => next.invocations
  | .invoke callee _ bindings _ next => ⟨start, callee.index, bindings.indices⟩ :: next.invocations
  | .repeat _ _ _ body next => body.invocations ++ next.invocations

theorem Program.erase_invocations {parties capabilities scope Γ results start finish}
    (program : Program (Role := Role) parties vocabulary capabilities scope Γ results start finish) :
    program.erase.invocations = program.invocations := by
  induction program <;> simp_all [Program.erase, Raw.invocations, Program.invocations]

private theorem variable_bound {α : Type} {values : List α} {value : α}
    (reference : Var values value) : reference.index < values.length := by
  induction reference with
  | here => simp [Var.index]
  | there reference ih => simpa [Var.index] using ih

theorem Program.invocations_scope {parties capabilities scope Γ results start finish}
    (program : Program (Role := Role) parties vocabulary capabilities scope Γ results start finish) :
    ∀ call ∈ program.invocations, call.callee < scope.length := by
  induction program <;> simp_all [Program.invocations]
  · exact variable_bound _
  · intro call member
    rcases member with member | member <;> solve_by_elim

theorem Program.invocation_sites_sublist {parties capabilities scope Γ results start finish}
    (program : Program (Role := Role) parties vocabulary capabilities scope Γ results start finish) :
    (program.invocations.map (·.site)).Sublist program.sites := by
  induction program <;> simp only [Program.invocations, Program.sites, List.map_nil, List.map_cons, List.map_append]
  all_goals first
    | exact .slnil
    | assumption
    | exact .cons _ (by assumption)
    | exact .cons_cons _ (by assumption)
    | exact List.nil_sublist _
    | skip
  exact .cons _ (List.Sublist.append (by assumption) (by assumption))

theorem Program.invocation_sites_unique {parties capabilities scope Γ results start finish}
    (program : Program (Role := Role) parties vocabulary capabilities scope Γ results start finish) :
    (program.invocations.map (·.site)).Nodup := by
  apply List.Nodup.sublist program.invocation_sites_sublist
  rw [program.sites_dense]
  exact List.nodup_range'

end Zkc.Source.Mathematical.Protocol
