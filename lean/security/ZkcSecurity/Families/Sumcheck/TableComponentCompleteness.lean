module

public import ZkcSecurity.Families.Sumcheck.TableComponentRoots

@[expose] public section

/-! Successful root execution of the same table presentation used by residual
soundness. This is an intermediate handler theorem; actual compiled-pair
completeness additionally needs the fixed exported producer and shared ROM.
-/

set_option autoImplicit false
namespace ZkcSecurity.Families.Sumcheck.TableComponent

variable {F : Type} [Field F] [DecidableEq F]
  {I : PIR.Signature} {Context : Type} {State : Nat → Type}
  {program : Program I Context State (Message.endpoints F)} {H O : Type}

/-- Successful completion includes every actual handler observation and the
poststate required by a later child call. Stopped processes cannot satisfy it. -/
theorem root_honest_run (layout : Layout program)
    (handler : PIR.Handler I H O)
    (invariant : Nat → {n : Nat} → Context → State n → H → Prop)
    (ready : Nat → {n : Nat} → Context → State (n + 1) → (F × F) → H → Prop)
    (execution : HonestRunLaws program handler invariant ready)
    (honestMessage : HonestMessageLaw layout.representation ready)
    (count : Nat) (context : Context) (s : State (0 + count)) (h : H)
    (trueClaim : program.claim s = (layout.entries s).sum)
    (initial : invariant count context s h) :
    ∃ result final events,
      (program.remaining (n := 0) count context s).run handler h =
        ⟨.returned result, final, events⟩ ∧
      (root layout count context s).run handler h = ⟨.returned true, final, events⟩ ∧
      invariant 0 context result final := by
  obtain ⟨result, final, events, returned, yes, retained⟩ := Consumers.honest_run
    layout.representation Message.endpoints_laws TableReference.laws handler invariant ready
    execution honestMessage count context s h ((layout.yes_iff s).mpr trueClaim) initial
  refine ⟨result, final, events, returned, ?_, retained⟩
  rw [root, PIR.run_bind, returned]
  have checked := (layout.yes_iff result).mp yes
  simp only [PIR.Execution.follow, terminal, checked, decide_true, PIR.Process.run,
    List.append_nil]

end ZkcSecurity.Families.Sumcheck.TableComponent
