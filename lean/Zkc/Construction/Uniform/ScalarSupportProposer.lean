module

public import Zkc.Construction.Uniform.ScalarFragment
public meta import Lean.Elab.Tactic

@[expose] public meta section

/-! A compiled proposer of structural scalar support. Every successful branch
constructs a kernel-checked rule; an unsupported goal remains a proof-search
failure, never a theorem of semantic impossibility. -/
namespace Zkc.Construction.Uniform.ScalarSupport
open Lean Elab Tactic

syntax "derive_scalar_support" : tactic

elab_rules : tactic
  | `(tactic| derive_scalar_support) => do
    evalTactic (← `(tactic|
      first
      | (apply ScalarFragment.participant_supported; decide +kernel)
      | exact Supported.done _
      | exact Supported.halt _
      | (apply Supported.enter
         · first | rfl | assumption
         · derive_scalar_support)
      | (apply Supported.leave; derive_scalar_support)
      | (apply Supported.action
         · first | exact Message.boolean | exact Message.field _ | exact Message.group _ | trivial
         · intro reply; derive_scalar_support)
      | (split <;> derive_scalar_support)))

end Zkc.Construction.Uniform.ScalarSupport
