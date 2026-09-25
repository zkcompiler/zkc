import Examples.TableProtocol.Language
import Zkc.Compiler.RegionFolding
import Mathlib.Tactic.Ring

/-! The installed table fold: interpolation at identical SSA endpoints is
constant. Operand identity is checked afresh; no sampled values or cached facts
authorize replacing distinct variables, partial table operations or calls. -/

set_option autoImplicit false
namespace TableProtocol.Optimization
open Zkc.Source Zkc.Compiler

def replacement {Γ : List Ty} : (op : Protocol.Operation) →
    Operands Γ (Protocol.arguments op) → Option (Var Γ (Protocol.result op))
  | .linear => fun args => match args with
    | .cons a (.cons b (.cons _ .nil)) =>
      if a.index = b.index then some a else none
  | _ => fun _ => none

theorem replacement_correct {Γ : List Ty} (op : Protocol.Operation)
    (args : Operands Γ (Protocol.arguments op)) (value : Var Γ (Protocol.result op))
    (selected : replacement op args = some value) (env : Environment Value Γ) :
    Protocol.meaning.operation op (Operands.eval env args) = .done (env value) := by
  cases op <;> try { simp [replacement] at selected }
  cases args with | cons a rest =>
    cases rest with | cons b rest =>
      cases rest with | cons r rest =>
        cases rest
        simp only [replacement] at selected
        split at selected
        next same =>
          have decoded := congrArg (Var.decode Γ (.scalar .seven)) same
          simp only [Var.decode_index] at decoded
          have equal := Option.some.inj decoded
          have chosen := Option.some.inj selected
          subst b
          subst value
          simp only [Operands.eval, Protocol.meaning]
          congr 1
          change (1 - (env r : Field .seven)) * env a + env r * env a = env a
          ring
        next => contradiction

def folding : OperationFolding Protocol.meaning := ⟨@replacement, @replacement_correct⟩

end TableProtocol.Optimization
