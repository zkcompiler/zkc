module

public import Zkc.Core.Facts.Contracts.RoleOperations
public import Zkc.Core.Facts.Contracts.Typing

@[expose] public section

namespace Zkc.Core.BodyAnalysis
variable {V : Vocabulary}

/-- Resolve the located types of computations, absent values and changes of holder.
A participating computation uses the function reader on the underlying operand types. -/
def readRoleValue (hs : Headers V) (r : Role) (raw : RoleRaw V) (ins : List (LTy V)) :
    Option ((outs : List (LTy V)) × RoleOp V hs r ins outs) :=
  match raw with
  | .compute holders w =>
    if held : r ∈ holders then
      if inputs : ∀ a, a ∈ ins → r ∈ a.holders then
        match (localRules hs.fns).op w (ins.map LTy.ty) with
        | .ok ⟨_, op⟩ => some ⟨_, .compute holders op ins rfl held inputs⟩
        | .error _ => none
      else none
    else none
  | .absent outs =>
    match ins with
    | [] => if absent : ∀ a, a ∈ outs → r ∉ a.holders then some ⟨outs, .absent outs absent⟩ else none
    | _ => none
  | .keep holders =>
    match ins with
    | [⟨ty, previous⟩] =>
      if same : r ∈ previous ↔ r ∈ holders then some ⟨[⟨ty, holders⟩], .keep holders same⟩ else none
    | _ => none
  | .effect .. | .apply .. => none

def roleAssertionTypes (hs : Headers V) (r : Role) (allowed : RoleRaw V → Bool) :
    AssertionTypes (LTy V) (RoleRaw V) where
  signature op ins := if allowed op then (readRoleValue hs r op ins).map Sigma.fst else none
  boolean t := decide (t.ty = .bool ∧ r ∈ t.holders)

end Zkc.Core.BodyAnalysis
