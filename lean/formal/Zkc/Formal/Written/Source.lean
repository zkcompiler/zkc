module

public import Zkc.Core.Admission.Theorems
public import Zkc.Frontend.Emit.Reports
public import Zkc.Formal.Written.Execution
public import Zkc.Formal.Written.Extraction

@[expose] public section
set_option autoImplicit false

namespace Zkc.Formal.Written
open Core

def singletonProgram {V : Vocabulary} (hdr : ProtocolHeader V) (ns : Names hdr.ins)
    (body : Prot V ⟨[], []⟩ hdr ns) (ok : ProtocolConditions hdr body) : Typed V :=
  ⟨⟨[], [hdr]⟩, .protocol hdr ns body ok .nil, by simp [Headers.keys]⟩

macro "protocol_conditions " t:term:max ns:term:max n:num : tactic => `(tactic|
  exact {
    within := @of_decide_eq_true _ (decideWithin (List.range $n) $t) (by decide +kernel)
    located := by decide +kernel
    enclosed := @of_decide_eq_true _ (decideEnclosed $t) (by decide +kernel)
    distinct := (Term.repeatedAddress_eq_none $t).mp (by decide +kernel)
    shaped := rfl
    linear := by change Term.misuse (fun a : LTy _ => Ty.isLinear _ a.ty) $ns $t = none; decide +kernel
    armed := by decide +kernel
    once := (Term.rebound_eq_none (Names.toList $ns) $t).mp (by decide +kernel) })

abbrev Standard := (Zkc.Frontend.Emit.Bindings.mk [] (by decide)).vocabulary
abbrev pointTy : Standard.Ty := .nominal (.inl (.group .g1))
abbrev scalarTy : Standard.Ty := .nominal (.inl (.field .bls12381Fr))
abbrev challengeLaw : Standard.LawKey := .uniform (.nominal (.field .bls12381Fr))

/-- Interpretation of the verifier's three pure standard rows at their actual signatures. -/
structure GroupRows (M : Model Standard) (ops : Operations (M.Val scalarTy) (M.Val pointTy))
    [DecidableEq (M.Val pointTy)] : Prop where
  scale : ∀ p k, M.apply (.inl (.group .scale (.group .g1))) _ rfl (.cons p (.cons k .nil)) =
    some (.cons (ops.scale p k) .nil)
  add : ∀ p q, M.apply (.inl (.group .add (.group .g1))) _ rfl (.cons p (.cons q .nil)) =
    some (.cons (ops.add p q) .nil)
  equal : ∀ (p q : M.Val pointTy), M.apply (.inl (.group .equal (.group .g1))) _ rfl (.cons p (.cons q .nil)) =
    some (.cons (decide (p = q)) .nil)

/-- All fields of each observed operation are retained, including peers, law, type and occurrence. -/
def forkTrace (M : Model Standard) (path : List Frame) (prover : Role)
    (commitmentSite challengeSite responseSite : Key)
    (a : M.Val pointTy) (b : Branch (M.Val scalarTy)) : List ((op : ROp M) × (RSig M).Reply op) :=
  [⟨.get .message prover ⟨path, commitmentSite⟩ pointTy, a⟩,
   ⟨.own (.coin challengeLaw) [prover] ⟨path, challengeSite⟩ [] .nil scalarTy, b.challenge⟩,
   ⟨.get .message prover ⟨path, responseSite⟩ scalarTy, b.suffix⟩]

end Zkc.Formal.Written
