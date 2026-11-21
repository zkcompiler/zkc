module

public import Zkc.Core.Program.EraseProgram
public import Zkc.Core.Meaning.Program

@[expose] public section
namespace Zkc.Core

deriving instance DecidableEq for FnHeader

/-- The meaning of an entry at this header, across interpretations of the vocabulary. -/
abbrev FunctionMeaning {V : Vocabulary} (header : FnHeader V) :=
  (M : Model V) → HList M.Val header.ins → Local (HList M.Val header.outs)

/-- Recognize two operations with the same typed interface in one installed function table. -/
def LocalOp.same? {V : Vocabulary} {fns : List (FnHeader V)} {ins outs : List V.Ty}
    (a b : LocalOp V fns ins outs) (unique : (fns.map (·.key)).Nodup) : Option (PLift (a = b)) :=
  if h : a.print = b.print then some ⟨eq_of_heq (Sigma.mk.inj (LocalOp.print_injective unique a b h)).2⟩ else none

/-- A proved body that may be linked after any table of earlier functions. The law can
restrict the models it covers, and can refer to the values of the inputs and results. -/
structure FunctionReadback {V : Vocabulary} (header : FnHeader V) (law : FunctionMeaning header → Prop) where
  inputs : Names header.ins
  body : (earlier : List (FnHeader V)) → Fn V earlier header inputs
  armed : ∀ earlier, (body earlier).armed = true
  holds : ∀ earlier (tables : (M : Model V) → FnTable M earlier),
    law (fun M args => (body earlier).denote (localSem M _ (tables M)) [] (Env.empty.extend inputs args))

namespace FunctionReadback
variable {V : Vocabulary} {header : FnHeader V} {law : FunctionMeaning header → Prop}

/-- A typed body whose case arms can be recovered by the Core elaborator. -/
abbrev ArmedBody (earlier : List (FnHeader V)) (h : FnHeader V) :=
  (inputs : Names h.ins) × (body : Fn V earlier h inputs) ×' body.armed = true

def ArmedBody.meaning {fns : List (FnHeader V)} (a : ArmedBody fns header)
    (tables : (M : Model V) → FnTable M fns) : FunctionMeaning header :=
  fun M args => a.2.1.denote (localSem M _ (tables M)) [] (Env.empty.extend a.1 args)

theorem ArmedBody.eq_of_erase_eq {earlier : List (FnHeader V)} (distinct : (earlier.map (·.key)).Nodup)
    (a b : ArmedBody earlier header) (same : eraseFn a.1 a.2.1 = eraseFn b.1 b.2.1) : a = b := by
  have read (x : ArmedBody earlier header) :
      elabRegion (localRules earlier) header.key Ctx.empty [] header.key header.ins (eraseFn x.1 x.2.1) =
        .ok ⟨header.outs, x.1, x.2.1⟩ :=
    elabRegion_erase (localRules earlier) _ _ _ _ _ _
      (elabBody_erase _ (localRules_lawful distinct) _ _ x.2.2 _ _)
  have left := read a
  rw [same, read b] at left
  obtain ⟨ia, ba, ok⟩ := a
  obtain ⟨ib, bb, ok'⟩ := b
  have eq := Except.ok.inj left
  cases eq
  rfl

/-- Find the actual entry of a linked table and transport its law. A successful result
carries the member used by calls. Unrelated functions and protocols may precede or follow
that entry. Comparison includes the full header, input names, instructions, and exit. -/
def locate (proof : FunctionReadback header law) : {hs : Headers V} → (defs : Defs V hs) →
    (hs.fns.map (·.key)).Nodup →
    Option {ref : Member hs.fns header // law (fun M => Defs.fnTable M defs _ ref)}
  | _, .nil, _ => none
  | _, .protocol _ _ _ _ rest, distinct => proof.locate rest distinct
  | _, .fn (hs := hs) h inputs body checked rest _, distinct =>
    let before := (List.nodup_cons.mp distinct).2
    if equal : h = header then by
      subst h
      exact do
        let actual : ArmedBody hs.fns header := ⟨inputs, body, checked.armed⟩
        let expected : ArmedBody hs.fns header := ⟨proof.inputs, proof.body _, proof.armed _⟩
        if same : eraseFn actual.1 actual.2.1 = eraseFn expected.1 expected.2.1 then
          have agree := ArmedBody.eq_of_erase_eq before actual expected same
          have established := proof.holds hs.fns (fun M => Defs.fnTable M rest)
          have sameLaw := congrArg (fun a => law (ArmedBody.meaning a (fun M => Defs.fnTable M rest))) agree
          return ⟨.head, sameLaw.mpr established⟩
        else none
    else do
      let ⟨ref, cert⟩ ← proof.locate rest before
      return ⟨.tail ref, cert⟩

/-- Reuse a body certificate at the operation in a calling instruction. Matching the
typed call also identifies the actual definition table used by that operation. -/
def atOperation {hs : Headers V} (proof : FunctionReadback header law) (defs : Defs V hs)
    (unique : (hs.fns.map (·.key)).Nodup) (op : LocalOp V hs.fns header.ins header.outs) :
    Option (PLift (law (fun M => localOp M (Defs.fnTable M defs) op))) := do
  let ⟨actual,holds⟩ ← proof.locate defs unique
  let ⟨equal⟩ ← op.same? (.call actual) unique
  return ⟨equal.symm ▸ holds⟩

end FunctionReadback
end Zkc.Core
