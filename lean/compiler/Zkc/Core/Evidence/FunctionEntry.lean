module

public import Zkc.Core.Evidence.FunctionReadback

@[expose] public section
namespace Zkc.Core
variable {V : Vocabulary}

/-- A function body together with the actual table used by its calls. -/
structure FunctionEntry {hs : Headers V} (defs : Defs V hs) {hdr : FnHeader V} (ref : Member hs.fns hdr) where
  earlier : Headers V
  definitions : Defs V earlier
  distinct : (earlier.fns.map (·.key)).Nodup
  inputs : Names hdr.ins
  body : Fn V earlier.fns hdr inputs
  armed : body.armed = true
  meaning : ∀ M args, Defs.fnTable M defs _ ref args =
    body.denote (localSem M _ (Defs.fnTable M definitions)) [] (Env.empty.extend inputs args)

def Defs.functionEntry : {hs : Headers V} → (defs : Defs V hs) → (hs.fns.map (·.key)).Nodup →
    {hdr : FnHeader V} → (ref : Member hs.fns hdr) → FunctionEntry defs ref
  | _, .nil, _, _, ref => nomatch ref
  | _, .protocol _ _ _ _ ds, unique, _, ref =>
    let entry := ds.functionEntry unique ref
    ⟨entry.earlier,entry.definitions,entry.distinct,entry.inputs,entry.body,entry.armed,entry.meaning⟩
  | _, .fn _ inputs body ok ds _, unique, _, .head =>
    ⟨_,ds,(List.nodup_cons.mp unique).2,inputs,body,ok.armed,fun _ _ => rfl⟩
  | _, .fn _ _ _ _ ds _, unique, _, .tail ref =>
    let entry := ds.functionEntry (List.nodup_cons.mp unique).2 ref
    ⟨entry.earlier,entry.definitions,entry.distinct,entry.inputs,entry.body,entry.armed,entry.meaning⟩

namespace FunctionEntry
variable {hs : Headers V} {ds : Defs V hs} {hdr : FnHeader V} {ref : Member hs.fns hdr}

def resolve (headers : List (FnHeader V)) (expected : FnHeader V) : Option (Member headers expected) := do
  let [⟨actual,ref⟩] := Member.withKey FnHeader.key expected.key headers | none
  if same : actual = expected then return same ▸ ref else none

structure AtInputs (entry : FunctionEntry ds ref) (ns : Names hdr.ins) where
  body : Fn V entry.earlier.fns hdr ns
  meaning : ∀ M args, Defs.fnTable M ds _ ref args =
    body.denote (localSem M _ (Defs.fnTable M entry.definitions)) [] (Env.empty.extend ns args)

def atInputs (entry : FunctionEntry ds ref) (ns : Names hdr.ins) : Option (entry.AtInputs ns) :=
  if agrees : entry.inputs.toList = ns.toList then
    have same : entry.inputs = ns := by
      have read := Names.ofList_toList entry.inputs
      rw [agrees,Names.ofList_toList] at read
      exact (Option.some.inj read).symm
    some (same ▸ (⟨entry.body,entry.meaning⟩ : entry.AtInputs entry.inputs))
  else none

/-- Reuse the meaning of a canonical body proved against this function's own predecessors. -/
def recognize (entry : FunctionEntry ds ref) (expected : FunctionReadback.ArmedBody entry.earlier.fns hdr)
    (law : FunctionMeaning hdr → Prop)
    (holds : law (expected.meaning fun M => Defs.fnTable M entry.definitions)) :
    Option (PLift (law fun M => Defs.fnTable M ds _ ref)) := do
  let actual : FunctionReadback.ArmedBody entry.earlier.fns hdr := ⟨entry.inputs,entry.body,entry.armed⟩
  if erased : eraseFn actual.1 actual.2.1 = eraseFn expected.1 expected.2.1 then
    have same := FunctionReadback.ArmedBody.eq_of_erase_eq entry.distinct actual expected erased
    have meaning : (fun M => Defs.fnTable M ds _ ref) = actual.meaning (fun M => Defs.fnTable M entry.definitions) :=
      funext fun M => funext fun args => entry.meaning M args
    return ⟨by rwa [meaning,same]⟩
  else none

end FunctionEntry
end Zkc.Core
