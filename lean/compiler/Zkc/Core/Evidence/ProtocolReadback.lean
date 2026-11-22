module

public import Zkc.Core.Program.EraseProgram
public import Zkc.Core.Meaning.Program

@[expose] public section
namespace Zkc.Core
variable {V : Vocabulary}

/-- Evidence about a referenced protocol uses precisely the preceding tables visible to
that definition. Its projected body denotes the operational meaning at the reference. -/
structure ProtocolEntry {hs : Headers V} (defs : Defs V hs) {hdr : ProtocolHeader V}
    (ref : Member hs.protocols hdr) where
  earlier : Headers V
  definitions : Defs V earlier
  distinct : earlier.keys.Nodup
  inputs : Names hdr.ins
  body : Prot V earlier hdr inputs
  checked : ProtocolConditions hdr body
  meaning : ∀ M r path args, Defs.rTable M defs _ ref r path args =
    (project r body).denote (roleSem M r (Defs.fnTable M definitions) (Defs.rTable M definitions))
      path (Env.empty.extend inputs args)

theorem Headers.earlierProtocolKeys {hs : Headers V} {h : ProtocolHeader V}
    (after : (Headers.mk hs.fns (h :: hs.protocols)).keys.Nodup) : hs.keys.Nodup := by
  obtain ⟨fns,protocols,apart⟩ := List.nodup_append.mp after
  exact List.nodup_append.mpr ⟨fns,(List.nodup_cons.mp protocols).2,
    fun x hx y hy => apart x hx y (List.mem_cons_of_mem _ hy)⟩

def Defs.protocolEntry : {hs : Headers V} → (defs : Defs V hs) → hs.keys.Nodup →
    {h : ProtocolHeader V} → (ref : Member hs.protocols h) → ProtocolEntry defs ref
  | _, .nil, _, _, ref => nomatch ref
  | _, .fn _ _ _ _ ds _, distinct, _, ref =>
    let entry := ds.protocolEntry (List.nodup_cons.mp distinct).2 ref
    ⟨entry.earlier,entry.definitions,entry.distinct,entry.inputs,entry.body,entry.checked,entry.meaning⟩
  | _, .protocol _ inputs body ok ds, distinct, _, .head =>
    ⟨_,ds,Headers.earlierProtocolKeys distinct,inputs,body,ok,fun _ _ _ _ => rfl⟩
  | _, .protocol _ _ _ _ ds, distinct, _, .tail ref =>
    let entry := ds.protocolEntry (Headers.earlierProtocolKeys distinct) ref
    ⟨entry.earlier,entry.definitions,entry.distinct,entry.inputs,entry.body,entry.checked,entry.meaning⟩

/-- **The program of a role is the denotation of the projection of its protocol's body, in
whatever table the protocol is read**: over the tables of the definitions before the protocol,
as its entry in the program's table has them. -/
theorem roleMeaning_entry (M : Model V) (p : Typed V) {hdr : ProtocolHeader V}
    (x : Member p.headers.protocols hdr) (r : Role) (path : List Frame)
    (ins : HList (RV M r) hdr.ins) :
    roleMeaning M p x r path ins =
      (project r (p.defs.protocolEntry p.distinct x).body).denote
        (roleSem M r (Defs.fnTable M (p.defs.protocolEntry p.distinct x).definitions)
          (Defs.rTable M (p.defs.protocolEntry p.distinct x).definitions))
        path (Env.empty.extend (p.defs.protocolEntry p.distinct x).inputs ins) := by
  unfold roleMeaning
  exact (p.defs.protocolEntry p.distinct x).meaning M r path ins

namespace ProtocolEntry

/-- Resolve the call identity and executable ports while retaining the checked protocol shape. -/
def locatePorts (hs : Headers V) (key : Key) (roles : Nat) (ins outs : List (LTy V)) :
    Option ((shape : Shape V) × Member hs.protocols ⟨key,roles,ins,outs,shape⟩) := do
  let [⟨h,ref⟩] := Member.withKey ProtocolHeader.key key hs.protocols | none
  if aligned : h.key = key ∧ h.roles = roles ∧ h.ins = ins ∧ h.outs = outs then
    have same : h = ⟨key,roles,ins,outs,h.shape⟩ := by
      obtain ⟨k,rs,args,results,shape⟩ := h
      obtain ⟨rfl,rfl,rfl,rfl⟩ := aligned
      rfl
    return ⟨h.shape,same ▸ ref⟩
  else none

/-- The same table entry expressed at specified source binder names. -/
structure AtInputs {h : ProtocolHeader V} {hs : Headers V} {ds : Defs V hs} {ref : Member hs.protocols h}
    (entry : ProtocolEntry ds ref) (ns : Names h.ins) where
  body : Prot V entry.earlier h ns
  armed : body.armed = true
  meaning : ∀ M r path args, Defs.rTable M ds _ ref r path args =
    (project r body).denote (roleSem M r (Defs.fnTable M entry.definitions) (Defs.rTable M entry.definitions))
      path (Env.empty.extend ns args)

def atInputs {h : ProtocolHeader V} {hs : Headers V} {ds : Defs V hs} {ref : Member hs.protocols h}
    (entry : ProtocolEntry ds ref) (ns : Names h.ins) : Option (entry.AtInputs ns) :=
  if agrees : entry.inputs.toList = ns.toList then
    have same : entry.inputs = ns := by
      have read := Names.ofList_toList entry.inputs
      rw [agrees, Names.ofList_toList] at read
      exact (Option.some.inj read).symm
    some (same ▸ (⟨entry.body,entry.checked.armed,entry.meaning⟩ : entry.AtInputs entry.inputs))
  else none

abbrev Body (hs : Headers V) (h : ProtocolHeader V) :=
  (inputs : Names h.ins) × (body : Prot V hs h inputs) ×' body.armed = true

/-- Equality of erased regions at the same ports recovers both the actual typed body and
its input names. The stored shape stays available through the entry's formation evidence. -/
theorem eq_of_erase_eq {hs : Headers V} {hdr : ProtocolHeader V} (distinct : hs.keys.Nodup)
    (a b : Body hs hdr) (same : eraseProtocol a.1 a.2.1 = eraseProtocol b.1 b.2.1) : a = b := by
  have read (x : Body hs hdr) :
      elabRegion (protocolRules hs) hdr.key Ctx.empty [] hdr.key hdr.ins (eraseProtocol x.1 x.2.1) =
        .ok ⟨hdr.outs, x.1, x.2.1⟩ :=
    elabRegion_erase _ _ _ _ _ _ _ (elabBody_erase _ (protocolRules_lawful distinct) _ _ x.2.2 _ _)
  have left := read a
  rw [same, read b] at left
  obtain ⟨ia,ba,ok⟩ := a
  obtain ⟨ib,bb,ok'⟩ := b
  cases Except.ok.inj left
  rfl

abbrev RoleMeaning (hdr : ProtocolHeader V) (r : Role) :=
  (M : Model V) → List Frame → HList (RV M r) hdr.ins → Program M (HList (RV M r) hdr.outs)

def Body.meaning {hs : Headers V} {hdr : ProtocolHeader V} (candidate : Body hs hdr)
    (defs : Defs V hs) (r : Role) : RoleMeaning hdr r :=
  fun M path args => (project r candidate.2.1).denote
    (roleSem M r (Defs.fnTable M defs) (Defs.rTable M defs)) path (Env.empty.extend candidate.1 args)

/-- The property may depend on the meanings of earlier function and protocol entries.
A successful decision proves it of the role program actually returned by the program table. -/
def recognize {hs : Headers V} {defs : Defs V hs} {hdr : ProtocolHeader V}
    {ref : Member hs.protocols hdr} (entry : ProtocolEntry defs ref) (r : Role)
    (candidate : Body entry.earlier hdr) (law : RoleMeaning hdr r → Prop)
    (holds : law (candidate.meaning entry.definitions r)) :
    Option (PLift (law (fun M => Defs.rTable M defs _ ref r))) := do
  let actual : Body entry.earlier hdr := ⟨entry.inputs,entry.body,entry.checked.armed⟩
  if same : eraseProtocol actual.1 actual.2.1 = eraseProtocol candidate.1 candidate.2.1 then
    return ⟨by
      have equal := eq_of_erase_eq entry.distinct actual candidate same
      have meaning : (fun M => Defs.rTable M defs _ ref r) = actual.meaning entry.definitions r :=
        funext fun M => funext fun path => funext fun args => entry.meaning M r path args
      rwa [meaning, equal]⟩
  else none

end ProtocolEntry
end Zkc.Core
