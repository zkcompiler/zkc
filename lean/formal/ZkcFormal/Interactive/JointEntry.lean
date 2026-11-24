module

public import Zkc.Core.Evidence.ProtocolReadback

@[expose] public section
namespace ZkcFormal.Interactive.JointEntry
open Zkc.Core
variable {V : Vocabulary} {hs : Headers V} {h : ProtocolHeader V}

/-- A checked joint protocol body at its actual table reference, forgetting only the run record. -/
structure Entry (ds : Defs V hs) (ref : Member hs.protocols h) where
  earlier : Headers V
  definitions : Defs V earlier
  distinct : earlier.keys.Nodup
  candidate : ProtocolEntry.Body earlier h
  meaning : ∀ M path args, (Defs.gTable M ds _ ref path args).map Prod.fst =
    candidate.2.1.denote (protocolSem M (Defs.fnTable M definitions) (Defs.gTable M definitions))
      path (Env.empty.extend candidate.1 args)

def locate : {hs : Headers V} → (ds : Defs V hs) → hs.keys.Nodup →
    {h : ProtocolHeader V} → (ref : Member hs.protocols h) → Entry ds ref
  | _, .nil, _, _, ref => nomatch ref
  | _, .fn _ _ _ _ rest _, distinct, _, ref =>
    let e := locate rest (List.nodup_cons.mp distinct).2 ref
    ⟨e.earlier,e.definitions,e.distinct,e.candidate,e.meaning⟩
  | _, .protocol _ inputs body ok rest, distinct, _, .head =>
    ⟨_,rest,Headers.earlierProtocolKeys distinct,⟨inputs,body,ok.armed⟩,by
      intro M path args
      change ((Term.observe M _ _ body path (Env.empty.extend inputs args)).map
        (fun out => (out.1, cast (congrArg (fun s : Shape V => s.fields.Val M) ok.shaped.symm) out.2))).map Prod.fst = _
      rw [Process.map_map]
      exact Term.observe_fst M _ _ body path _⟩
  | _, .protocol _ _ _ _ rest, distinct, _, .tail ref =>
    let e := locate rest (Headers.earlierProtocolKeys distinct) ref
    ⟨e.earlier,e.definitions,e.distinct,e.candidate,e.meaning⟩

abbrev Returns {S : Sig} {H A : Type} (p : Process S H A) (post : A → Prop) :=
  p.Every (fun _ _ => True) post (fun _ => False)

theorem returns_map {S : Sig} {H A B : Type} (p : Process S H A) (f : A → B) (post : B → Prop) :
    Returns (p.map f) post ↔ Returns p (fun a => post (f a)) := by
  rw [Process.map_eq_bind]
  apply Process.every_bind

theorem returns_mapG {A : Type} (M : Model V) (ρ : Role → Role) (p : Protocol M A) (post : A → Prop)
    (good : Returns p post) : Returns (mapG M ρ p) post := by
  induction p with
  | done | halt => exact good
  | call op k ih =>
    cases op <;> exact fun r _ => ih r (good r trivial)

end ZkcFormal.Interactive.JointEntry
