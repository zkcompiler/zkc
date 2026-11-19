module

public import Zkc.Formal.Written.TableVerifier
public import Zkc.Frontend.Written.Root
public import Zkc.Frontend.Written.Charge

@[expose] public section
namespace Zkc.Formal.Written.TableVerifier
open Core Frontend Frontend.Emit

abbrev compiled (source : Frontend.Written.AdmittedRoot) := source.evidence.admitted.program

/-- Recover the concrete source kind from the nominal type of the admitted registration. -/
def registeredKind (source : Frontend.Written.AdmittedRoot) (handle : source.emission.bindings.vocabulary.Ty) :
    Option InstanceId := do
  let .nominal (.inr (.type (.nominal "oracle.handle") (.cons (.moduleRef kind) .nil))) := handle | none
  let entry ← source.state.table.entries[kind]?
  guard (Static.qualifiedName source.state.program entry.key.declaration == "zkc::oracle::table")
  let #[.type row,.natural 1024] := entry.key.arguments | none
  guard (StandardNames.typeOf? row == some (.nominal (.field .koalaBear)))
  return kind

/-- Resolve the emitted addresses of the source registration and immediate query. -/
def tableSites (source : Frontend.Written.AdmittedRoot) : Option (List (List (Key × Nat) × Key)) := do
  let some (.protocol code) := source.state.results.body? source.id | none
  let addresses ← SiteAddresses.forProtocol (compiled source) ⟨source.id⟩
  [("codeword","value"),("rows","rows"),("rows","opening")].mapM fun (name,part) => do
    let #[site] := code.sites.filter (fun s => s.name == some name && s.part == part) | none
    addresses.resolve site

structure Certificate (source : Frontend.Written.AdmittedRoot) where
  domain : source.emission.bindings.vocabulary.Ty
  handle : source.emission.bindings.vocabulary.Ty
  kind : InstanceId
  registration : registeredKind source handle = some kind
  shape : Shape source.emission.bindings.vocabulary
  root : Member (compiled source).headers.protocols ⟨⟨source.id⟩,2,ports domain,[],shape⟩
  entry : ProtocolEntry (compiled source).defs root
  calls : Calls entry.earlier domain
  draw : Frontend.Written.DeclaredDraw
  declared : Frontend.Written.declaredDraw source.state ⟨source.id⟩ "positions" = .ok draw
  amount : draw.ceiling = (3/4 : Rat)^40
  charge : Frontend.Written.DrawCharge
  located : Frontend.Written.drawCharge source.state (compiled source) ⟨source.id⟩ "positions" = .ok charge
  address : charge.draws = [([],⟨2⟩)]
  sites : tableSites source = some [([],⟨1⟩),([],⟨4⟩),([],⟨6⟩)]
  meaning : ∀ M path args, roleMeaning M (compiled source) root 1 path args =
    (project 1 (body calls handle)).denote
      (roleSem M 1 (Defs.fnTable M entry.definitions) (Defs.rTable M entry.definitions))
      path (Env.empty.extend (names domain) args)

def namedFunction (source : Frontend.Written.AdmittedRoot) (name : String) :
    Option Key := do
  let [d] := source.emission.named.definitions.filter (fun d =>
    (source.state.table.entries[d.key.number]?).any fun e =>
      Static.qualifiedName source.state.program e.key.declaration == name) | none
  return d.key

def functionMember {V : Core.Vocabulary} (hs : Headers V) (wanted : FnHeader V) :
    Option (Member hs.fns wanted) := do
  let [⟨h,ref⟩] := Member.withKey FnHeader.key wanted.key hs.fns | none
  if e : h = wanted then return e ▸ ref else none

/-- Issue only after the declared ceiling, realized draw address and entire admitted
protocol body agree with the written table verifier. -/
def certify (source : Frontend.Written.AdmittedRoot) : Option (Certificate source) := do
  let p := compiled source
  let k : Key := ⟨source.id⟩
  let some (.protocol _ _ [_,d] _ (.mk _ (_ :: .op _ _ (.event (.given (.request _) ..) h) _ :: _) _)) :=
    source.emission.named.definitions.find? (fun defn => defn.key == k) | none
  match recognized : registeredKind source h with
  | none => none
  | some kind =>
    let domain := d.ty
    let ⟨shape,ref⟩ ← ProtocolEntry.locatePorts p.headers k 2 (ports domain) []
    let entry := p.defs.protocolEntry p.distinct ref
    let tab ← namedFunction source "spot_check::tabulate"
    let pt ← namedFunction source "zkc::coset::at"
    let poly ← namedFunction source "zkc::polynomial::evaluate"
    let calls : Calls entry.earlier domain := ⟨tab,pt,poly,
      ← functionMember _ _, ← functionMember _ _, ← functionMember _ _⟩
    if armed : (body calls h).armed = true then
      let target : ProtocolEntry.Body entry.earlier ⟨k,2,ports domain,[],shape⟩ :=
        ⟨names domain,body calls h,armed⟩
      let ⟨meaning⟩ ← entry.recognize 1 target (fun run => ∀ M path args,
        run M path args = target.meaning entry.definitions 1 M path args) (fun _ _ _ => rfl)
      match declared : Frontend.Written.declaredDraw source.state k "positions" with
      | .error _ => none
      | .ok draw =>
        match located : Frontend.Written.drawCharge source.state p k "positions" with
        | .error _ => none
        | .ok charge =>
          if amount : draw.ceiling = (3/4 : Rat)^40 then
            if address : charge.draws = [([],⟨2⟩)] then
              if sites : tableSites source = some [([],⟨1⟩),([],⟨4⟩),([],⟨6⟩)] then
                return ⟨domain,h,kind,recognized,shape,ref,entry,calls,draw,declared,amount,charge,located,address,sites,meaning⟩
              else none
            else none
          else none
    else none

end Zkc.Formal.Written.TableVerifier
