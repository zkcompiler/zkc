module

public import ZkcFormal.Interactive.ReductionRound
public import Zkc.Core.Evidence.BlockReadback

@[expose] public section
namespace ZkcFormal.Interactive.Sumcheck.ReductionRound
open Zkc.Core
variable {V : Vocabulary}

def singleResult (fns : List (FnHeader V)) (raw : LocalRaw V) (ins : List V.Ty) :
    Option ((t : V.Ty) × LocalOp V fns ins [t]) := do
  let .ok ⟨[t],op⟩ := LocalOp.read fns raw ins | none
  return ⟨t,op⟩

def atType (fns : List (FnHeader V)) (raw : LocalRaw V) (ins : List V.Ty) (t : V.Ty) :
    Option (LocalOp V fns ins [t]) := do
  let ⟨out,op⟩ ← singleResult fns raw ins
  if same : out = t then return same ▸ op else none

structure Operations (V : Vocabulary) where
  message : LocalRaw V
  boundary : LocalRaw V
  bindState : LocalRaw V
  evaluate : LocalRaw V

def Operations.read (round : List (Instruction (ProtocolRaw V) (List Role))) : Option (Operations V) := do
  let read (i : Nat) : Option (LocalRaw V) := do
    let .op _ _ (.compute _ raw) _ ← round[i]? | none
    return raw
  return ⟨← read 0,← read 2,← read 6,← read 7⟩

def Operations.members (raw : Operations V) (hs : Headers V) (state t : V.Ty) :
    Option ((msg : V.Ty) × (residual : V.Ty) × Members hs t msg state residual) := do
  let ⟨msg,sendValue⟩ ← singleResult hs.fns raw.message [state]
  let ⟨residual,bindState⟩ ← singleResult hs.fns raw.bindState [state,t]
  return ⟨msg,residual,sendValue,bindState,← atType hs.fns raw.boundary [msg] t,← atType hs.fns raw.evaluate [msg,t] t⟩

abbrev caller (key : Key) (state point t : V.Ty) (outs : List (LTy V)) (shape : Shape V) : ProtocolHeader V :=
  ⟨key,2,inputs state point t,outs,shape⟩

structure Prefix {hs : Headers V} (ds : Defs V hs) {key state point t outs shape}
    (ref : Member hs.protocols (caller key state point t outs shape)) (events : Events t) where
  entry : ProtocolEntry ds ref
  atNames : entry.AtInputs names
  message : V.Ty
  residual : V.Ty
  members : Members entry.earlier t message state residual
  block : FirstBlock atNames.body (body members events point)

def recognize {hs : Headers V} (ds : Defs V hs) (distinct : hs.keys.Nodup)
    {key state point t outs shape} (ref : Member hs.protocols (caller key state point t outs shape))
    (events : Events t) : Option (Prefix ds ref events) := do
  let entry := ds.protocolEntry distinct ref
  let atNames ← entry.atInputs names
  let .mk _ steps _ := eraseProtocol (hdr := caller key state point t outs shape) (hs := entry.earlier) names atNames.body
  let .block _ _ _ (.mk _ round _) :: _ := steps | none
  let raw ← Operations.read round
  let ⟨msg,residual,members⟩ ← raw.members entry.earlier state t
  let block ← Term.firstBlock (protocolRules entry.earlier) (protocolRules_lawful entry.distinct)
    (body members events point) rfl atNames.body atNames.armed
  return ⟨entry,atNames,msg,residual,members,block⟩

structure AtCall (p : Zkc.Core.Typed V) (key : Key) {t : V.Ty} (events : Events t) where
  state : V.Ty
  point : V.Ty
  outs : List (LTy V)
  shape : Shape V
  ref : Member p.headers.protocols (caller key state point t outs shape)
  first : Prefix p.defs ref events

def locate (p : Zkc.Core.Typed V) (key : Key) {t : V.Ty} (events : Events t) : Option (AtCall p key events) := do
  let [⟨h,_⟩] := Member.withKey ProtocolHeader.key key p.headers.protocols | none
  let [a,b,_] := h.ins | none
  let ⟨shape,ref⟩ ← ProtocolEntry.locatePorts p.headers key 2 (inputs a.ty b.ty t) h.outs
  let first ← recognize p.defs p.distinct ref events
  return ⟨a.ty,b.ty,h.outs,shape,ref,first⟩

private theorem block_denote {hs : Headers V} {Γ : Ctx (LTy V)} {mid outs : List (LTy V)}
    {actual : Term (protocolDialect V hs) Γ outs} {inside : Term (protocolDialect V hs) Γ mid}
    (first : FirstBlock actual inside) (r : Role) (M : Model V) (fns : FnTable M hs.fns) (roles : RTable M hs.protocols)
    (path : List Frame) (env : Env (RV M r) Γ) :
    (project r actual).denote (roleSem M r fns roles) path env =
    ((project r inside).denote (roleSem M r fns roles) (path ++ [.iteration first.key first.index]) env).bind
      fun values => (project r first.rest).denote (roleSem M r fns roles) path (env.extend first.results values) := by
  obtain ⟨key,index,results,rest,rfl⟩ := first
  rfl

/-- The verified first round is followed by the original caller continuation at the
block's result names. The induction endpoint exposes the actual intermediate state. -/
theorem Prefix.process {hs : Headers V} {ds : Defs V hs} {key state point t outs shape}
    {ref : Member hs.protocols (caller key state point t outs shape)} {events : Events t}
    (cert : Prefix ds ref events) (M : Model V) [DecidableEq (M.Val t)]
    (boundary : M.Val cert.message → M.Val t) (evaluate : M.Val cert.message → M.Val t → M.Val t)
    (equalLaw : ScalarEquality.Law t events.equal events.equalType M)
    (boundaryLaw : ∀ m, localOp M (Defs.fnTable M cert.entry.definitions) cert.members.boundary (.cons m .nil) =
      .done (.cons (boundary m) .nil))
    (evaluateLaw : ∀ m r, localOp M (Defs.fnTable M cert.entry.definitions) cert.members.evaluate (.cons m (.cons r .nil)) =
      .done (.cons (evaluate m r) .nil))
    (path : List Frame) (hidden : RV M 1 ⟨state,[0]⟩) (initialPoint : M.Val point) (claim : M.Val t) :
    let args := HList.cons hidden (.cons (hide M 1 ⟨point,[0,1]⟩ initialPoint) (.cons (hide M 1 ⟨t,[0,1]⟩ claim) .nil))
    let inside := path ++ [.iteration cert.block.key cert.block.index]
    let sem := roleSem M 1 (Defs.fnTable M cert.entry.definitions) (Defs.rTable M cert.entry.definitions)
    Defs.rTable M ds _ ref 1 path args =
      ((verifierRound (receive M cert.message inside) (fun _ => challenge M events inside)
        (.declared .reject ⟨inside,⟨4⟩⟩) boundary evaluate claim).map (returned M cert.residual)).bind
        fun values => (project 1 cert.block.rest).denote sem path ((Env.empty.extend names args).extend cert.block.results values) := by
  dsimp only
  rw [cert.atNames.meaning,block_denote cert.block]
  rw [verifier cert.members events point M (Defs.fnTable M cert.entry.definitions)
    (Defs.rTable M cert.entry.definitions) boundary evaluate equalLaw boundaryLaw evaluateLaw _ hidden initialPoint claim]

#print axioms Prefix.process
end ZkcFormal.Interactive.Sumcheck.ReductionRound
