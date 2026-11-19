module

public import Zkc.Formal.Interactive.RoundLayout
public import Zkc.Core.Evidence.BlockReadback

@[expose] public section
namespace Zkc.Formal.Interactive.Sumcheck.ReductionRound
open Core
variable {V : Vocabulary}

abbrev caller (key : Key) (state point t : V.Ty) (outs : List (LTy V)) (shape : Shape V) : ProtocolHeader V :=
  ⟨key,2,inputs state point t,outs,shape⟩

structure Prefix {hs : Headers V} (ds : Defs V hs) {key state point t outs shape}
    (ref : Member hs.protocols (caller key state point t outs shape)) (events : Events t) where
  entry : ProtocolEntry ds ref
  atNames : entry.AtInputs names
  message : V.Ty
  residual : V.Ty
  members : Members entry.earlier t message state residual
  sites : Nat → Key
  inside : Term (protocolDialect V entry.earlier)
    (Ctx.empty.extend (names (state := state) (point := point) (t := t))) (outputs residual t)
  block : FirstBlock atNames.body inside
  same : RoleSame [(2,2)] (project 1 (body members events point sites)) (project 1 inside)

def firstInside {D : Dialect} {Γ outs} (term : Term D Γ outs) :
    Option ((mid : List D.Ty) × (inside : Term D Γ mid) × FirstBlock term inside) :=
  match term with
  | .block key index inside results rest => some ⟨_,inside,key,index,results,rest,rfl⟩
  | _ => none

def recognize {hs : Headers V} (ds : Defs V hs) (distinct : hs.keys.Nodup)
    {key state point t outs shape} (ref : Member hs.protocols (caller key state point t outs shape))
    (events : Events t) : Option (Prefix ds ref events) := do
  let entry := ds.protocolEntry distinct ref
  let atNames ← entry.atInputs names
  let ⟨mid,inside,block⟩ ← firstInside atNames.body
  let ⟨msg,residual,members,sites,types,same⟩ ← readCompared (List.nodup_append.mp entry.distinct).1
    state point events ⟨2,rfl⟩ inside
  return ← show Option _ from by
    subst mid
    exact some ⟨entry,atNames,msg,residual,members,sites,inside,block,same⟩

structure AtCall (p : Core.Typed V) (key : Key) {t : V.Ty} (events : Events t) where
  state : V.Ty
  point : V.Ty
  outs : List (LTy V)
  shape : Shape V
  ref : Member p.headers.protocols (caller key state point t outs shape)
  first : Prefix p.defs ref events

def locate (p : Core.Typed V) (key : Key) {t : V.Ty} (events : Events t) : Option (AtCall p key events) := do
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
      ((verifierRound (receive M cert.message inside (cert.sites 1)) (fun _ => challenge M events inside (challengeSite cert.sites))
        (.declared .reject ⟨inside,cert.sites 4⟩) boundary evaluate claim).map (returned M cert.residual)).bind
        fun values => (project 1 cert.block.rest).denote sem path ((Env.empty.extend names args).extend cert.block.results values) := by
  dsimp only
  rw [cert.atNames.meaning,block_denote cert.block]
  have aligned {F : LTy V → Type} {Γ} (env : Env F Γ) : StraightLine.Agrees [(2,2)] env env := by
    intro a b mem ty ha hb
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (List.mem_singleton.mp mem)
    rfl
  rw [← cert.same _ ⟨M,_,_,rfl⟩ _ _ _ (aligned _)]
  rw [verifier cert.members events point M (Defs.fnTable M cert.entry.definitions)
    (Defs.rTable M cert.entry.definitions) boundary evaluate equalLaw boundaryLaw evaluateLaw _ hidden initialPoint claim cert.sites]

#print axioms Prefix.process
end Zkc.Formal.Interactive.Sumcheck.ReductionRound
