module

public import Zkc.Frontend.Constructed.Layer

@[expose] public section

namespace Zkc.Frontend.Constructed
open Core BodyAnalysis

abbrev Code (Op Who : Type) := List (Instruction Op Who) × List Name

structure ClauseCode (V : Core.Vocabulary) where
  site : Site
  part : Part V
  takes : List V.Ty
  gives : List V.Ty
  body : Code (RoleCode V) Holders
  deriving DecidableEq

structure LayerCode (V : Core.Vocabulary) where
  line : LineTag
  state : V.Ty
  takes : List V.Ty
  gives : List V.Ty
  start : Code (LocalRaw V) Unit
  clauses : List (ClauseCode V)
  again : Code (LocalRaw V) Unit
  finish : Code (LocalRaw V) Unit
  deriving DecidableEq

variable {V : Core.Vocabulary} {hs : Headers V} {r : Role} {ins : List (LTy V)}

/-- Inspect the actual code, retaining keys, operand positions, binders and exits.
Equal-typed code with a different data dependency has a different image. -/
def readLayer (layer : Layer V hs r ins) : LayerCode V :=
  ⟨layer.line,layer.state,layer.takes,layer.gives,
   eraseBody LocalOp.print id layer.start,
   layer.clauses.map (fun c => ⟨c.site.site,c.site.part,c.site.takes,c.site.gives,
     eraseBody roleCode id c.code⟩),
   eraseBody LocalOp.print id layer.again,eraseBody LocalOp.print id layer.finish⟩

/-- Contract of a message site: forward, pair the prior state with the reply,
invoke the bound member, then return the forwarded value and the new state. -/
def messageCode (s : Sites) (p r : Role) (key : Key) (t : V.Ty) (member : MemberOp) : ClauseCode V :=
  ⟨⟨[],key⟩,.get .message p,[],[t],
    ([.op key [1] (.get t [] .message p [r]) [],
      .op ⟨s.fresh + 3⟩ [2] (.compute [r] (.owned .make [pair transcript t] [])) [0,1],
      .op (s.request member) [3] (.own (.request member.key) [] transcript) [2]], [1,3])⟩

def declaredCode (s : Sites) (p r : Role) (point scalar : V.Ty) (law : V.LawKey) : LayerCode V :=
  ⟨.construction, transcript, [transcript], [transcript], ([],[0]),
    [messageCode s p r s.commitment point .absorbPoint,
     ⟨⟨[],s.challenge⟩,.own (.coin law) [p],[],[scalar],
       ([.op (s.request .squeeze) [1] (.own (.request MemberOp.squeeze.key) [] (pair scalar transcript)) [0],
         .op ⟨s.fresh + 3⟩ [2,3] (.compute [r] (.owned .take [pair scalar transcript] [])) [1]],[2,3])⟩,
     messageCode s p r s.response scalar .absorbScalar], ([],[1]), ([],[0])⟩

theorem verifierLayer_readback (s : Sites) (p r : Role) (point scalar : V.Ty) (law : V.LawKey)
    (ports : List (LTy V)) :
    readLayer (hs := hs) (verifierLayer s p r point scalar law ports) = declaredCode s p r point scalar law := rfl

end Zkc.Frontend.Constructed
