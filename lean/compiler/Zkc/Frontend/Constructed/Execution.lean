module

public import Zkc.Frontend.Constructed.Schnorr
public import Zkc.Core.Format.Format

@[expose] public section

namespace Zkc.Frontend.Constructed
open Core

abbrev Log := List (Nat × List Nat × List Nat × Unit)

def ascii (s : String) := s.toUTF8.data.toList.map UInt8.toNat

/-- The legacy catalogue's label consists of unsigned 64-bit little-endian words. -/
def label (words : List Nat) : List Nat :=
  words.flatMap fun w => (List.range 8).map fun i => (w / 256^i) % 256

def Verifier.siteLabel (v : Verifier) (event : Nat) :=
  label [1,0,event,v.prover,v.verifier]

def appendMessage (log : Log) (name data : List Nat) : Log := log ++ [(0,name,data,())]

structure Query where
  history : Log
  label : List Nat
  deriving DecidableEq, Repr

abbrev Units := Vector UInt8 64

/-- A complete query has a fixed 64-byte reply. Receives remain messages at this
stage. A caller may choose the response after seeing the query. -/
inductive Input (M : Model V) where
  | commitment (at_ : Occurrence)
  | response (at_ : Occurrence)
  | squeeze (q : Query)

def signature (M : Model V) : Sig :=
  ⟨Input M, fun | .commitment _ => M.Val point | .response _ => M.Val scalar | .squeeze _ => Units⟩

/-- The model supplies the two nominal formats. Their canonical BLS interpretations
are deployment assumptions. Prefix round trips, widths and byte ranges are required. -/
structure Encoding (A : Type) (width : Nat) extends Core.Format A where
  lawful : toFormat.Lawful
  size : ∀ a, (write a).length = width
  bytesValid : ∀ a n, n ∈ write a → n < 256

structure Interpretation (M : Model V) where
  group : Encoding (M.Val point) 48
  field : Encoding (M.Val scalar) 32
  /-- Interpretation of the reduced natural representative in this model. -/
  fromResidue : Fin Zkc.Vocabulary.Field.bls12381Fr.order → M.Val scalar

def Interpretation.decode {M : Model V} (i : Interpretation M) (units : Units) : M.Val scalar :=
  let n := units.toList.foldl (fun n b => 256*n + b.toNat) 0
  i.fromResidue ⟨n % _, Nat.mod_lt _ (by decide)⟩

/-- The canonical proof-identity computation is an explicit provider on the selected
deployment. Absence is a setup error. A successful result contains exactly 32 bytes. -/
abbrev Identity := Deployed V → Option (Vector UInt8 32)

def initialLog {M : Model V} (i : Interpretation M) (digest : Vector UInt8 32)
    (base publicPoint : M.Val point) : Log :=
  [(0,ascii "dom-sep",ascii merlinSuite,()), (0,ascii "identity",digest.toList.map UInt8.toNat,()),
   (0,label [0,0],i.group.write base,()), (0,label [0,1],i.group.write publicPoint,())]

section
variable {M : Model V} (v : Verifier) (i : Interpretation M)

/-- Interpret only requests issued by the selected layer at its fresh occurrences.
The payload includes the transcript the deployed program actually threaded. -/
def memberRequest (key : Key) (at_ : Occurrence) (arg result : V.Ty) (value : M.Val arg) :
    Process (signature M) Stop (M.Val result) :=
  if at_.path != [] then .halt .undefined
  else if key == MemberOp.absorbPoint.key && at_.key == v.sites.request .absorbPoint then
    if h : arg = pair transcript point ∧ result = transcript then
      let (log, x, _) := cast (congrArg M.Val h.1) value
      .done <| cast (congrArg M.Val h.2.symm) (appendMessage log (v.siteLabel v.labels.commitment) (i.group.write x))
    else .halt .undefined
  else if key == MemberOp.squeeze.key && at_.key == v.sites.request .squeeze then
    if h : arg = transcript ∧ result = pair scalar transcript then
      let log := cast (congrArg M.Val h.1) value
      let name := v.siteLabel v.labels.challenge
      .call (.squeeze ⟨log,name⟩) fun reply =>
        let next := log ++ [(1,name,reply.toList.map UInt8.toNat,())]
        .done <| cast (congrArg M.Val h.2.symm) (i.decode reply,next,())
    else .halt .undefined
  else if key == MemberOp.absorbScalar.key && at_.key == v.sites.request .absorbScalar then
    if h : arg = pair transcript scalar ∧ result = transcript then
      let (log, x, _) := cast (congrArg M.Val h.1) value
      .done <| cast (congrArg M.Val h.2.symm) (appendMessage log (v.siteLabel v.labels.response) (i.field.write x))
    else .halt .undefined
  else .halt .undefined

/-- The three catalogue requests at the installed occurrences have the following
byte semantics for every model, prior state, message and fixed-width reply. -/
theorem absorbPoint_at_site (log : Log) (x : M.Val point) :
    memberRequest v i MemberOp.absorbPoint.key ⟨[],v.sites.request .absorbPoint⟩
      (pair transcript point) transcript (log,x,()) =
    .done (appendMessage log (v.siteLabel v.labels.commitment) (i.group.write x)) := by
  simp [memberRequest]

theorem squeeze_at_site (log : Log) :
    memberRequest v i MemberOp.squeeze.key ⟨[],v.sites.request .squeeze⟩
      transcript (pair scalar transcript) log =
    .call (.squeeze ⟨log,v.siteLabel v.labels.challenge⟩) (fun reply =>
      .done (i.decode reply,log ++ [(1,v.siteLabel v.labels.challenge,reply.toList.map UInt8.toNat,())],())) := by
  simp [memberRequest, MemberOp.key]

theorem absorbScalar_at_site (log : Log) (x : M.Val scalar) :
    memberRequest v i MemberOp.absorbScalar.key ⟨[],v.sites.request .absorbScalar⟩
      (pair transcript scalar) transcript (log,x,()) =
    .done (appendMessage log (v.siteLabel v.labels.response) (i.field.write x)) := by
  simp [memberRequest, MemberOp.key]

def answer : (op : ROp M) → Process (signature M) Stop ((RSig M).Reply op)
  | .own (.request key) [] at_ [arg] (.cons x .nil) result => memberRequest v i key at_ arg result x
  | .get .message p at_ t =>
    if p == v.prover && at_ == ⟨[],v.sites.commitment⟩ then
      if h : t = point then .call (.commitment at_) fun x => .done (cast (congrArg M.Val h.symm) x)
      else .halt .undefined
    else if p == v.prover && at_ == ⟨[],v.sites.response⟩ then
      if h : t = scalar then .call (.response at_) fun x => .done (cast (congrArg M.Val h.symm) x)
      else .halt .undefined
    else .halt .undefined
  | _ => .halt .undefined

/-- Substitute byte-level service calls in the deployed process. Preserve every
return and stop, including the verifier's own guard reason and occurrence. -/
def interpret {A : Type} : Core.Program M A → Process (signature M) Stop A
  | .done x => .done x
  | .halt why => .halt why
  | .call op k => (answer v i op).bind fun x => interpret (k x)

def Verifier.run (identity : Identity) (inputs : HList (RV M v.verifier) v.deployment.entry.ins) :
    Except String (Process (signature M) Stop (HList (RV M v.verifier) v.deployment.entry.outs × Log)) := do
  let some digest := identity v.deployment | throw "FS-IDENTITY: no proof identity for this deployment"
  let heldInputs := cast (congrArg (HList M.Val) v.inputs) (heldValues M v.verifier inputs)
  let .cons base (.cons publicPoint .nil) := heldInputs
  let first := initialLog i digest base publicPoint
  have takes : Stack.Takes (v.deployment.stack v.verifier) = [transcript] := by rw [v.stack_eq]; rfl
  have gives : Stack.Gives (v.deployment.stack v.verifier) = [transcript] := by rw [v.stack_eq]; rfl
  let role := v.deployment.run M v.verifier inputs (cast (congrArg (HList M.Val) takes.symm) (.cons first .nil))
  return (interpret v i role).map fun (out, states) =>
    (out,(cast (congrArg (HList M.Val) gives) states).single)

end
end Zkc.Frontend.Constructed
