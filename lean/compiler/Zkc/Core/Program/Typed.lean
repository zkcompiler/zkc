module

public import Zkc.Core.Program.Dialects

@[expose] public section

/-!
A typed program: its definitions, each with what elaboration decided about its body, and
the lookup of a definition by its key.
-/

namespace Zkc.Core

/-! ## A program -/

abbrev Fn (V : Vocabulary) (fns : List (FnHeader V)) (hdr : FnHeader V) : Type :=
  Term (localDialect V fns) hdr.ins hdr.outs

abbrev Prot (V : Vocabulary) (hs : Headers V) (hdr : ProtocolHeader V) : Type :=
  Term (protocolDialect V hs) hdr.ins hdr.outs

abbrev RoleP (V : Vocabulary) (hs : Headers V) (r : Role) (hdr : ProtocolHeader V) : Type :=
  Term (roleDialect V hs r) hdr.ins hdr.outs

/-- Whether a local operation can stop with a reason: a call of a function that can. -/
def LocalOp.canStop {V : Vocabulary} {fns : List (FnHeader V)} {ins res : List V.Ty} : LocalOp V fns ins res → Bool
  | .call (hdr := hdr) _ => hdr.canStop
  | _ => false

/-- Whether the body of a function can stop with a reason. -/
def Fn.canStop {V : Vocabulary} {fns : List (FnHeader V)} {hdr : FnHeader V} (body : Fn V fns hdr) : Bool :=
  Term.canStop (fun o => LocalOp.canStop o) body

/-- What elaboration decides about the body of a function: its instructions have their own
addresses, every value of a linear type is used once, and its header says whether it can stop
with a reason as its body does. -/
structure FnConditions {V : Vocabulary} {fns : List (FnHeader V)} {hdr : FnHeader V}
    (body : Fn V fns hdr) : Prop where
  distinct : Term.Distinct body
  linear : body.UsedOnce (fun τ : V.Ty => Ty.isLinear V τ)
  stops : hdr.canStop = body.canStop

/-- What elaboration decides about the body of a protocol: its roles are those below the
number in its header (nobody else acts in the body, and its ports and results are held by no
other role); nobody but those who perform a choice or a loop acts in its regions; its
instructions have their own addresses; the shape in its header is the shape of its body; and
every value of a linear type is used once. -/
structure ProtocolConditions {V : Vocabulary} {hs : Headers V} (hdr : ProtocolHeader V)
    (body : Prot V hs hdr) : Prop where
  within : Within (List.range hdr.roles) body
  located : ∀ a, a ∈ hdr.ins ++ hdr.outs → ∀ r, r ∈ a.holders → r < hdr.roles
  enclosed : Enclosed body
  distinct : Term.Distinct body
  shaped : hdr.shape = shapeOf body
  linear : body.UsedOnce (fun a : LTy V => Ty.isLinear V a.ty)

/-- The definitions of a program, the latest first; each applies only earlier ones, and each
carries what elaboration decided about its body, once. -/
inductive Defs (V : Vocabulary) : Headers V → Type where
  | nil : Defs V ⟨[], []⟩
  | fn {hs} (hdr : FnHeader V) (body : Fn V hs.fns hdr) (ok : FnConditions body)
      (rest : Defs V hs) : Defs V ⟨hdr :: hs.fns, hs.protocols⟩
  | protocol {hs} (hdr : ProtocolHeader V) (body : Prot V hs hdr) (ok : ProtocolConditions hdr body)
      (rest : Defs V hs) : Defs V ⟨hs.fns, hdr :: hs.protocols⟩

/-- The keys of the definitions of a program. -/
def Headers.keys {V : Vocabulary} (hs : Headers V) : List Key :=
  hs.fns.map (·.key) ++ hs.protocols.map (·.key)

/-- A typed program. The keys of its definitions are distinct. -/
structure Typed (V : Vocabulary) where
  headers : Headers V
  defs : Defs V headers
  distinct : headers.keys.Nodup

/-! ## A definition found by its key -/

/-- A definition of a program, as a typed reference: a function or a protocol. -/
inductive Ref {V : Vocabulary} (hs : Headers V) where
  | fn {hdr : FnHeader V} (ref : Var hs.fns hdr)
  | protocol {hdr : ProtocolHeader V} (ref : Var hs.protocols hdr)

/-- The key of a referenced definition. -/
def Ref.key {V : Vocabulary} {hs : Headers V} : Ref hs → Key
  | .fn (hdr := hdr) _ => hdr.key
  | .protocol (hdr := hdr) _ => hdr.key

/-- The references of the headers with the key. -/
def Var.withKey {α : Type} (keyOf : α → Key) (key : Key) :
    (items : List α) → List ((a : α) × Var items a)
  | [] => []
  | a :: rest =>
      let later := (Var.withKey keyOf key rest).map fun found => ⟨found.1, .tail found.2⟩
      if keyOf a = key then ⟨a, .head⟩ :: later else later

/-- The definition with the key, when exactly one has it. -/
def Headers.find {V : Vocabulary} (hs : Headers V) (key : Key) : Option (Ref hs) :=
  match (Var.withKey (·.key) key hs.fns).map (fun found => Ref.fn found.2) ++
      (Var.withKey (·.key) key hs.protocols).map (fun found => Ref.protocol found.2) with
  | [found] => some found
  | _ => none

/-- A definition of a typed program, as a typed reference. -/
abbrev Subject {V : Vocabulary} (p : Typed V) : Type := Ref p.headers

/-- The definition of a typed program with the key. -/
def Typed.find {V : Vocabulary} (p : Typed V) (key : Key) : Option (Subject p) :=
  p.headers.find key


/-- The keys of the definitions that the definition with the key reaches by calls and
applications, itself included. -/
def Defs.closureOf {V : Vocabulary} : {hs : Headers V} → Defs V hs → Key → List Key
  | _, .nil, _ => []
  | _, .fn hdr body _ rest, key =>
      if hdr.key = key then
        hdr.key :: (Term.calls (fun o => LocalOp.calls o) body).flatMap (Defs.closureOf rest)
      else Defs.closureOf rest key
  | _, .protocol hdr body _ rest, key =>
      if hdr.key = key then
        hdr.key :: (Term.calls (fun o => ProtocolOp.calls o) body).flatMap (Defs.closureOf rest)
      else Defs.closureOf rest key

/-- The keys of the definitions that a definition reaches by calls and applications, itself
included. -/
def Subject.closure {V : Vocabulary} {p : Typed V} (s : Subject p) : List Key :=
  p.defs.closureOf s.key

end Zkc.Core
