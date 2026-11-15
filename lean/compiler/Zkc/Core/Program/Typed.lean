module

public import Zkc.Core.Program.Dialects
public import Zkc.Core.Program.Linear

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
def LocalOp.canStop {V : Vocabulary} {fns : List (FnHeader V)} {ins res : List V.Ty} :
    LocalOp V fns ins res → Bool
  | .call (hdr := hdr) _ => hdr.canStop
  | _ => false

/-- Whether the body of a function can stop with a reason. -/
def Fn.canStop {V : Vocabulary} {fns : List (FnHeader V)} {hdr : FnHeader V}
    (body : Fn V fns hdr) : Bool :=
  Term.canStop (fun o => LocalOp.canStop o) body

/-- What elaboration decides about the body of a function: its instructions have their own
addresses, every value of a linear type is used once, its header says whether it can stop
with a reason as its body does, and its case analyses without an arm give nothing. With these
a typed function is one that a program by names writes: its printed form elaborates to it. -/
structure FnConditions {V : Vocabulary} {fns : List (FnHeader V)} {hdr : FnHeader V}
    (body : Fn V fns hdr) : Prop where
  distinct : Term.Distinct body
  linear : body.UsedOnce (fun τ : V.Ty => Ty.isLinear V τ)
  stops : hdr.canStop = body.canStop
  armed : body.armed = true

/-- What elaboration decides about the body of a protocol: its roles are those below the
number in its header (nobody else acts in the body, and its ports and results are held by no
other role); nobody but those who perform a choice or a loop acts in its regions; its
instructions have their own addresses; the shape in its header is the shape of its body;
every value of a linear type is used once; and its case analyses without an arm give
nothing. -/
structure ProtocolConditions {V : Vocabulary} {hs : Headers V} (hdr : ProtocolHeader V)
    (body : Prot V hs hdr) : Prop where
  within : Within (List.range hdr.roles) body
  located : ∀ a, a ∈ hdr.ins ++ hdr.outs → ∀ r, r ∈ a.holders → r < hdr.roles
  enclosed : Enclosed body
  distinct : Term.Distinct body
  shaped : hdr.shape = shapeOf body
  linear : body.UsedOnce (fun a : LTy V => Ty.isLinear V a.ty)
  armed : body.armed = true

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

/-! ## One definition after the definitions before it -/

/-- A definition elaborated against the headers of those before it: its header, its body and
what elaboration decided about the body; none of them has its key. Elaborating a definition
needs the headers before it and not their bodies, so this is what the check of one definition
gives while a program is being written, and what a program is extended by. -/
inductive Elaborated (V : Vocabulary) (hs : Headers V) where
  | fn (hdr : FnHeader V) (body : Fn V hs.fns hdr) (ok : FnConditions body)
      (fresh : hdr.key ∉ hs.keys)
  | protocol (hdr : ProtocolHeader V) (body : Prot V hs hdr) (ok : ProtocolConditions hdr body)
      (fresh : hdr.key ∉ hs.keys)

/-- The key of an elaborated definition. -/
def Elaborated.key {V : Vocabulary} {hs : Headers V} : Elaborated V hs → Key
  | .fn hdr .. => hdr.key
  | .protocol hdr .. => hdr.key

/-- The headers before an elaborated definition, with its own. -/
def Elaborated.headers {V : Vocabulary} {hs : Headers V} : Elaborated V hs → Headers V
  | .fn hdr .. => ⟨hdr :: hs.fns, hs.protocols⟩
  | .protocol hdr .. => ⟨hs.fns, hdr :: hs.protocols⟩

/-- Distinct keys stay distinct with the key of a protocol that none of them is. -/
theorem Headers.distinct_protocol {V : Vocabulary} {hs : Headers V} {key : Key}
    (fresh : key ∉ hs.keys) (distinct : hs.keys.Nodup) :
    (hs.fns.map (·.key) ++ key :: hs.protocols.map (·.key)).Nodup := by
  have ⟨fns, protocols, apart⟩ := List.nodup_append.mp distinct
  refine List.nodup_append.mpr ⟨fns, List.nodup_cons.mpr
    ⟨fun found => fresh (List.mem_append_right _ found), protocols⟩, ?_⟩
  intro a inFns b inRest same
  cases List.mem_cons.mp inRest with
  | inl first =>
      subst same
      subst first
      exact fresh (List.mem_append_left _ inFns)
  | inr later => exact apart a inFns b later same

/-- A program with one more definition, elaborated against its headers. -/
def Typed.add {V : Vocabulary} (p : Typed V) : Elaborated V p.headers → Typed V
  | .fn hdr body ok fresh =>
      ⟨⟨hdr :: p.headers.fns, p.headers.protocols⟩, .fn hdr body ok p.defs,
        List.nodup_cons.mpr ⟨fresh, p.distinct⟩⟩
  | .protocol hdr body ok fresh =>
      ⟨⟨p.headers.fns, hdr :: p.headers.protocols⟩, .protocol hdr body ok p.defs,
        Headers.distinct_protocol fresh p.distinct⟩

/-- A program without definitions. -/
def Typed.empty {V : Vocabulary} : Typed V := ⟨⟨[], []⟩, .nil, List.nodup_nil⟩

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

section
variable {α : Type}

theorem Var.key_mem (keyOf : α → Key) : ∀ {items : List α} {a : α}, Var items a →
    keyOf a ∈ items.map keyOf
  | _ :: _, _, .head => List.mem_cons_self
  | _ :: _, _, .tail x => List.mem_cons_of_mem _ (Var.key_mem keyOf x)

theorem Var.withKey_absent (keyOf : α → Key) (key : Key) : ∀ {items : List α},
    key ∉ items.map keyOf → Var.withKey keyOf key items = []
  | [], _ => rfl
  | a :: rest, absent => by
      have other : keyOf a ≠ key := fun same => absent (same ▸ List.mem_cons_self)
      have later : key ∉ rest.map keyOf := fun found => absent (List.mem_cons_of_mem _ found)
      simp only [Var.withKey, other, ↓reduceIte, Var.withKey_absent keyOf key later, List.map_nil]

/-- With distinct keys, the variable with the key of an item is that item's. -/
theorem Var.withKey_key (keyOf : α → Key) : ∀ {items : List α} {a : α} (x : Var items a),
    (items.map keyOf).Nodup → Var.withKey keyOf (keyOf a) items = [⟨a, x⟩]
  | _ :: _, _, .head, distinct => by
      have absent := (List.nodup_cons.mp distinct).1
      simp only [Var.withKey, ↓reduceIte, Var.withKey_absent keyOf _ absent, List.map_nil]
  | b :: _, a, .tail x, distinct => by
      have ⟨absent, others⟩ := List.nodup_cons.mp distinct
      have other : keyOf b ≠ keyOf a := fun same => absent (same ▸ Var.key_mem keyOf x)
      simp only [Var.withKey, other, ↓reduceIte, Var.withKey_key keyOf x others, List.map_cons,
        List.map_nil]

end

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
