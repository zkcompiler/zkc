module

public import Zkc.Core.Program.Dialects
public import Zkc.Core.Program.Linear

@[expose] public section

/-!
A typed program: its definitions, each with the names of its inputs and what elaboration decided
about its body, and the lookup of a definition by its key. The body of a definition is a term in
the context of its inputs, by their names; a header has no names, since a caller passes by
position. Also one definition elaborated against the headers before it (`Elaborated`), the
program extended by it (`Typed.add`), whether a function or a local operation can stop
(`Fn.canStop`, `LocalOp.canStop`), and the definitions that a definition reaches by its calls
(`Defs.closureOf`).
-/

namespace Zkc.Core

/-! ## A program -/

/-- The body of a function, in the context of its inputs by their names. -/
abbrev Fn (V : Vocabulary) (fns : List (FnHeader V)) (hdr : FnHeader V)
    (inputs : Names hdr.ins) : Type :=
  Term (localDialect V fns) (Ctx.empty.extend inputs) hdr.outs

/-- The body of a protocol, in the context of its ports by their names. -/
abbrev Prot (V : Vocabulary) (hs : Headers V) (hdr : ProtocolHeader V)
    (inputs : Names hdr.ins) : Type :=
  Term (protocolDialect V hs) (Ctx.empty.extend inputs) hdr.outs

/-- The program of a role of a protocol, in the context of the protocol's ports by their
names. -/
abbrev RoleP (V : Vocabulary) (hs : Headers V) (r : Role) (hdr : ProtocolHeader V)
    (inputs : Names hdr.ins) : Type :=
  Term (roleDialect V hs r) (Ctx.empty.extend inputs) hdr.outs

/-- Whether a local operation can stop with a reason: a call of a function that can. -/
def LocalOp.canStop {V : Vocabulary} {fns : List (FnHeader V)} {ins res : List V.Ty} :
    LocalOp V fns ins res → Bool
  | .call (hdr := hdr) _ => hdr.canStop
  | _ => false

/-- Whether the body of a function can stop with a reason. -/
def Fn.canStop {V : Vocabulary} {fns : List (FnHeader V)} {hdr : FnHeader V}
    {inputs : Names hdr.ins} (body : Fn V fns hdr inputs) : Bool :=
  Term.canStop (fun o => LocalOp.canStop o) body

/-- What elaboration decides about the body of a function: its instructions have their own
addresses, every value of a linear type is used once, its header says whether it can stop
with a reason as its body does, its case analyses without an arm give nothing, and every name
is bound at one place. With these a typed function is one that a program by names writes: its
erased form elaborates to it. -/
structure FnConditions {V : Vocabulary} {fns : List (FnHeader V)} {hdr : FnHeader V}
    {inputs : Names hdr.ins} (body : Fn V fns hdr inputs) : Prop where
  distinct : Term.Distinct body
  linear : body.UsedOnce (fun τ : V.Ty => Ty.isLinear V τ) inputs
  stops : hdr.canStop = body.canStop
  armed : body.armed = true
  once : body.BoundOnce inputs.toList

/-- What elaboration decides about the body of a protocol: its roles are those below the
number in its header (nobody else acts in the body, and its ports and results are held by no
other role); nobody but those who perform a choice or a loop acts in its regions; its
instructions have their own addresses; the shape in its header is the shape of its body;
every value of a linear type is used once; its case analyses without an arm give nothing; and
every name is bound at one place. -/
structure ProtocolConditions {V : Vocabulary} {hs : Headers V} (hdr : ProtocolHeader V)
    {inputs : Names hdr.ins} (body : Prot V hs hdr inputs) : Prop where
  within : Within (List.range hdr.roles) body
  located : ∀ a, a ∈ hdr.ins ++ hdr.outs → ∀ r, r ∈ a.holders → r < hdr.roles
  enclosed : Enclosed body
  distinct : Term.Distinct body
  shaped : hdr.shape = shapeOf body
  linear : body.UsedOnce (fun a : LTy V => Ty.isLinear V a.ty) inputs
  armed : body.armed = true
  once : body.BoundOnce inputs.toList

/-- The definitions of a program, the latest first; each applies only earlier ones, and each
carries the names of its inputs and what elaboration decided about its body, once. -/
inductive Defs (V : Vocabulary) : Headers V → Type where
  | nil : Defs V ⟨[], []⟩
  | fn {hs} (hdr : FnHeader V) (inputs : Names hdr.ins) (body : Fn V hs.fns hdr inputs)
      (ok : FnConditions body) (rest : Defs V hs) : Defs V ⟨hdr :: hs.fns, hs.protocols⟩
  | protocol {hs} (hdr : ProtocolHeader V) (inputs : Names hdr.ins) (body : Prot V hs hdr inputs)
      (ok : ProtocolConditions hdr body) (rest : Defs V hs) : Defs V ⟨hs.fns, hdr :: hs.protocols⟩

/-- The keys of the definitions of a program. -/
def Headers.keys {V : Vocabulary} (hs : Headers V) : List Key :=
  hs.fns.map (·.key) ++ hs.protocols.map (·.key)

/-- A typed program. The keys of its definitions are distinct. -/
structure Typed (V : Vocabulary) where
  headers : Headers V
  defs : Defs V headers
  distinct : headers.keys.Nodup

/-! ## One definition after the definitions before it -/

/-- A definition elaborated against the headers of those before it: its header, the names of
its inputs, its body and what elaboration decided about the body; none of them has its key.
Elaborating a definition needs the headers before it and not their bodies, so this is what the
check of one definition gives while a program is being written, and what a program is extended
by. -/
inductive Elaborated (V : Vocabulary) (hs : Headers V) where
  | fn (hdr : FnHeader V) (inputs : Names hdr.ins) (body : Fn V hs.fns hdr inputs)
      (ok : FnConditions body) (fresh : hdr.key ∉ hs.keys)
  | protocol (hdr : ProtocolHeader V) (inputs : Names hdr.ins) (body : Prot V hs hdr inputs)
      (ok : ProtocolConditions hdr body) (fresh : hdr.key ∉ hs.keys)

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
  | .fn hdr inputs body ok fresh =>
      ⟨⟨hdr :: p.headers.fns, p.headers.protocols⟩, .fn hdr inputs body ok p.defs,
        List.nodup_cons.mpr ⟨fresh, p.distinct⟩⟩
  | .protocol hdr inputs body ok fresh =>
      ⟨⟨p.headers.fns, hdr :: p.headers.protocols⟩, .protocol hdr inputs body ok p.defs,
        Headers.distinct_protocol fresh p.distinct⟩

/-- A program without definitions. -/
def Typed.empty {V : Vocabulary} : Typed V := ⟨⟨[], []⟩, .nil, List.nodup_nil⟩

/-! ## A definition found by its key -/

/-- A definition of a program, as a typed reference: a function or a protocol. -/
inductive Ref {V : Vocabulary} (hs : Headers V) where
  | fn {hdr : FnHeader V} (ref : Member hs.fns hdr)
  | protocol {hdr : ProtocolHeader V} (ref : Member hs.protocols hdr)

/-- The key of a referenced definition. -/
def Ref.key {V : Vocabulary} {hs : Headers V} : Ref hs → Key
  | .fn (hdr := hdr) _ => hdr.key
  | .protocol (hdr := hdr) _ => hdr.key

/-- The references of the headers with the key. -/
def Member.withKey {α : Type} (keyOf : α → Key) (key : Key) :
    (items : List α) → List ((a : α) × Member items a)
  | [] => []
  | a :: rest =>
      let later := (Member.withKey keyOf key rest).map fun found => ⟨found.1, .tail found.2⟩
      if keyOf a = key then ⟨a, .head⟩ :: later else later

section
variable {α : Type}

theorem Member.key_mem (keyOf : α → Key) : ∀ {items : List α} {a : α}, Member items a →
    keyOf a ∈ items.map keyOf
  | _ :: _, _, .head => List.mem_cons_self
  | _ :: _, _, .tail x => List.mem_cons_of_mem _ (Member.key_mem keyOf x)

theorem Member.withKey_absent (keyOf : α → Key) (key : Key) : ∀ {items : List α},
    key ∉ items.map keyOf → Member.withKey keyOf key items = []
  | [], _ => rfl
  | a :: rest, absent => by
      have other : keyOf a ≠ key := fun same => absent (same ▸ List.mem_cons_self)
      have later : key ∉ rest.map keyOf := fun found => absent (List.mem_cons_of_mem _ found)
      simp only [Member.withKey, other, ↓reduceIte, Member.withKey_absent keyOf key later,
        List.map_nil]

/-- With distinct keys, the reference with the key of an item is that item's. -/
theorem Member.withKey_key (keyOf : α → Key) :
    ∀ {items : List α} {a : α} (x : Member items a),
      (items.map keyOf).Nodup → Member.withKey keyOf (keyOf a) items = [⟨a, x⟩]
  | _ :: _, _, .head, distinct => by
      have absent := (List.nodup_cons.mp distinct).1
      simp only [Member.withKey, ↓reduceIte, Member.withKey_absent keyOf _ absent, List.map_nil]
  | b :: _, a, .tail x, distinct => by
      have ⟨absent, others⟩ := List.nodup_cons.mp distinct
      have other : keyOf b ≠ keyOf a := fun same => absent (same ▸ Member.key_mem keyOf x)
      simp only [Member.withKey, other, ↓reduceIte, Member.withKey_key keyOf x others,
        List.map_cons, List.map_nil]

/-- A reference with a key has that key. -/
theorem Member.key_of_withKey (keyOf : α → Key) (key : Key) :
    ∀ {items : List α} {found : (a : α) × Member items a},
      found ∈ Member.withKey keyOf key items → keyOf found.1 = key
  | [], _, listed => nomatch listed
  | a :: rest, found, listed => by
      simp only [Member.withKey] at listed
      split at listed
      · rename_i same
        rcases List.mem_cons.mp listed with first | later
        · subst first
          exact same
        · obtain ⟨other, inRest, moved⟩ := List.mem_map.mp later
          subst moved
          exact Member.key_of_withKey keyOf key (items := rest) inRest
      · obtain ⟨other, inRest, moved⟩ := List.mem_map.mp listed
        subst moved
        exact Member.key_of_withKey keyOf key (items := rest) inRest

end

/-- The definition with the key, when exactly one has it. -/
def Headers.find {V : Vocabulary} (hs : Headers V) (key : Key) : Option (Ref hs) :=
  match (Member.withKey (·.key) key hs.fns).map (fun found => Ref.fn found.2) ++
      (Member.withKey (·.key) key hs.protocols).map (fun found => Ref.protocol found.2) with
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
  | _, .fn hdr _ body _ rest, key =>
      if hdr.key = key then
        hdr.key :: (Term.calls (fun o => LocalOp.calls o) body).flatMap (Defs.closureOf rest)
      else Defs.closureOf rest key
  | _, .protocol hdr _ body _ rest, key =>
      if hdr.key = key then
        hdr.key :: (Term.calls (fun o => ProtocolOp.calls o) body).flatMap (Defs.closureOf rest)
      else Defs.closureOf rest key

/-- The keys of the definitions that a definition reaches by calls and applications, itself
included. -/
def Subject.closure {V : Vocabulary} {p : Typed V} (s : Subject p) : List Key :=
  p.defs.closureOf s.key

end Zkc.Core
