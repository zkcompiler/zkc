import Zkc.Protocols.BackendProfiles.Definitions
import Zkc.Realization.JsonArrays

set_option autoImplicit false

namespace Zkc.Protocols.BackendProfiles
open Lean (Json)
open Zkc.Realization.JsonArrays

def literalWire : Zkc.Protocols.BackendProfiles.Literal → Wire
  | .unit => .array [.str "literal", .str "unit", .array []]
  | .shift n => .array [.str "literal", .str "shift:u6", .array [.nat n]]
  | .scalar n => .array [.str "literal", .str "scalar", .array [.nat n]]

def termWire {Op : Type} (op : Op → Wire) : Term Op → Wire
  | .input i => .array [.str "input", .nat i]
  | .literal v => literalWire v
  | .apply o a b => .array [.str "apply", op o, termWire op a, termWire op b]
  | .choose c a b => .array [.str "choose", termWire op c, termWire op a, termWire op b]

def opWire : NativeOp → Wire
  | .addmod n => .array [.str "addmod", .nat n]
  | .mulmod n => .array [.str "mulmod", .nat n]
  | .node s => .array [.str "node", .str s]
  | .ofWords s => .array [.str "ofWords", .str s]
  | .odd n => .array [.str "odd", .nat n]
  | .shift n => .array [.str "shift", .nat n]

def blockWire {Op : Type} (op : Op → Wire) (b : Block Op) : Wire :=
  .array (b.map fun (i,t) => .array [.nat i, termWire op t])

def profileWire : Profile → Wire
  | .scalar => .str "scalar"
  | .fri => .str "fri"

def requestWire (label : String) (r : Request) : Wire :=
  .array [.str label, profileWire r.profile, .nat r.inputs,
    blockWire Wire.str r.expected, .array (r.expectedExports.map Wire.nat),
    blockWire opWire r.native, .array (r.nativeExports.map Wire.nat)]

theorem literalWire_injective (a b : Zkc.Protocols.BackendProfiles.Literal)
    (h : literalWire a = literalWire b) : a = b := by
  cases a <;> cases b <;> simp_all [literalWire]

theorem termWire_injective {Op : Type} (op : Op → Wire)
    (inj : Function.Injective op) (a other : Term Op)
    (h : termWire op a = termWire op other) : a = other := by
  induction a generalizing other with
  | input i =>
    cases other <;> simp_all [termWire, literalWire]
    rename_i v
    cases v <;> simp at h
  | literal v =>
    cases other with
    | input i => cases v <;> simp [termWire, literalWire] at h
    | literal w => exact congrArg Zkc.Compiler.Readback.Term.literal (literalWire_injective v w h)
    | apply o a b => cases v <;> simp [termWire, literalWire] at h
    | choose c a b => cases v <;> simp [termWire, literalWire] at h
  | apply o a b iha ihb =>
    cases other with
    | input i => simp [termWire] at h
    | literal v => cases v <;> simp [termWire, literalWire] at h
    | apply p x y =>
      simp only [termWire, Wire.array.injEq, List.cons.injEq] at h
      rw [inj h.2.1, iha x h.2.2.1, ihb y h.2.2.2.1]
    | choose c x y => simp [termWire] at h
  | choose c a b ihc iha ihb =>
    cases other with
    | input i => simp [termWire] at h
    | literal v => cases v <;> simp [termWire, literalWire] at h
    | apply p x y => simp [termWire] at h
    | choose d x y =>
      simp only [termWire, Wire.array.injEq, List.cons.injEq] at h
      rw [ihc d h.2.1, iha x h.2.2.1, ihb y h.2.2.2.1]

theorem opWire_injective : Function.Injective opWire := by
  intro a b h; cases a <;> cases b <;> simp_all [opWire]

theorem blockWire_injective {Op : Type} (op : Op → Wire)
    (inj : Function.Injective op) (a b : Block Op)
    (h : blockWire op a = blockWire op b) : a = b := by
  induction a generalizing b with
  | nil => cases b <;> simp_all [blockWire]
  | cons row rest ih =>
    obtain ⟨i,t⟩ := row
    cases b with
    | nil => simp [blockWire] at h
    | cons row' rest' =>
      obtain ⟨j,u⟩ := row'
      simp only [blockWire, List.map_cons, Wire.array.injEq, List.cons.injEq] at h
      have hi : i = j := Wire.nat.inj h.1.1
      have ht := termWire_injective op inj t u h.1.2.1
      have hr := ih rest' (congrArg Wire.array h.2)
      simp [hi, ht, hr]

theorem mapNat_injective (xs ys : List Nat)
    (h : xs.map Wire.nat = ys.map Wire.nat) : xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all
  | cons x xs ih =>
    cases ys with
    | nil => simp at h
    | cons y ys =>
      simp only [List.map_cons, List.cons.injEq, Wire.nat.injEq] at h
      simp [h.1, ih ys h.2]

theorem requestWire_injective (id jd : String) (r s : Request)
    (h : requestWire id r = requestWire jd s) : id = jd ∧ r = s := by
  cases r with | mk rp rn rb re rt rx =>
   cases s with | mk sp sn sb se st sx =>
    simp only [requestWire, Wire.array.injEq, List.cons.injEq] at h
    have hp : rp = sp := by cases rp <;> cases sp <;> simp_all [profileWire]
    have hb := blockWire_injective Wire.str (fun _ _ => Wire.str.inj) rb sb h.2.2.2.1
    have ht := blockWire_injective opWire opWire_injective rt st h.2.2.2.2.2.1
    have he : re = se := mapNat_injective re se h.2.2.2.2.1
    have hx : rx = sx := mapNat_injective rx sx h.2.2.2.2.2.2.1
    exact ⟨Wire.str.inj h.1, by simp [hp, Wire.nat.inj h.2.2.1, hb, ht, he, hx]⟩

theorem representation_unique (j : Json) (f g : Nat) (id jd : String) (r s : Request)
    (hr : checkJson f j (requestWire id r) = true)
    (hs : checkJson g j (requestWire jd s) = true) : id = jd ∧ r = s := by
  exact requestWire_injective id jd r s (toJson_injective _ _
    ((checkJson_sound f j _ hr).symm.trans (checkJson_sound g j _ hs)))

end Zkc.Protocols.BackendProfiles
