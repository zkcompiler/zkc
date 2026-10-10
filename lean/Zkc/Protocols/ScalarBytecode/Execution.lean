import Zkc.Realization.InstructionSimulation
import Zkc.Semantics.OperationContract
import Zkc.Protocols.ScalarBytecode.Codec

set_option autoImplicit false

namespace Zkc.Protocols.ScalarBytecode.Execution
open Zkc.Realization.InstructionSequence Zkc.Semantics.OperationContract Zkc.Realization.ByteEncoding

abbrev Hash := Bytes → Bytes
inductive Op where
 | init | read | absorb | draw | add | mul | check | expectEnd | accept | constant | gexp | gmul | missing
 deriving DecidableEq, Repr
structure Args where
 a : Nat := 0
 b : Nat := 0
 data : Bytes := []
 label : String := ""
abbrev sig : Signature where
 Op := Op
 Arg := fun _ => Args
 Result := fun _ _ => Nat
 legalArg := fun _ _ => True
 legalResult := fun op a v => op = .read → v < a.a
structure Event where
 site : Nat
 op : Op
 label : String
 value : Nat
 data : Bytes
 deriving DecidableEq, Repr
structure Core where
 regs : Nat → Nat
 provider : Bytes
 binding : Nat
structure Cursor where
 full : Bytes
 offset : Nat
 core : Core
structure Tail where
 rest : Bytes
 offset : Nat
 core : Core
def Represents (c : Cursor) (t : Tail) : Prop :=
 c.full.drop c.offset = t.rest ∧ c.offset = t.offset ∧ c.core = t.core
/-- Effect retains consumed bytes even on rejection; raw bytes are always legal arguments. -/
def effect (hash : Hash) (r : Request sig) (core : Core) (bs : Bytes) :
    Reply sig r × Core × Nat × List Event :=
 let ev (v : Nat) (data : Bytes := []) := [Event.mk r.site r.op r.arg.label v data]
 match r.op with
 | .read =>
   if (bs.take 8).length = 8 then
     let v := Zkc.Realization.ByteEncoding.valueBE (bs.take 8)
     if v < r.arg.a then (.ok v,core,8,ev v (bs.take 8))
     else (.reject "abi_decode_failure:noncanonical",core,8,ev v (bs.take 8))
   else (.reject "abi_decode_failure:underrun",core,0,ev 0 (bs.take 8))
 | .init => (.ok 0,{core with provider := hash r.arg.data},0,ev 0 r.arg.data)
 | .absorb => (.ok 0,{core with provider := hash (core.provider ++ [⟨0,by decide⟩] ++ Zkc.Protocols.ScalarBytecode.Codec.enc r.arg.a)},0,ev r.arg.a (Zkc.Protocols.ScalarBytecode.Codec.enc r.arg.a))
 | .draw =>
   let h := hash (core.provider ++ [⟨1,by decide⟩] ++ r.arg.data)
   let v := Zkc.Realization.ByteEncoding.valueBE (h.take 8) % Zkc.Protocols.ScalarBytecode.Parameters.challengeBound
   (.ok v,{core with provider := h},0,ev v r.arg.data)
 | .add => (.ok ((r.arg.a+r.arg.b)%Zkc.Protocols.ScalarBytecode.Parameters.modulus),core,0,[])
 | .mul => (.ok ((r.arg.a*r.arg.b)%Zkc.Protocols.ScalarBytecode.Parameters.modulus),core,0,[])
 | .check => if r.arg.a = r.arg.b then (.ok 0,core,0,ev 1)
             else (.reject "check_failure",core,0,ev 0)
 | .expectEnd => if bs = [] then (.ok 0,core,0,ev 1)
                 else (.reject "proof_trailing_data",core,0,ev 0)
 | .accept => (.ok 0,core,0,ev 1)
 | .constant => (.ok r.arg.a,core,0,[])
 | .gexp => (.ok (r.arg.a ^ r.arg.b % 4611686018427394499),core,0,[])
 | .gmul => (.ok (r.arg.a * r.arg.b % 4611686018427394499),core,0,[])
 | .missing => (.unavailable "E400:no-codec",core,0,ev 0)
def cursorHandler (hash : Hash) : Handler sig Cursor Event := fun r c =>
 let e := effect hash r c.core (c.full.drop c.offset)
 (e.1,⟨c.full,c.offset+e.2.2.1,e.2.1⟩,e.2.2.2)
def tailHandler (hash : Hash) : Handler sig Tail Event := fun r t =>
 let e := effect hash r t.core t.rest
 (e.1,⟨t.rest.drop e.2.2.1,t.offset+e.2.2.1,e.2.1⟩,e.2.2.2)
theorem handler_simulation (hash : Hash) (r : Request sig) (c : Cursor) (t : Tail)
    (h : Represents c t) :
 (cursorHandler hash r c).1 = (tailHandler hash r t).1 ∧
 Represents (cursorHandler hash r c).2.1 (tailHandler hash r t).2.1 ∧
 (cursorHandler hash r c).2.2 = (tailHandler hash r t).2.2 := by
 rcases h with ⟨hb,ho,hc⟩
 simp only [cursorHandler,tailHandler,Represents,hb,hc]
 simp [← hb,List.drop_drop,ho]
/-- This is the Zkc.Protocols.ScalarBytecode.Codec reader, with operationally necessary consumed-state information added. -/
theorem read_value_agrees (hash : Hash) (site modulus : Nat) (core : Core) (bs : Bytes)
    (hm : modulus = Zkc.Protocols.ScalarBytecode.Parameters.modulus) :
 (match (effect hash ⟨site,.read,⟨modulus,0,[],""⟩⟩ core bs).1 with
  | .ok v => some (v,bs.drop 8)
  | _ => none) = Zkc.Protocols.ScalarBytecode.Codec.readScalar bs := by
 subst modulus
 rw [Zkc.Protocols.ScalarBytecode.Codec.readScalar_implementation]
 by_cases hw : (bs.take 8).length = 8 <;>
   by_cases hv : Zkc.Realization.ByteEncoding.valueBE (bs.take 8) < Zkc.Protocols.ScalarBytecode.Parameters.modulus <;>
   simp only [effect,hw,hv,↓reduceIte,true_and,false_and]
/-- Exact canonical word and arbitrary remainder reuse Zkc.Protocols.ScalarBytecode.Codec, not new codec mathematics. -/
theorem read_canonical (v : Nat) (hv : v < Zkc.Protocols.ScalarBytecode.Parameters.modulus) (tail : Bytes) :
 Zkc.Protocols.ScalarBytecode.Codec.readScalar (Zkc.Protocols.ScalarBytecode.Codec.enc v ++ tail) = some (v,tail) := Zkc.Protocols.ScalarBytecode.Codec.scalar_complete v hv tail
inductive Ref where
 | binding
 | reg : Nat → Ref
 deriving Repr
structure Instr where
 site : Nat
 op : Op
 x : Ref := .binding
 y : Ref := .binding
 literal : Nat := 0
 data : Bytes := []
 label : String := ""
 dest : Nat := 0
 deriving Repr
def get (c : Core) : Ref → Nat
 | .binding => c.binding
 | .reg n => c.regs n
def request (i : Instr) (c : Core) : Request sig :=
 ⟨i.site,i.op,⟨(if i.op = .read ∨ i.op = .constant then i.literal else get c i.x),
 get c i.y,i.data,i.label⟩⟩
def put (c : Core) (dest v : Nat) : Core :=
 {c with regs := fun n => if n = dest then v else c.regs n}
def cursorStep (hash : Hash) (i : Instr) (c : Cursor) : Step Cursor Event :=
 let h := cursorHandler hash (request i c.core) c
 match h.1 with
 | .reject why => .halt (.reject why) h.2.1 h.2.2
 | .unavailable why => .halt (.unavailable why) h.2.1 h.2.2
 | .ok v =>
   let t := {h.2.1 with core := put h.2.1.core i.dest v}
   if i.op = .accept then .halt .accept t h.2.2 else .next t h.2.2
def tailStep (hash : Hash) (i : Instr) (c : Tail) : Step Tail Event :=
 let h := tailHandler hash (request i c.core) c
 match h.1 with
 | .reject why => .halt (.reject why) h.2.1 h.2.2
 | .unavailable why => .halt (.unavailable why) h.2.1 h.2.2
 | .ok v =>
   let t := {h.2.1 with core := put h.2.1.core i.dest v}
   if i.op = .accept then .halt .accept t h.2.2 else .next t h.2.2
theorem primitive_simulation (hash : Hash) (i : Instr) (c : Cursor) (t : Tail)
     (h : Represents c t) : Lift Represents (cursorStep hash i c) (tailStep hash i t) := by
 rcases c with ⟨full,offset,core⟩
 rcases t with ⟨rest,offset',core'⟩
 have hc := h.2.2
 dsimp only at hc
 subst core'
 let c : Cursor := ⟨full,offset,core⟩
 let t : Tail := ⟨rest,offset',core⟩
 have hh := handler_simulation hash (request i t.core) c t h
 unfold cursorStep tailStep
 generalize cursorHandler hash (request i t.core) c = l at hh ⊢
 generalize tailHandler hash (request i t.core) t = r at hh ⊢
 rcases l with ⟨lr,ls,le⟩
 rcases r with ⟨rr,rs,re⟩
 rcases hh with ⟨he,hs,hev⟩
 dsimp only at he hs hev ⊢
 subst rr
 subst re
 cases lr with
 | reject why => exact .halt hs
 | unavailable why => exact .halt hs
 | ok v =>
   have hp : Represents {ls with core := put ls.core i.dest v}
       {rs with core := put rs.core i.dest v} := ⟨hs.1,hs.2.1,congrArg (fun s => put s i.dest v) hs.2.2⟩
   change Lift Represents
     (if i.op = .accept then .halt .accept {ls with core := put ls.core i.dest v} le
       else .next {ls with core := put ls.core i.dest v} le)
     (if i.op = .accept then .halt .accept {rs with core := put rs.core i.dest v} le
       else .next {rs with core := put rs.core i.dest v} le)
   by_cases hi : i.op = .accept
   · simp only [hi,↓reduceIte]; exact .halt hp
   · simp only [hi,↓reduceIte]; exact .next hp
/-- No non-read simulation premise remains. Hash is the explicitly selected pure provider. -/
theorem interpreted_run_simulation (hash : Hash) (ops : List Instr)
    (c : Cursor) (t : Tail) (h : Represents c t) :
 TerminalRel Represents (run (cursorStep hash) ops c) (run (tailStep hash) ops t) :=
 simulation _ _ _ (primitive_simulation hash) ops c t h
def verdict : Exit → String
 | .accept => "accept"
 | .incomplete => "incomplete"
 | .unavailable why => "unavailable:" ++ why
 | .reject why => if why = "abi_decode_failure:underrun" ∨ why = "abi_decode_failure:noncanonical"
     then "abi_decode_failure" else why
def coarse {S : Type} (out : Terminal S Event) : String × List Nat :=
 (verdict out.outcome,(out.events.filter (fun e => e.op == .draw)).map Event.value)
theorem coarse_of_strong {c : Terminal Cursor Event} {t : Terminal Tail Event}
    (h : TerminalRel Represents c t) : coarse c = coarse t := by
 simp only [coarse,h.1,h.2.2]
theorem canonical_read_effect (hash : Hash) (site : Nat) (label : String)
    (v : Nat) (hv : v < Zkc.Protocols.ScalarBytecode.Parameters.modulus) (core : Core) (tail : Bytes) :
 effect hash ⟨site,.read,⟨Zkc.Protocols.ScalarBytecode.Parameters.modulus,0,[],label⟩⟩ core (Zkc.Protocols.ScalarBytecode.Codec.enc v ++ tail) =
 (.ok v,core,8,[⟨site,.read,label,v,Zkc.Protocols.ScalarBytecode.Codec.enc v⟩]) := by
 have hv8 : v < 256^8 := Nat.lt_trans hv (by decide : Zkc.Protocols.ScalarBytecode.Parameters.modulus < 256^8)
 simp [effect,Zkc.Protocols.ScalarBytecode.Codec.enc,Zkc.Realization.ByteEncoding.value_be 8 v hv8,hv]
theorem handler_lawful (hash : Hash) : LawfulHandler (tailHandler hash) := by
 intro r t _
 rcases r with ⟨site,op,arg⟩
 cases op
 case read =>
   by_cases hw : (t.rest.take 8).length = 8 <;>
     by_cases hv : Zkc.Realization.ByteEncoding.valueBE (t.rest.take 8) < arg.a <;>
     simp only [tailHandler,effect,hw,hv,↓reduceIte,LegalReply]
   all_goals simp_all
 all_goals simp [tailHandler,effect,LegalReply,sig]
 all_goals split <;> simp_all

theorem no_incomplete_halt (hash : Zkc.Protocols.ScalarBytecode.Execution.Hash) (i : Zkc.Protocols.ScalarBytecode.Execution.Instr) (s : Zkc.Protocols.ScalarBytecode.Execution.Tail)
 (es : List Zkc.Protocols.ScalarBytecode.Execution.Event) (t : Zkc.Protocols.ScalarBytecode.Execution.Tail) :
 Zkc.Protocols.ScalarBytecode.Execution.tailStep hash i s ≠ .halt .incomplete t es := by
 unfold Zkc.Protocols.ScalarBytecode.Execution.tailStep
 generalize Zkc.Protocols.ScalarBytecode.Execution.tailHandler hash (Zkc.Protocols.ScalarBytecode.Execution.request i s.core) s = h
 rcases h with ⟨reply,u,ev⟩
 cases reply with
 | reject why => simp
 | unavailable why => simp
 | ok v =>
   dsimp only
   split <;> simp

end Zkc.Protocols.ScalarBytecode.Execution
