import Zkc.Protocols.ScalarBytecode.Execution
import Zkc.Realization.InstructionComposition
import Zkc.Semantics.Locality

set_option autoImplicit false

namespace Zkc.Protocols.ScalarBytecode.Frames
open Zkc.Realization.InstructionSequence Zkc.Semantics.OperationContract Zkc.Realization.ByteEncoding Zkc.Semantics.Locality Zkc.Protocols.ScalarBytecode.Execution

-- Strong observation: only explicitly hidden scratch registers may differ.
def CoreRel (live : Nat → Prop) (a b : Core) : Prop :=
 a.provider = b.provider ∧ a.binding = b.binding ∧ ∀ n, live n → a.regs n = b.regs n
def Rel (live : Nat → Prop) (a b : Tail) : Prop :=
 a.rest = b.rest ∧ a.offset = b.offset ∧ CoreRel live a.core b.core

theorem reflRel (live : Nat → Prop) (a : Tail) : Rel live a a := ⟨rfl,rfl,rfl,rfl,fun _ _ => rfl⟩
def Reads (live : Nat → Prop) : Ref → Prop
 | .binding => True
 | .reg n => live n
def Safe (live : Nat → Prop) (i : Instr) := Reads live i.x ∧ Reads live i.y

theorem get_eq (live : Nat → Prop) (a b : Core) (r : Ref)
 (h : CoreRel live a b) (hr : Reads live r) : get a r = get b r := by
 cases r with
 | binding => exact h.2.1
 | reg n => exact h.2.2 n hr

theorem request_eq (live : Nat → Prop) (i : Instr) (a b : Core)
 (h : CoreRel live a b) (hi : Safe live i) : request i a = request i b := by
 simp only [request,get_eq live a b i.x h hi.1,get_eq live a b i.y h hi.2]

theorem put_rel (live : Nat → Prop) (a b : Core) (d v : Nat)
 (h : CoreRel live a b) : CoreRel live (put a d v) (put b d v) := by
 refine ⟨h.1,h.2.1,?_⟩
 intro n hn
 simp only [put]
 split
 · rfl
 · exact h.2.2 n hn

theorem effect_rel (live : Nat → Prop) (hash : Hash) (r : Request sig)
 (a b : Core) (bs : Bytes) (h : CoreRel live a b) :
 (effect hash r a bs).1 = (effect hash r b bs).1 ∧
 CoreRel live (effect hash r a bs).2.1 (effect hash r b bs).2.1 ∧
 (effect hash r a bs).2.2 = (effect hash r b bs).2.2 := by
 rcases r with ⟨site,op,arg⟩
 cases op
 case read =>
   by_cases hw : (bs.take 8).length = 8 <;>
     by_cases hv : Zkc.Realization.ByteEncoding.valueBE (bs.take 8) < arg.a <;>
     simp only [effect,hw,hv,↓reduceIte]
   all_goals exact ⟨True.intro,h,True.intro⟩
 all_goals simp only [effect]
 all_goals try { split <;> simp_all [CoreRel] }
 all_goals simp_all [CoreRel]

-- Factor the dependent reply match without changing any operation semantics.
def finish (op : Op) (dest : Nat) (a : Tail) {r : Request sig}
 (e : Reply sig r × Core × Nat × List Event) : Step Tail Event :=
 let u : Tail := ⟨a.rest.drop e.2.2.1,a.offset + e.2.2.1,e.2.1⟩
 match e.1 with
 | .reject why => .halt (.reject why) u e.2.2.2
 | .unavailable why => .halt (.unavailable why) u e.2.2.2
 | .ok v =>
   let t := {u with core := put u.core dest v}
   if op = .accept then .halt .accept t e.2.2.2 else .next t e.2.2.2

theorem step_finish (hash : Hash) (i : Instr) (a : Tail) :
 tailStep hash i a = finish i.op i.dest a (effect hash (request i a.core) a.core a.rest) := by
 unfold tailStep tailHandler finish
 generalize effect hash (request i a.core) a.core a.rest = e
 rcases e with ⟨reply,core,n,ev⟩
 cases reply <;> rfl

theorem step_frame (live : Nat → Prop) (hash : Hash) (i : Instr)
 (hi : Safe live i) (a b : Tail) (h : Rel live a b) :
 Lift (Rel live) (tailStep hash i a) (tailStep hash i b) := by
 have hq := request_eq live i a.core b.core h.2.2 hi
 have he := effect_rel live hash (request i b.core) a.core b.core b.rest h.2.2
 rw [step_finish,step_finish]
 rw [hq]
 simp only [h.1]
 generalize effect hash (request i b.core) a.core b.rest = x at he ⊢
 generalize effect hash (request i b.core) b.core b.rest = y at he ⊢
 rcases x with ⟨xr,xc,xn,xe⟩
 rcases y with ⟨yr,yc,yn,ye⟩
 rcases he with ⟨hr,hc,hev⟩
 cases hr
 have hn : xn = yn := congrArg Prod.fst hev
 have hes : xe = ye := congrArg Prod.snd hev
 cases hn; cases hes
 have hs : Rel live ⟨a.rest.drop xn,a.offset+xn,xc⟩ ⟨b.rest.drop xn,b.offset+xn,yc⟩ :=
  ⟨by rw [h.1],by rw [h.2.1],hc⟩
 cases xr with
 | reject why => exact .halt hs
 | unavailable why => exact .halt hs
 | ok v =>
   have hp : Rel live ⟨a.rest.drop xn,a.offset+xn,put xc i.dest v⟩
       ⟨b.rest.drop xn,b.offset+xn,put yc i.dest v⟩ := ⟨hs.1,hs.2.1,put_rel live xc yc _ _ hc⟩
   dsimp only [finish]
   split
   · exact .halt hp
   · exact .next hp

-- Finite continuation theorem: syntactic operand support is checked, not contextual opacity assumed.
theorem continuation_frame (live : Nat → Prop) (hash : Hash) (ops : List Instr)
 (safe : ∀ i ∈ ops, Safe live i) (a b : Tail) (h : Rel live a b) :
 TerminalRel (Rel live) (run (tailStep hash) ops a) (run (tailStep hash) ops b) := by
 induction ops generalizing a b with
 | nil => exact ⟨rfl,h,rfl⟩
 | cons i ops ih =>
   have hh := step_frame live hash i (safe i (by simp)) a b h
   cases ha : tailStep hash i a <;> cases hb : tailStep hash i b <;> rw [ha,hb] at hh
   · cases hh with
     | next hab =>
       have hr := ih (fun j hj => safe j (by simp [hj])) _ _ hab
       simpa only [TerminalRel,run,ha,hb] using
         And.intro hr.1 (And.intro hr.2.1 (congrArg (fun es => _ ++ es) hr.2.2))
   · cases hh
   · cases hh
   · cases hh with
     | halt hab =>
       simp only [TerminalRel,run,ha,hb]
       exact ⟨True.intro,hab,True.intro⟩

theorem resume_frame (live : Nat → Prop) (hash : Hash) (ops : List Instr)
 (safe : ∀ i ∈ ops, Safe live i) (a b : Terminal Tail Event)
 (h : TerminalRel (Rel live) a b) :
 TerminalRel (Rel live) (Zkc.Realization.InstructionSequence.resume (run (tailStep hash) ops) a)
   (Zkc.Realization.InstructionSequence.resume (run (tailStep hash) ops) b) := by
 by_cases ho : a.outcome = .incomplete
 · have hb : b.outcome = .incomplete := h.1.symm.trans ho
   have hr := continuation_frame live hash ops safe a.state b.state h.2.1
   simp only [Zkc.Realization.InstructionSequence.resume,ho,hb,↓reduceIte,TerminalRel]
   exact ⟨hr.1,hr.2.1,by rw [h.2.2,hr.2.2]⟩
 · have hb : b.outcome ≠ .incomplete := by rw [← h.1]; exact ho
   simpa only [Zkc.Realization.InstructionSequence.resume,ho,hb,↓reduceIte] using h

theorem same_prefix (live : Nat → Prop) (f g : Tail → Terminal Tail Event)
 (hfg : ∀ s, TerminalRel (Rel live) (f s) (g s)) (a : Terminal Tail Event) :
 TerminalRel (Rel live) (Zkc.Realization.InstructionSequence.resume f a) (Zkc.Realization.InstructionSequence.resume g a) := by
 by_cases ho : a.outcome = .incomplete
 · have h := hfg a.state
   simp only [Zkc.Realization.InstructionSequence.resume,ho,↓reduceIte,TerminalRel]
   exact ⟨h.1,h.2.1,by rw [h.2.2]⟩
 · simpa only [Zkc.Realization.InstructionSequence.resume,ho,↓reduceIte] using
     (show TerminalRel (Rel live) a a from ⟨rfl,reflRel live _,rfl⟩)

-- Reusable, applied finite block replacement law. The premise for the continuation
-- is concrete operand support, and the pure block law is proved from actual rows.
theorem block_context (live : Nat → Prop) (hash : Hash)
 (old new pre post : List Instr)
 (block : ∀ s, TerminalRel (Rel live) (run (tailStep hash) old s) (run (tailStep hash) new s))
 (safe : ∀ i ∈ post, Safe live i) (t : Tail) :
 TerminalRel (Rel live) (run (tailStep hash) (pre ++ (old ++ post)) t)
   (run (tailStep hash) (pre ++ (new ++ post)) t) := by
 rw [Zkc.Realization.InstructionSequence.run_append _ (Zkc.Protocols.ScalarBytecode.Execution.no_incomplete_halt hash),
     Zkc.Realization.InstructionSequence.run_append _ (Zkc.Protocols.ScalarBytecode.Execution.no_incomplete_halt hash)]
 apply same_prefix
 intro s
 rw [Zkc.Realization.InstructionSequence.run_append _ (Zkc.Protocols.ScalarBytecode.Execution.no_incomplete_halt hash),
     Zkc.Realization.InstructionSequence.run_append _ (Zkc.Protocols.ScalarBytecode.Execution.no_incomplete_halt hash)]
 exact resume_frame live hash post safe _ _ (block s)

end Zkc.Protocols.ScalarBytecode.Frames
