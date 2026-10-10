import Zkc.Protocols.ScalarBytecode.Suppliers.Contracts
import Zkc.Protocols.ScalarBytecode.Frames

set_option autoImplicit false

namespace Zkc.Protocols.ScalarBytecode.Endpoint
open Zkc.Realization.InstructionSequence Zkc.Semantics.OperationContract Zkc.Realization.ByteEncoding Zkc.Semantics.Locality Zkc.Protocols.ScalarBytecode.Execution Zkc.Protocols.ScalarBytecode.Suppliers

def LocalRel (live : Nat → Prop) (a b : Local) : Prop :=
  a.subject = b.subject ∧ a.offset = b.offset ∧ Zkc.Protocols.ScalarBytecode.Frames.CoreRel live a.core b.core

def OpenRel {S T : Type} (live : Nat → Prop) (R : S → T → Prop)
    (a : World S) (b : World T) : Prop := LocalRel live a.verifier b.verifier ∧ R a.external b.external

theorem local_refl (live : Nat → Prop) (v : Local) : LocalRel live v v :=
  ⟨rfl,rfl,rfl,rfl,fun _ _ => rfl⟩

def localFinish (i : Instr) (input : Input i.op) (a : Local) {r : Request sig}
    (e : Reply sig r × Core × Nat × List Event) : Step Local Event :=
  let t : Local := {a with
    core := e.2.1
    offset := a.offset + e.2.2.1
    pc := a.pc + 1
    history := a.history ++ [⟨⟨a.subject,i.site⟩,i.op,observed i.op input⟩]}
  match e.1 with
  | .reject why => .halt (.reject why) t e.2.2.2
  | .unavailable why => .halt (.unavailable why) t e.2.2.2
  | .ok value =>
    let u := {t with core := put t.core i.dest value}
    if i.op = .accept then .halt .accept u e.2.2.2 else .next u e.2.2.2

theorem update_finish (hash : Hash) (i : Instr) (input : Input i.op) (a : Local) :
    update hash i input a = localFinish i input a
      (effect hash (request i a.core) a.core (inputBytes i.op input)) := by
  unfold update localFinish
  generalize effect hash (request i a.core) a.core (inputBytes i.op input) = e
  rcases e with ⟨reply,core,n,events⟩
  cases reply <;> rfl

theorem update_frame (live : Nat → Prop) (hash : Hash) (i : Instr)
    (hi : Zkc.Protocols.ScalarBytecode.Frames.Safe live i) (a b : Local) (h : LocalRel live a b) (input : Input i.op) :
    Lift (LocalRel live) (update hash i input a) (update hash i input b) := by
  have hq := Zkc.Protocols.ScalarBytecode.Frames.request_eq live i a.core b.core h.2.2 hi
  have he := Zkc.Protocols.ScalarBytecode.Frames.effect_rel live hash (request i b.core) a.core b.core (inputBytes i.op input) h.2.2
  rw [update_finish,update_finish]
  rw [hq]
  generalize effect hash (request i b.core) a.core (inputBytes i.op input) = x at he ⊢
  generalize effect hash (request i b.core) b.core (inputBytes i.op input) = y at he ⊢
  rcases x with ⟨xr,xc,xn,xe⟩; rcases y with ⟨yr,yc,yn,ye⟩
  rcases he with ⟨hr,hc,hev⟩
  cases hr
  have hn : xn = yn := congrArg Prod.fst hev
  have hes : xe = ye := congrArg Prod.snd hev
  cases hn; cases hes
  cases xr with
  | reject why => exact .halt ⟨h.1,by rw [h.2.1],hc⟩
  | unavailable why => exact .halt ⟨h.1,by rw [h.2.1],hc⟩
  | ok value =>
    dsimp only [localFinish]
    split <;> constructor <;>
      exact ⟨h.1,by rw [h.2.1],Zkc.Protocols.ScalarBytecode.Frames.put_rel live xc yc _ _ hc⟩

theorem serve_subject {S : Type} (supplier : Supplier S) (i : Instr) (a b : Local)
    (h : a.subject = b.subject) (s : S) : serve supplier i a s = serve supplier i b s := by
  rcases i with ⟨site,op,x,y,n,data,label,dest⟩
  cases op <;> simp [serve,h]

theorem open_frame {S T : Type} {l : Supplier S} {r : Supplier T} {R : S → T → Prop}
    (sup : SupplierRel l r R) (live : Nat → Prop) (hash : Hash) (i : Instr)
    (hi : Zkc.Protocols.ScalarBytecode.Frames.Safe live i) (a : World S) (b : World T) (h : OpenRel live R a b) :
    Lift (OpenRel live R) (openStep hash l i a) (openStep hash r i b) := by
  have hs := serve_related sup i b.verifier a.external b.external h.2
  rw [← serve_subject l i a.verifier b.verifier h.1.1 a.external] at hs
  unfold openStep
  generalize serve l i a.verifier a.external = x at hs ⊢
  generalize serve r i b.verifier b.external = y at hs ⊢
  rcases x with ⟨xa,xs⟩; rcases y with ⟨ya,ys⟩
  rcases hs with ⟨he,hr⟩
  dsimp only at he hr ⊢
  subst ya
  have hh := update_frame live hash i hi a.verifier b.verifier h.1 xa
  cases hl : update hash i xa a.verifier <;> cases ht : update hash i xa b.verifier <;> rw [hl,ht] at hh
  · cases hh with
    | next hab =>
      constructor
      refine ⟨hab,?_⟩
      simp only [eventsOf,h.1.1]
      exact notify_related sup _ _ _ _ hr
  · cases hh
  · cases hh
  · cases hh with
    | halt hab =>
      constructor
      refine ⟨hab,?_⟩
      simp only [eventsOf,h.1.1]
      exact notify_related sup _ _ _ _ hr

theorem open_continuation {S T : Type} {l : Supplier S} {r : Supplier T} {R : S → T → Prop}
    (sup : SupplierRel l r R) (live : Nat → Prop) (hash : Hash) (ops : List Instr)
    (safe : ∀ i ∈ ops, Zkc.Protocols.ScalarBytecode.Frames.Safe live i) (a : World S) (b : World T) (h : OpenRel live R a b) :
    TerminalRel (OpenRel live R) (run (openStep hash l) ops a) (run (openStep hash r) ops b) := by
  induction ops generalizing a b with
  | nil => exact ⟨rfl,h,rfl⟩
  | cons i ops ih =>
    have hh := open_frame sup live hash i (safe i (by simp)) a b h
    cases hl : openStep hash l i a <;> cases hr : openStep hash r i b <;> rw [hl,hr] at hh
    · cases hh with
      | next hab =>
        have ht := ih (fun j hj => safe j (by simp [hj])) _ _ hab
        simpa only [TerminalRel,run,hl,hr] using
          And.intro ht.1 (And.intro ht.2.1 (congrArg (fun es => _ ++ es) ht.2.2))
    · cases hh
    · cases hh
    · cases hh with
      | halt hab =>
        simp only [TerminalRel,run,hl,hr]
        exact ⟨True.intro,hab,True.intro⟩

theorem update_no_incomplete (hash : Hash) (i : Instr) (input : Input i.op)
    (s t : Local) (es : List Event) : update hash i input s ≠ .halt .incomplete t es := by
  unfold update
  generalize effect hash (request i s.core) s.core (inputBytes i.op input) = e
  rcases e with ⟨reply,core,n,events⟩
  cases reply with
  | reject why => simp
  | unavailable why => simp
  | ok value => dsimp only; split <;> simp

theorem open_no_incomplete {S : Type} (hash : Hash) (supplier : Supplier S)
    (i : Instr) (s t : World S) (es : List Event) :
    openStep hash supplier i s ≠ .halt .incomplete t es := by
  unfold openStep
  dsimp only
  cases hu : update hash i (serve supplier i s.verifier s.external).1 s.verifier with
  | next v events => simp [mapStep]
  | halt x v events =>
    have hx : x ≠ .incomplete := by
      intro he; subst x
      exact update_no_incomplete hash i _ _ _ _ hu
    simp [mapStep,hx]

theorem resume_open {S T : Type} {l : Supplier S} {r : Supplier T} {R : S → T → Prop}
    (sup : SupplierRel l r R) (live : Nat → Prop) (hash : Hash) (ops : List Instr)
    (safe : ∀ i ∈ ops, Zkc.Protocols.ScalarBytecode.Frames.Safe live i) (a : Terminal (World S) Event) (b : Terminal (World T) Event)
    (h : TerminalRel (OpenRel live R) a b) :
    TerminalRel (OpenRel live R)
      (Zkc.Realization.InstructionSequence.resume (run (openStep hash l) ops) a) (Zkc.Realization.InstructionSequence.resume (run (openStep hash r) ops) b) := by
  by_cases ho : a.outcome = .incomplete
  · have hb : b.outcome = .incomplete := h.1.symm.trans ho
    have hr := open_continuation sup live hash ops safe a.state b.state h.2.1
    simp only [Zkc.Realization.InstructionSequence.resume,ho,hb,↓reduceIte,TerminalRel]
    exact ⟨hr.1,hr.2.1,by rw [h.2.2,hr.2.2]⟩
  · have hb : b.outcome ≠ .incomplete := by rw [← h.1]; exact ho
    simpa only [Zkc.Realization.InstructionSequence.resume,ho,hb,↓reduceIte] using h

theorem open_same_prefix {S : Type} (live : Nat → Prop)
    (f g : World S → Terminal (World S) Event)
    (hfg : ∀ s, TerminalRel (OpenRel live Eq) (f s) (g s)) (a : Terminal (World S) Event) :
    TerminalRel (OpenRel live Eq) (Zkc.Realization.InstructionSequence.resume f a) (Zkc.Realization.InstructionSequence.resume g a) := by
  by_cases ho : a.outcome = .incomplete
  · have h := hfg a.state
    simp only [Zkc.Realization.InstructionSequence.resume,ho,↓reduceIte,TerminalRel]
    exact ⟨h.1,h.2.1,by rw [h.2.2]⟩
  · simpa only [Zkc.Realization.InstructionSequence.resume,ho,↓reduceIte] using
      (show TerminalRel (OpenRel live Eq) a a from ⟨rfl,⟨local_refl live _,rfl⟩,rfl⟩)

/-- Actual opcode-specific frame checking suffices for the shared suffix;
    the prefix and deterministic external strategy are arbitrary. -/
theorem open_block_context {S : Type} (supplier : Supplier S) (live : Nat → Prop) (hash : Hash)
    (old new pre post : List Instr)
    (block : ∀ s, TerminalRel (OpenRel live Eq)
      (run (openStep hash supplier) old s) (run (openStep hash supplier) new s))
    (safe : ∀ i ∈ post, Zkc.Protocols.ScalarBytecode.Frames.Safe live i) (s : World S) :
    TerminalRel (OpenRel live Eq)
      (run (openStep hash supplier) (pre ++ (old ++ post)) s)
      (run (openStep hash supplier) (pre ++ (new ++ post)) s) := by
  have hn := fun i s es t => open_no_incomplete hash supplier i s t es
  rw [Zkc.Realization.InstructionSequence.run_append _ hn,Zkc.Realization.InstructionSequence.run_append _ hn]
  apply open_same_prefix
  intro t
  rw [Zkc.Realization.InstructionSequence.run_append _ hn,Zkc.Realization.InstructionSequence.run_append _ hn]
  exact resume_open (supplier_refl supplier) live hash post safe _ _ (block t)

/-- A stronger register relation may be weakened at an explicit observer edge. -/
theorem weaken {S : Type} (small large : Nat → Prop)
    (included : ∀ n, small n → large n)
    {a b : Terminal (World S) Event}
    (h : TerminalRel (OpenRel large Eq) a b) :
    TerminalRel (OpenRel small Eq) a b := by
  rcases h with ⟨ho,⟨⟨hp,hf,hprov,hbind,hregs⟩,hex⟩,hev⟩
  exact ⟨ho,⟨⟨hp,hf,hprov,hbind,fun n hn => hregs n (included n hn)⟩,hex⟩,hev⟩

theorem terminal_trans {S : Type} (live : Nat → Prop)
    {a b c : Terminal (World S) Event}
    (hab : TerminalRel (OpenRel live Eq) a b)
    (hbc : TerminalRel (OpenRel live Eq) b c) :
    TerminalRel (OpenRel live Eq) a c := by
  rcases hab with ⟨ho,⟨⟨hp,hf,hprov,hbind,hregs⟩,hex⟩,hev⟩
  rcases hbc with ⟨ho',⟨⟨hp',hf',hprov',hbind',hregs'⟩,hex'⟩,hev'⟩
  exact ⟨ho.trans ho',⟨⟨hp.trans hp',hf.trans hf',hprov.trans hprov',
    hbind.trans hbind',fun n hn => (hregs n hn).trans (hregs' n hn)⟩,
    hex.trans hex'⟩,hev.trans hev'⟩


theorem encapsulate_context {S : Type} (hash : Hash) (supplier : Supplier S)
    (live : Nat → Prop) (body pre post : List Instr) (publish : World S → World S)
    (block : ∀ g, TerminalRel (OpenRel live Eq)
      (run (openStep hash supplier) body g) ⟨.incomplete,publish g,[]⟩)
    (safe : ∀ i ∈ post, Zkc.Protocols.ScalarBytecode.Frames.Safe live i) (g : World S) :
    TerminalRel (OpenRel live Eq)
      (run (openStep hash supplier) (pre ++ (body ++ post)) g)
      (Zkc.Realization.InstructionSequence.resume (fun s => run (openStep hash supplier) post (publish s))
        (run (openStep hash supplier) pre g)) := by
  rw [Zkc.Realization.InstructionSequence.run_append _ (fun i s es t => open_no_incomplete hash supplier i s t es)]
  apply open_same_prefix
  intro s
  rw [Zkc.Realization.InstructionSequence.run_append _ (fun i s es t => open_no_incomplete hash supplier i s t es)]
  simpa only [Zkc.Realization.InstructionSequence.resume,if_true,List.nil_append] using
    resume_open (supplier_refl supplier) live hash post safe _ _ (block s)


end Zkc.Protocols.ScalarBytecode.Endpoint
