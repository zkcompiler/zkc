module

public import Zkc.Core.Evidence.ProtocolReadback

@[expose] public section
namespace Zkc.Formal.Interactive.Sumcheck.EmptyReduction
open Core
variable {V : Vocabulary}

def header (key : Key) (state scalar : V.Ty) (prefixSize : Nat) (shape : Shape V) : ProtocolHeader V :=
  let point : V.Ty := .seq scalar (some prefixSize)
  ⟨key,2,[⟨state,[0]⟩,⟨point,[0,1]⟩,⟨scalar,[0,1]⟩],
    [⟨point,[0,1]⟩,⟨scalar,[0,1]⟩,⟨state,[0]⟩],shape⟩

variable (key : Key) (state scalar : V.Ty) (prefixSize : Nat) (shape : Shape V)
local notation "H" => header key state scalar prefixSize shape
local macro "varAt " n:term:max : term => `(⟨$n, rfl⟩)

def body (hs : Headers V) : Prot V hs H (.cons 0 (.cons 1 (.cons 2 .nil))) :=
  .op ⟨0⟩ (.compute [0,1] (.owned (.makeSeq scalar 0)) [] rfl (by simp)) .nil (.cons 3 .nil) <|
  .op ⟨1⟩ (.compute [0,1] (.owned (.seqConcat scalar (some prefixSize) (some 0)))
      [⟨.seq scalar (some prefixSize),[0,1]⟩,⟨.seq scalar (some 0),[0,1]⟩] rfl (by
        intro a h
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl <;> simp)) (.cons (varAt 1) (.cons (varAt 3) .nil)) (.cons 4 .nil) <|
  .op ⟨2⟩ (.narrow [0,1] (fun _ h => h)) (.cons (varAt 4) .nil) (.cons 5 .nil) <|
  .op ⟨3⟩ (.narrow [0,1] (fun _ h => h)) (.cons (varAt 2) .nil) (.cons 6 .nil) <|
  .op ⟨4⟩ (.narrow [0] (fun _ h => h)) (.cons (varAt 0) .nil) (.cons 7 .nil) <|
  .ret (.cons (varAt 5) (.cons (varAt 6) (.cons (varAt 7) .nil)))

def witness (hs : Headers V) : ProtocolEntry.Body hs H :=
  ⟨.cons 0 (.cons 1 (.cons 2 .nil)), body key state scalar prefixSize shape hs, rfl⟩

/-- An empty reduction returns the public prefix and claim immediately at the verifier.
Its private input is represented by precisely what that role holds. -/
def Law (run : ProtocolEntry.RoleMeaning H 1) : Prop :=
  ∀ (M : Model V) path (hidden : RV M 1 ⟨state,[0]⟩) (point : M.Val (.seq scalar (some prefixSize)))
    (claim : M.Val scalar), run M path
      (.cons hidden (.cons (hide M 1 ⟨_,[0,1]⟩ point) (.cons (hide M 1 ⟨_,[0,1]⟩ claim) .nil))) =
    .done (.cons (hide M 1 ⟨_,[0,1]⟩ point) (.cons (hide M 1 ⟨_,[0,1]⟩ claim)
      (.cons (nothing M (r := 1) (a := ⟨state,[0]⟩) (by simp)) .nil)))

theorem empty_value {hs : Headers V} (ds : Defs V hs) :
    Law key state scalar prefixSize shape ((witness key state scalar prefixSize shape hs).meaning ds 1) := by
  intro M path hidden point claim
  let result (xs : List (M.Val scalar)) : HList (RV M 1) (header key state scalar prefixSize shape).outs :=
    .cons (hide M 1 ⟨.seq scalar (some prefixSize),[0,1]⟩ xs)
      (.cons (hide M 1 ⟨scalar,[0,1]⟩ claim) (.cons (nothing M (r := 1) (a := ⟨state,[0]⟩) (by simp)) .nil))
  change Process.done (result (point ++ [])) = Process.done (result point)
  rw [List.append_nil]

/-- Find the emitted reduction in its linked program. The certificate names the actual
protocol reference and states a property of its verifier meaning. -/
def certify (p : Core.Typed V) (k : Key) (state scalar : V.Ty) (prefixSize : Nat) :
    Option ((sh : Shape V) × (ref : Member p.headers.protocols (header k state scalar prefixSize sh)) ×'
      Law k state scalar prefixSize sh (fun M => roleMeaning M p ref 1)) := do
  let point : V.Ty := .seq scalar (some prefixSize)
  let ⟨sh,actual⟩ ← ProtocolEntry.locatePorts p.headers k 2
    [⟨state,[0]⟩,⟨point,[0,1]⟩,⟨scalar,[0,1]⟩] [⟨point,[0,1]⟩,⟨scalar,[0,1]⟩,⟨state,[0]⟩]
  let entry := p.defs.protocolEntry p.distinct actual
  let ⟨holds⟩ ← entry.recognize 1 (witness k state scalar prefixSize sh entry.earlier)
    (Law k state scalar prefixSize sh) (empty_value k state scalar prefixSize sh entry.definitions)
  return ⟨sh,actual,holds⟩

#print axioms empty_value
end Zkc.Formal.Interactive.Sumcheck.EmptyReduction
