module

public import Zkc.Formal.Interactive.EmptyReduction
public import Zkc.Formal.Interactive.ScalarEquality
public import Zkc.Formal.Interactive.SingletonTable
public import Zkc.Formal.Interactive.Experiment

@[expose] public section
namespace Zkc.Formal.Interactive.Sumcheck.EmptySumcheck
open Core

-- This file passes between the meaning of a program and its tables by definitional unfolding.
unseal Zkc.Core.fnMeaning Zkc.Core.roleMeaning Zkc.Core.protocolMeaning

variable {V : Vocabulary} (t : V.Ty)

abbrev header (k : Key) (shape : Shape V) : ProtocolHeader V :=
  ⟨k,2,[⟨.seq t (some 1),[0,1]⟩,⟨t,[0,1]⟩],[],shape⟩
abbrev reduction (k : Key) (shape : Shape V) := EmptyReduction.header k (.seq t (some 1)) t 0 shape
abbrev comparison := ScalarEquality.signature t

variable (equal : V.RowKey) (typed : V.row equal = some (comparison t))
variable {hs : Headers V} {red eval : Key} {sh : Shape V}
variable (callee : Member hs.protocols (reduction t red sh))
variable (evaluate : Member hs.fns (SingletonTable.header t eval))
local macro "varAt " n:term:max : term => `(⟨$n, rfl⟩)

def body (k : Key) (shape : Shape V) : Prot V hs (header t k shape) (.cons 0 (.cons 1 .nil)) :=
  .op ⟨0⟩ (.compute [0,1] (.owned (.makeSeq t 0)) [] rfl (by simp)) .nil (.cons 2 .nil) <|
  .op ⟨1⟩ (.apply callee [0,1] (by decide) rfl
        [⟨.seq t (some 1),[0,1]⟩,⟨.seq t (some 0),[0,1]⟩,⟨t,[0,1]⟩] (by
          change (_ = _ ∧ ∀ r, r ∈ [0] → r ∈ [0,1]) ∧
             (_ = _ ∧ ∀ r, r ∈ [0,1] → r ∈ [0,1]) ∧ (_ = _ ∧ ∀ r, r ∈ [0,1] → r ∈ [0,1]) ∧ True
          simp)) (.cons (varAt 0) (.cons (varAt 2) (.cons (varAt 1) .nil))) (.cons 3 (.cons 4 (.cons 5 .nil))) <|
  .op ⟨2⟩ (.compute [1] (.call evaluate) [⟨.seq t (some 1),[0,1]⟩,⟨.seq t (some 0),[0,1]⟩]
        rfl (by intro a ha; simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
                rcases ha with rfl | rfl <;> simp))
    (.cons (varAt 0) (.cons (varAt 3) .nil)) (.cons 6 .nil) <|
  .op ⟨3⟩ (.compute [1] (.row equal (comparison t) typed) [⟨t,[0,1]⟩,⟨t,[1]⟩] rfl
      (by intro a ha; simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
          rcases ha with rfl | rfl <;> simp))
    (.cons (varAt 4) (.cons (varAt 6) .nil)) (.cons 7 .nil) <|
  .guard ⟨4⟩ [1] (varAt 7) (by simp) .reject (.ret .nil)

def witness (k : Key) (shape : Shape V) : ProtocolEntry.Body hs (header t k shape) :=
  ⟨.cons 0 (.cons 1 .nil),body t equal typed callee evaluate k shape,rfl⟩

/-- The model interprets the source field equality at its actual vocabulary row. -/
abbrev Equality := ScalarEquality.Law t equal typed

def Law (k : Key) (shape : Shape V) (run : ProtocolEntry.RoleMeaning (header t k shape) 1) : Prop :=
  ∀ (M : Model V) [DecidableEq (M.Val t)], Equality t equal typed M →
    ∀ path (v claim : M.Val t), run M path
      (.cons (hide M 1 ⟨.seq t (some 1),[0,1]⟩ [v]) (.cons (hide M 1 ⟨t,[0,1]⟩ claim) .nil)) =
        if claim = v then .done .nil else .halt (.declared .reject ⟨path,⟨4⟩⟩)

set_option maxRecDepth 4096 in
theorem checked (k : Key) (shape : Shape V) (ds : Defs V hs)
    (reduces : EmptyReduction.Law red (.seq t (some 1)) t 0 sh (fun M => Defs.rTable M ds _ callee 1))
    (evaluates : SingletonTable.Law t eval (fun M => Defs.fnTable M ds _ evaluate)) :
    Law t equal typed k shape ((witness t equal typed callee evaluate k shape).meaning ds 1) := by
  intro M eq equality path v claim
  let hidden := nothing M (r := 1) (a := ⟨.seq t (some 1),[0]⟩) (by simp)
  have redValue := reduces M (path ++ [.application ⟨1⟩]) hidden [] claim
  have evalValue := evaluates M v
  have equalValue := equality claim v
  dsimp only at redValue evalValue
  change ((mapR M _ (Defs.rTable M ds _ callee 1 (path ++ [.application ⟨1⟩])
      (.cons hidden (.cons (hide M 1 ⟨.seq t (some 0),[0,1]⟩ []) (.cons (hide M 1 ⟨t,[0,1]⟩ claim) .nil))))).map _).bind _ = _
  rw [redValue]
  change ((liftLocal id (Defs.fnTable M ds _ evaluate (.cons [v] (.cons [] .nil)))).map _).bind _ = _
  rw [evalValue]
  have rowValue : localOp M (Defs.fnTable M ds) (.row equal (comparison t) typed)
      (.cons claim (.cons v .nil)) = .done (.cons (decide (claim = v)) .nil) := by
    simp only [localOp, equalValue]
  change ((liftLocal id (localOp M (Defs.fnTable M ds) (.row equal (comparison t) typed)
    (.cons claim (.cons v .nil)))).map _).bind _ = _
  rw [rowValue]
  change (bif decide (claim = v) then Process.done HList.nil else
    .halt (Stop.declared .reject ⟨path,⟨4⟩⟩)).bind _ = _
  by_cases h : claim = v <;> simp [h, Process.bind] <;> rfl

/-- Compose both earlier certificates at their references in the caller's own definition prefix. -/
def certify (p : Core.Typed V) (caller reduceKey evaluateKey : Key) (free : Ty.isLinear V t = false) :
    Option ((sh : Shape V) × (ref : Member p.headers.protocols (header t caller sh)) ×'
      Law t equal typed caller sh (fun M => roleMeaning M p ref 1)) := do
  let ⟨shape,root⟩ ← ProtocolEntry.locatePorts p.headers caller 2 [⟨.seq t (some 1),[0,1]⟩,⟨t,[0,1]⟩] []
  let entry := p.defs.protocolEntry p.distinct root
  let before : Core.Typed V := ⟨entry.earlier,entry.definitions,entry.distinct⟩
  let ⟨_,callee,redLaw⟩ ← EmptyReduction.certify before reduceKey (.seq t (some 1)) t 0
  let ⟨evaluate,evalLaw⟩ ← (SingletonTable.readback t free evaluateKey).locate
    entry.definitions (List.nodup_append.mp entry.distinct).1
  let ⟨holds⟩ ← entry.recognize 1 (witness t equal typed callee evaluate caller shape)
    (Law t equal typed caller shape) (checked t equal typed callee evaluate caller shape entry.definitions redLaw evalLaw)
  return ⟨shape,root,holds⟩

/-- A wrong public claim has zero probability of acceptance for every interactive service. -/
theorem falseClaim {k : Key} {shape : Shape V} {run : ProtocolEntry.RoleMeaning (header t k shape) 1}
    (law : Law t equal typed k shape run) (M : Model V) [DecidableEq (M.Val t)] (equality : Equality t equal typed M)
    {σ : Type} (K : Experiment (RSig M) σ) (s : σ) (path : List Frame) (v claim : M.Val t) (incorrect : claim ≠ v) :
    K.probability (run M path (.cons (hide M 1 ⟨.seq t (some 1),[0,1]⟩ [v])
      (.cons (hide M 1 ⟨t,[0,1]⟩ claim) .nil))) s (fun _ _ => true) = 0 := by
  simp only [law M equality path v claim, incorrect, ↓reduceIte]
  rfl

#print axioms certify
#print axioms falseClaim
end Zkc.Formal.Interactive.Sumcheck.EmptySumcheck
