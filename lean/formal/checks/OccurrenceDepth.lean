import Zkc.Kernel
import Zkc.Formal.Interactive.RoundFamily
import Zkc.Formal.Written.FiniteModel
open Zkc.Core Zkc.Formal.Written Zkc.Formal.Written.FiniteModel
open Zkc.Formal.Interactive.Sumcheck Zkc.Formal.Interactive.Sumcheck.ReductionRound
namespace OccurrenceDepth

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def claims : Claims Nat := ⟨fun _ => Unit, fun d _ => d, fun _ _ _ => ()⟩
def constant (key n : Nat) (two : Bool) : Definition Standard :=
  .fn ⟨key⟩ (if two then [.nat,.nat] else [.nat]) [.nat] false none Summary.empty
    (.mk (if two then [0,1] else [0]) [.op ⟨1⟩ [2] (.literal .nat [n]) []] [2])
def stored : NamedProgram Standard := ⟨[constant 5 3 false, constant 6 0 true, constant 7 1 true]⟩
noncomputable section
def programBase : Typed Standard := Typed.empty
kernel_ok e5 with h5 ns5 body5 : Elaborated Standard programBase.headers :=
  elaborateDefinition programBase.headers (constant 5 3 false)
def p5 : Typed Standard := programBase.add e5
kernel_ok e6 with h6 ns6 body6 : Elaborated Standard p5.headers :=
  elaborateDefinition p5.headers (constant 6 0 true)
def p6 : Typed Standard := p5.add e6
kernel_ok e7 with h7 ns7 body7 : Elaborated Standard p6.headers :=
  elaborateDefinition p6.headers (constant 7 1 true)
def installed : Typed Standard := p6.add e7
abbrev hs : Headers Standard := ⟨[h7,h6,h5],[]⟩
theorem succeeds : (admit stored ⟨[],[],[],[],[]⟩).isOk := by decide +kernel
theorem readback (a : Admitted Standard) (h : admit stored ⟨[],[],[],[],[]⟩ = .ok a) :
    a.program = installed :=
  admitted_eq_of_elaborated h (.cons e5.eq (.cons e6.eq (.cons e7.eq (.nil _))))
abbrev fns := Defs.fnTable model installed.defs
local instance : DecidableEq (model.Val (.nat : Standard.Ty)) := inferInstanceAs (DecidableEq Nat)
def boundOp : LocalOp Standard hs.fns [.nat] [.nat] := .call (.tail (.tail .head))
def evalZero : LocalOp Standard hs.fns [.nat,.nat] [.nat] := .call (.tail .head)
def evalOne : LocalOp Standard hs.fns [.nat,.nat] [.nat] := .call .head
def members (e : LocalOp Standard hs.fns [.nat,.nat] [.nat]) :
    Members hs .nat .nat .nat .nat := ⟨boundOp,e,boundOp,e⟩

abbrev Law (e : LocalOp Standard hs.fns [.nat,.nat] [.nat]) {ι : Type} (depth : ι → Nat) :=
  RoundInterpretationOn (t := .nat) model fns claims [0,1] 1 (members e) depth

def atOne : Law evalZero (fun _ : Unit => 1) where
  boundary := fun _ => 3
  evaluate := fun _ _ => 0
  ends := fun _ => rfl
  atPoint := fun _ _ => rfl
  roots := by intros; change 0 ≤ 1; decide

def atZero : Law evalOne (fun _ : Unit => 0) where
  boundary := fun _ => 3
  evaluate := fun _ _ => 1
  ends := fun _ => rfl
  atPoint := fun _ _ => rfl
  roots := by intros; change 0 ≤ 1; decide

def result (p : Local (HList model.Val [.nat])) : Nat :=
  (functionResult (t := .nat) (M := model) p).getD 99

theorem firstFailsCross (l : Law evalZero (Fin.val (n := 2))) : False := by
  have b : 3 = l.boundary 0 := congrArg result (l.ends 0)
  have ev (r : Nat) : 0 = l.evaluate 0 r := congrArg result (l.atPoint 0 r)
  have bad := l.roots (0 : Fin 2) () 0 (by rw [← b]; decide)
  change [0,1].countP (fun r : Nat => decide (l.evaluate 0 r = 0)) ≤ 1 at bad
  simp [← ev] at bad

theorem secondFailsCross (l : Law evalOne (Fin.val (n := 2))) : False := by
  have b : 3 = l.boundary 0 := congrArg result (l.ends 0)
  have ev (r : Nat) : 1 = l.evaluate 0 r := congrArg result (l.atPoint 0 r)
  have bad := l.roots (1 : Fin 2) () 0 (by rw [← b]; decide)
  change [0,1].countP (fun r : Nat => decide (l.evaluate 0 r = 1)) ≤ 1 at bad
  simp [← ev] at bad

end
end OccurrenceDepth
