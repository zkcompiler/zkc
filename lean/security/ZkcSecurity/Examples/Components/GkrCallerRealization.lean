module

public import ZkcSecurity.Examples.Components.GkrRoundsGateRealization
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum

@[expose] public section

/-! The finite two-layer circuit used by the actual-caller trial. Representation
is closed under every future challenge, independently of verifier messages. -/
namespace ZkcSecurity.Examples.Components.GkrCallerRealization
open Zkc.Source Zkc.Source.Structured Zkc.Polynomial.Multilinear
open GkrRoundsReference GkrRoundsRealization GkrRoundsGateRealization

variable {F : Type} [Field F]

def inputs : List F := [3, 5]
def honestOutputs : List F := [120, 30]
def wrongOutputs : List F := [121, 31]
def stackedAdd : List F := [0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0]
def stackedMul : List F := [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0]

def addTable (rho : F) : Table F 2 :=
  fun bits => if bits 0 then (if bits 1 then rho else 0) else 0
def mulTable (rho : F) : Table F 2 :=
  fun bits => if bits 0 then 0 else (if bits 1 then 1 - rho else 0)
def below : Table F 1 := fun bits => if bits 0 then 15 else 8
def reference (rho : F) : GkrRoundsReference.State F 2 :=
  GkrRoundsLayout.state (addTable rho) (mulTable rho) below below
def raw (rho : F) : RawState F :=
  ⟨[0, 0, 0, rho], [0, 1 - rho, 0, 0], [8, 8, 15, 15], [8, 15, 8, 15]⟩
def honestClaim (rho : F) : F := (1 - rho) * 120 + rho * 30
def wrongClaim (rho : F) : F := (1 - rho) * 121 + rho * 31

theorem concrete_vectors (rho : F) :
    callerVectors 1 (addTable rho) (mulTable rho) below = raw rho := by
  simp [callerVectors, GkrRoundsLayout.encode, List.ofFn_succ, vertex,
    addTable, mulTable, below, raw]

theorem represented (rho : F) : Represents (raw rho) (reference rho) := by
  rw [← concrete_vectors]
  exact concrete_caller 1 _ _ _ (by norm_num [indexLimit])

theorem first_future (rho : F) (challenges : Fin 1 → F) :
    Represents ((raw rho).prefix 1 challenges)
      ((data F).restrictPrefix 1 (reference rho) challenges) :=
  prefix_represents 1 _ _ (represented rho) challenges

theorem all_future (rho : F) (challenges : Fin 2 → F) :
    Represents ((raw rho).prefix 2 challenges)
      ((data F).restrictPrefix 2 (reference rho) challenges) :=
  prefix_represents 2 _ _ (represented rho) challenges

theorem total_eq (rho : F) : total (reference rho) = 120 - 90 * rho := by
  simp [total, booleanSum, half, reference, GkrRoundsLayout.state,
    GkrRoundsLayout.replicate, GkrRoundsLayout.tile, GkrRoundsLayout.leading,
    GkrRoundsLayout.trailing, addTable, mulTable, below,
    Zkc.Protocols.AlgebraicRounds.Gate.value]
  ring

theorem honest_control (rho : F) : honestClaim rho = total (reference rho) := by
  rw [total_eq]
  unfold honestClaim
  ring

theorem wrong_control (rho : F) : wrongClaim rho ≠ total (reference rho) := by
  rw [total_eq]
  have gap : wrongClaim rho = (120 - 90 * rho) + 1 := by unfold wrongClaim; ring
  rw [gap]
  exact fun equality => one_ne_zero (add_left_cancel (equality.trans (add_zero _).symm))

end ZkcSecurity.Examples.Components.GkrCallerRealization
