module

public import Zkc.Construction.OriginalSimulation
public import Zkc.Construction.DomainCalculations

@[expose] public section

/-! Local construction rules used by artifact proof search. The source and
target are fixed indices of Original.Simulation. In particular a local rule
cannot admit a whole-region equality as a certificate payload. -/
set_option autoImplicit false
namespace Zkc.Construction.ArtifactBinding
open Zkc.Source

variable {carriers : Structured.Carriers} {A B : Type}

theorem fold_done (routing : Original.Routing) (value : A) (state : Original.State carriers) :
    Original.fold routing (.done value) state = .done (value, state) := rfl

/-- A physical frame retains the exact immutable caller capture. This modest
predicate is useful while composing callbacks; stronger live-value predicates
can be supplied to the same proof-search interface. -/
def Captures (captured frame : Domain.Environment carriers) : Prop :=
  frame.take captured.length = captured

theorem captures_append (captured suffix : Domain.Environment carriers) :
    Captures captured (captured ++ suffix) := by
  simp [Captures]

theorem captures_trans {initial captured frame : Domain.Environment carriers}
    (outer : Captures initial captured) (inner : Captures captured frame) :
    Captures initial frame := by
  have length := congrArg List.length outer
  simp only [List.length_take] at length
  have bound : initial.length ≤ captured.length := by omega
  unfold Captures at *
  calc
    frame.take initial.length = (frame.take captured.length).take initial.length := by
      rw [List.take_take, Nat.min_eq_left bound]
    _ = initial := by rw [inner]; exact outer

/-- Read a locally allocated slot without unfolding an arbitrary caller's
immutable capture. The concrete offset is checked by the caller's size law. -/
theorem read_after_capture (captured suffix : Domain.Environment carriers)
    (offset reference : Nat) (size : captured.length = offset)
    (after : offset ≤ reference) :
    (captured ++ suffix)[reference]? = suffix[reference - offset]? := by
  rw [List.getElem?_append_right (by omega), size]

/-- Use a proved one-operation normalization on either side. The source,
target, return relation and frame predicate stay fixed by the conclusion. -/
def transport
    {returns : A → B → Prop}
    {live : PIR.Process (Domain.effects carriers) A → Domain.Environment carriers → Prop}
    {source source' : PIR.Process (Domain.effects carriers) A}
    {target target' : PIR.Process (Domain.effects carriers) B}
    (sourceEquation : source = source') (targetEquation : target = target')
    (derivation : Original.Simulation returns live source' target') :
    Original.Simulation returns live source target := by
  subst source target
  exact derivation

end Zkc.Construction.ArtifactBinding
