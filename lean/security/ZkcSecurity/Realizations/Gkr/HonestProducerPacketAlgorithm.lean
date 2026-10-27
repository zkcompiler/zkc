module

meta import Lean.Elab.Command
meta import Lean.Meta.Eqns

public import ZkcExamples.Structured.GkrSourceCallbacks

@[expose] public section

/-! Complete coefficient packet stream computed by the actual producer. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace ZkcSecurity.Realizations.Gkr.HonestProducerPackets
open Zkc Source Structured
open Zkc.Polynomial Zkc.Polynomial.Multilinear
open ZkcExamples.Structured SumcheckVerifierHelpers GkrSourceCallbacks

variable {F G : Type}

def sendTail (ctx : ProtocolContext) : List F → PIR.Process (participantInterface F G) Unit
  | [] => .done ()
  | value :: rest => .call (.send (ty := .field "bls12-381.fr")
      (lineCoefficientSite ctx) (ctx.roles 1) value) fun _ => sendTail ctx rest

def tail [Zero F] (line : List F) (start count : Nat) : List F :=
  List.ofFn (fun i : Fin count => (line)[start + i.val + 1]?.getD 0)

theorem tail_succ [Zero F] (line : List F) (start count : Nat) :
    tail line start (count + 1) = (line)[start + 1]?.getD 0 :: tail line (start + 1) count := by
  rw [tail, List.ofFn_succ]
  simp only [Fin.val_zero, Nat.add_zero]
  congr 1
  apply congrArg List.ofFn
  funext i
  simp only [Fin.val_succ]
  congr 3; omega

theorem reconstruct [Zero F] (line : List F) (count : Nat) (size : line.length = count + 1) :
    (line)[0]?.getD 0 :: tail line 0 count = line := by
  apply List.ext_getElem
  · simp [tail, size]
  · intro i hi hj
    cases i with
    | zero => simp [List.getElem?_eq_getElem hj]
    | succ i =>
      simp [tail, List.getElem?_eq_getElem hj]

end ZkcSecurity.Realizations.Gkr.HonestProducerPackets

-- Materialize the unfolding equation in its defining module so joint imports
-- share one stored declaration instead of generating client-local proof copies.
run_cmd Lean.Elab.Command.liftTermElabM do
  discard <| Lean.Meta.getEqnsFor? ``ZkcSecurity.Realizations.Gkr.HonestProducerPackets.sendTail
