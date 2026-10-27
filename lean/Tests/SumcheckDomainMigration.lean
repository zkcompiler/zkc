import ZkcExamples.Construction.SumcheckProof
import ZkcExamples.Construction.SumcheckDomainControls
import Zkc.Construction.Uniform.DomainHandler
import Mathlib.Algebra.Field.ZMod

/-! Concrete adversarial controls for the checked actual Sumcheck transition.
These distinguish message consumption, query timing and transcript delivery. -/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 800000
namespace Tests.SumcheckDomainMigration
open Zkc Zkc.Source Zkc.Source.Structured Zkc.Construction
open Zkc.Construction.Uniform.DomainAdapter
open ZkcExamples.Construction.SumcheckDomainConnection
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
abbrev F := ZMod 5
abbrev G := ZMod 5

def counted : History F G → StateM Nat F := fun _ => do
  modify (· + 1)
  pure 2

-- Excess rounds stop before reading an adversarial proof or touching the oracle.
example (initial : History F G) (proof : Proof F G) (state : Nat) :
    (retained counted [] 0 3 initial proof).run state = ((.stopped .refused, proof), state) := by
  rw [retained_root]
  simp [rootProcess, runK]
  rfl

-- A wrong first domain leaves the entire proof unread and makes no query.
example (initial : History F G) (tail : Proof F G) (state : Nat) :
    (retained counted [] 0 1 initial (.field "other" 0 :: tail)).run state =
      ((.stopped .refused, .field "other" 0 :: tail), state) := by
  rw [retained_root]
  simp [rootProcess, reduce, roundState, PIR.Process.bind, runK, Value.decode]
  rfl

-- The accepted first message is consumed; the wrong second head is retained.
example (initial : History F G) (tail : Proof F G) (state : Nat) :
    (retained counted [] 0 1 initial
      (.field "bls12-381.fr" 0 :: .field "other" 0 :: tail)).run state =
      ((.stopped .refused, .field "other" 0 :: tail), state) := by
  rw [retained_root]
  simp [rootProcess, reduce, roundState, PIR.Process.bind, runK, Value.decode]
  rfl

-- A failed sum guard consumes both messages and stops before the draw.
example (initial : History F G) (tail : Proof F G) (state : Nat) :
    (retained counted [] 1 1 initial
      (.field "bls12-381.fr" 0 :: .field "bls12-381.fr" 0 :: tail)).run state =
      ((.stopped .reject, tail), state) := by
  rw [retained_root]
  simp [rootProcess, reduce, roundState, PIR.Process.bind, runK, Value.decode]
  rfl

def recorded : History F G → StateM (List (History F G)) F := fun history => do
  modify (· ++ [history])
  pure 2

-- The old oracle sees low/high/query, before delivery. The carried transcript
-- additionally absorbs delivery; the unread suffix is retained verbatim.
example (initial : History F G) (tail : Proof F G) :
    (scalarRoundK recorded [] 0 initial
      (.field "bls12-381.fr" 0 :: .field "bls12-381.fr" 0 :: tail)
      (fun _ _ history unread => pure (.returned history, unread))).run [] =
      ((.returned (initial ++
        [.message (staticOrigin lowTemplate) (.field "bls12-381.fr" 0),
          .message (staticOrigin highTemplate) (.field "bls12-381.fr" 0),
          .challenge (staticOrigin drawTemplate),
          .message (staticOrigin deliveryTemplate) (.field "bls12-381.fr" 2)]), tail),
        [initial ++ [.message (staticOrigin lowTemplate) (.field "bls12-381.fr" 0),
          .message (staticOrigin highTemplate) (.field "bls12-381.fr" 0),
          .challenge (staticOrigin drawTemplate)]]) := by
  simp [scalarRoundK, recorded, List.append_assoc]
  rfl

end Tests.SumcheckDomainMigration
