import ZkcExamples.Construction.SumcheckProof
import ZkcExamples.Executable.SumcheckSourceHonest
import Zkc.Construction.Uniform.DomainHandler
import Mathlib.Algebra.Field.ZMod

/-! Adversarial controls at the migrated all-input endpoint. Each compiler
result is reduced through the checked source equality, preserving exact stops,
message consumption, unread suffixes and query timing. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Tests.SumcheckDomainMigration
open Zkc Zkc.Source Zkc.Source.Structured Zkc.Construction
open Uniform Uniform.DomainAdapter
open ZkcExamples.Construction
open ZkcExamples.Structured SumcheckSourceVerifier SumcheckVerifierLaws
open ZkcExamples.Executable.SumcheckMessages
attribute [local implicit_reducible] CheckedProtocol.signature
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
abbrev F := ZMod 5
abbrev G := ZMod 5

def counted : History F G → StateM Nat F := fun _ => do
  modify (· + 1)
  pure 2

theorem verifier_source (values : List F) (claim : F) (rounds handle : Nat) :
    SumcheckProof.verifier (G := G) values claim rounds handle =
      (((SumcheckVerifierPrelude.admittedRounds SumcheckSourceNormalForms.reduceMaximum childContext
        (some rounds) (some handle) (some claim)).bind
          (fun pc => SumcheckVerifierTerminal.actualOwnedCheck SumcheckSourceViews.unit 1
            (some values) pc.1 pc.2)).bind fun result => .done (result.get .here)).interpret CommonAdapter.project := by
  unfold SumcheckProof.verifier SumcheckProof.process
  have law := verifier_optional (F := F) (G := G) (some values) (some claim) (some rounds) (some handle)
  change SumcheckProof.program.participant F G 1 (SumcheckProof.verifierInputs values claim rounds handle) = _ at law
  rw [law]
  rfl

example (initial : History F G) (proof : Proof F G) (state : Nat) :
    (SumcheckProof.compiledVerifier counted [] 0 3 initial proof).run state =
      ((.stopped .refused, proof), state) := by
  rw [SumcheckProof.compiled_transform counted [] 0 3 77, verifier_source]
  rfl

example (initial : History F G) (tail : Proof F G) (state : Nat) :
    (SumcheckProof.compiledVerifier counted [] 0 1 initial (.field "other" 0 :: tail)).run state =
      ((.stopped .refused, .field "other" 0 :: tail), state) := by
  rw [SumcheckProof.compiled_transform counted [] 0 1 77, verifier_source]
  rfl

example (initial : History F G) (tail : Proof F G) (state : Nat) :
    (SumcheckProof.compiledVerifier counted [] 0 1 initial
      (.field "bls12-381.fr" 0 :: .field "other" 0 :: tail)).run state =
      ((.stopped .refused, .field "other" 0 :: tail), state) := by
  rw [SumcheckProof.compiled_transform counted [] 0 1 77, verifier_source]
  rfl

example (initial : History F G) (tail : Proof F G) (state : Nat) :
    (SumcheckProof.compiledVerifier counted [] 1 1 initial
      (.field "bls12-381.fr" 0 :: .field "bls12-381.fr" 0 :: tail)).run state =
      ((.stopped .reject, tail), state) := by
  rw [SumcheckProof.compiled_transform counted [] 1 1 77, verifier_source]
  simp [SumcheckVerifierPrelude.admittedRounds, SumcheckVerifierPrelude.pendingRounds,
    SumcheckSourceNormalForms.reduceMaximum, SumcheckVerifierLaws.roundPlain, PIR.repeatN,
    PIR.Process.bind, PIR.Process.interpret, CommonAdapter.project, transform]
  rfl

def recorded : History F G → StateM (List (History F G)) F := fun history => do
  modify (· ++ [history])
  pure 2

-- The oracle sees low/high/draw before the subsequent delivery is absorbed.
example (initial : History F G) (tail : Proof F G) :
    (DomainAdapter.runK SourceProcess.legacyOrigin initial recorded
      (ZkcExamples.Executable.SumcheckSourceHonest.viewRound 77 (([], (0 : F)), []))
      (.field "bls12-381.fr" 0 :: .field "bls12-381.fr" 0 :: tail)
      (fun result unread => pure (.returned (readbackHistory SourceProcess.legacyOrigin result.2), unread))).run [] =
    ((.returned (some (ZkcExamples.Executable.SumcheckSourceHonest.transcript.delivered [] 0 0 2)), tail),
      [ZkcExamples.Executable.SumcheckSourceHonest.transcript.drawn initial 0 0]) := by
  simp [ZkcExamples.Executable.SumcheckSourceHonest.viewRound,
    ZkcExamples.Executable.SumcheckSourceHonest.transcript,
    roundPresent, PIR.Process.interpret, CommonAdapter.project, PIR.Process.bind, SourceProcess.sourceView,
    SourceProcess.receive, SourceProcess.query, SourceProcess.send, DomainAdapter.runK,
    DomainAdapter.query, readbackHistory, readbackEvent, readbackPayload, Payload.ofValue,
    Value.decode, Domain.drawRequest, Transcript.drawn, Transcript.delivered, recorded,
    List.append_assoc, SourceProcess.legacyOrigin]
  rfl

end Tests.SumcheckDomainMigration
