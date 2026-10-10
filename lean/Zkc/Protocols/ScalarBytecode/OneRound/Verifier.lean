import Zkc.Protocols.ScalarBytecode.OneRound.Source

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

namespace Zkc.Protocols.ScalarBytecode.OneRound.Verifier
open Zkc.Realization.InstructionSequence Zkc.Semantics.OperationContract Zkc.Realization.ByteEncoding Zkc.Semantics.Locality Zkc.Protocols.ScalarBytecode.Execution Zkc.Protocols.ScalarBytecode.Endpoint

def absorb (hash : Hash) (state : Bytes) (v : Nat) :=
  hash (state ++ [⟨0,by decide⟩] ++ Zkc.Protocols.ScalarBytecode.Codec.enc v)
def prefixState (hash : Hash) (claim a b c : Nat) :=
  absorb hash (absorb hash (absorb hash (absorb hash
    (hash (Zkc.Realization.ByteEncoding.utf8 Zkc.Protocols.ScalarBytecode.OneRound.Source.sourceId)) claim) a) b) c
def digest (hash : Hash) (claim a b c : Nat) :=
  hash (prefixState hash claim a b c ++ [⟨1,by decide⟩] ++ Zkc.Realization.ByteEncoding.utf8 "r16.sumcheck.c1")
def support : Nat := Zkc.Protocols.ScalarBytecode.Parameters.challengeBound
def challenge (hash : Hash) (claim a b c : Nat) :=
  Zkc.Realization.ByteEncoding.valueBE ((digest hash claim a b c).take 8) % support
def boundary (a b c : Nat) := (((a+a)%Zkc.Protocols.ScalarBytecode.Parameters.modulus+b)%Zkc.Protocols.ScalarBytecode.Parameters.modulus+c)%Zkc.Protocols.ScalarBytecode.Parameters.modulus
def value (a b c r : Nat) :=
  (a+((b*r)%Zkc.Protocols.ScalarBytecode.Parameters.modulus+(c*((r*r)%Zkc.Protocols.ScalarBytecode.Parameters.modulus))%Zkc.Protocols.ScalarBytecode.Parameters.modulus)%Zkc.Protocols.ScalarBytecode.Parameters.modulus)%Zkc.Protocols.ScalarBytecode.Parameters.modulus
def verdict (claim a b c r : Nat) : Exit :=
  if boundary a b c = claim then
    if value a b c r = (r+r)%Zkc.Protocols.ScalarBytecode.Parameters.modulus then .accept else .reject "check_failure"
  else .reject "check_failure"
def flat (hash : Hash) (claim a b c : Nat) :=
  run (tailStep hash) Zkc.Protocols.ScalarBytecode.OneRound.Source.code
    ⟨Zkc.Protocols.ScalarBytecode.Codec.wire [a,b,c],0,⟨fun _ => 0,[],claim⟩⟩

theorem challenge_support (hash : Hash) (claim a b c : Nat) :
    challenge hash claim a b c < support := Nat.mod_lt _ (by decide)

theorem flat_verdict (hash : Hash) (claim a b c : Nat)
    (ha : a < Zkc.Protocols.ScalarBytecode.Parameters.modulus) (hb : b < Zkc.Protocols.ScalarBytecode.Parameters.modulus) (hc : c < Zkc.Protocols.ScalarBytecode.Parameters.modulus) :
    (flat hash claim a b c).outcome =
      verdict claim a b c (challenge hash claim a b c) := by
  have ha8 : a < 256^8 := Nat.lt_trans ha (by decide : Zkc.Protocols.ScalarBytecode.Parameters.modulus < 256^8)
  have hb8 : b < 256^8 := Nat.lt_trans hb (by decide : Zkc.Protocols.ScalarBytecode.Parameters.modulus < 256^8)
  have hc8 : c < 256^8 := Nat.lt_trans hc (by decide : Zkc.Protocols.ScalarBytecode.Parameters.modulus < 256^8)
  simp only [Zkc.Protocols.ScalarBytecode.Parameters.modulus] at ha hb hc
  by_cases h : (a+a+b+c)%Zkc.Protocols.ScalarBytecode.Parameters.modulus = claim <;>
    by_cases hf : value a b c (challenge hash claim a b c) =
      (challenge hash claim a b c + challenge hash claim a b c)%Zkc.Protocols.ScalarBytecode.Parameters.modulus <;>
    simp [value,challenge,digest,prefixState,absorb,Zkc.Protocols.ScalarBytecode.Codec.enc,Zkc.Protocols.ScalarBytecode.OneRound.Source.sourceId,support] at hf <;>
    simp [h,hf,flat,Zkc.Protocols.ScalarBytecode.OneRound.Source.code,run,tailStep,tailHandler,request,effect,Zkc.Protocols.ScalarBytecode.Execution.get,put,
    Zkc.Protocols.ScalarBytecode.Codec.wire,Zkc.Protocols.ScalarBytecode.Codec.enc,List.take_of_length_le,Zkc.Realization.ByteEncoding.be_length,Zkc.Realization.ByteEncoding.value_be 8 a ha8,Zkc.Realization.ByteEncoding.value_be 8 b hb8,Zkc.Realization.ByteEncoding.value_be 8 c hc8,
    ha,hb,hc,verdict,boundary,value,challenge,digest,prefixState,absorb,Zkc.Protocols.ScalarBytecode.OneRound.Source.sourceId,
    support]

end Zkc.Protocols.ScalarBytecode.OneRound.Verifier
