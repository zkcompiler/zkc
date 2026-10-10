import Zkc.Protocols.ScalarBytecode.Endpoint.Execution

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

namespace Zkc.Protocols.ScalarBytecode.OneRound.Source
open Zkc.Realization.InstructionSequence Zkc.Semantics.OperationContract Zkc.Realization.ByteEncoding Zkc.Semantics.Locality Zkc.Protocols.ScalarBytecode.Execution Zkc.Protocols.ScalarBytecode.Endpoint

-- Reified from pinned actual OIR; host extraction remains an explicit boundary.
def code : List Instr := [
  ⟨0,.init,.binding,.binding,0,Zkc.Realization.ByteEncoding.utf8 "sha256:af01e27b6cf7a6128d5ae54ed3f6415e3eb1212786b6b29ad6dda8ed06b758c9","",0⟩,
  ⟨1,.absorb,.binding,.binding,0,[],"",2⟩,
  ⟨2,.read,.binding,.binding,2305843009213697249,[],"g1_0",5⟩,
  ⟨3,.absorb,.reg 5,.binding,0,[],"",6⟩,
  ⟨4,.read,.binding,.binding,2305843009213697249,[],"g1_1",9⟩,
  ⟨5,.absorb,.reg 9,.binding,0,[],"",10⟩,
  ⟨6,.read,.binding,.binding,2305843009213697249,[],"g1_2",13⟩,
  ⟨7,.absorb,.reg 13,.binding,0,[],"",14⟩,
  ⟨8,.add,.reg 5,.reg 5,0,[],"",16⟩,
  ⟨9,.add,.reg 16,.reg 9,0,[],"",18⟩,
  ⟨10,.add,.reg 18,.reg 13,0,[],"",20⟩,
  ⟨11,.check,.reg 20,.binding,0,[],"round1",22⟩,
  ⟨12,.draw,.binding,.binding,0,Zkc.Realization.ByteEncoding.utf8 "r16.sumcheck.c1","",25⟩,
  ⟨13,.mul,.reg 9,.reg 25,0,[],"",26⟩,
  ⟨14,.mul,.reg 25,.reg 25,0,[],"",28⟩,
  ⟨15,.mul,.reg 13,.reg 28,0,[],"",30⟩,
  ⟨16,.add,.reg 26,.reg 30,0,[],"",32⟩,
  ⟨17,.add,.reg 5,.reg 32,0,[],"",34⟩,
  ⟨18,.add,.reg 25,.reg 25,0,[],"",36⟩,
  ⟨19,.check,.reg 34,.reg 36,0,[],"final",38⟩,
  ⟨20,.expectEnd,.binding,.binding,0,[],"",40⟩,
  ⟨21,.accept,.binding,.binding,0,[],"",42⟩]
def pre := code.take 13
def body := (code.drop 13).take 5
def post := code.drop 18
def sourceId : String := "sha256:af01e27b6cf7a6128d5ae54ed3f6415e3eb1212786b6b29ad6dda8ed06b758c9"
def artifactId : String := "571687f8e9de4f8f100792c21e486db9f17b7d4ffb18d54450ebe379f2761e67"
def inputRegs : List Nat := [5,9,13,25]
def exportReg : Nat := 34
theorem split_code : code = pre ++ (body ++ post) := rfl

def initial (claim : Nat) (bs : Bytes) : World Bytes :=
  ⟨⟨⟨"r22","r17-n1",1⟩,⟨fun _ => 0,[],claim⟩,0,0,[]⟩,bs⟩

end Zkc.Protocols.ScalarBytecode.OneRound.Source
