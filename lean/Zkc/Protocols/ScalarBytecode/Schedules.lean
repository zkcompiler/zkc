import Zkc.Protocols.ScalarBytecode.Execution

set_option autoImplicit false

namespace Zkc.Protocols.ScalarBytecode.Schedules
open Zkc.Realization.InstructionSequence Zkc.Realization.ByteEncoding Zkc.Protocols.ScalarBytecode.Execution

def sumcheck : List Instr := [
  ⟨0,.init,.binding,.binding,0,[⟨115,by decide⟩,⟨104,by decide⟩,⟨97,by decide⟩,⟨50,by decide⟩,⟨53,by decide⟩,⟨54,by decide⟩,⟨58,by decide⟩,⟨53,by decide⟩,⟨51,by decide⟩,⟨51,by decide⟩,⟨55,by decide⟩,⟨100,by decide⟩,⟨101,by decide⟩,⟨99,by decide⟩,⟨50,by decide⟩,⟨50,by decide⟩,⟨52,by decide⟩,⟨49,by decide⟩,⟨101,by decide⟩,⟨102,by decide⟩,⟨53,by decide⟩,⟨48,by decide⟩,⟨57,by decide⟩,⟨99,by decide⟩,⟨100,by decide⟩,⟨101,by decide⟩,⟨49,by decide⟩,⟨100,by decide⟩,⟨54,by decide⟩,⟨55,by decide⟩,⟨48,by decide⟩,⟨56,by decide⟩,⟨56,by decide⟩,⟨51,by decide⟩,⟨57,by decide⟩,⟨49,by decide⟩,⟨56,by decide⟩,⟨101,by decide⟩,⟨48,by decide⟩,⟨48,by decide⟩,⟨52,by decide⟩,⟨48,by decide⟩,⟨102,by decide⟩,⟨51,by decide⟩,⟨99,by decide⟩,⟨100,by decide⟩,⟨97,by decide⟩,⟨52,by decide⟩,⟨51,by decide⟩,⟨52,by decide⟩,⟨99,by decide⟩,⟨98,by decide⟩,⟨101,by decide⟩,⟨52,by decide⟩,⟨48,by decide⟩,⟨55,by decide⟩,⟨100,by decide⟩,⟨102,by decide⟩,⟨100,by decide⟩,⟨50,by decide⟩,⟨52,by decide⟩,⟨57,by decide⟩,⟨98,by decide⟩,⟨99,by decide⟩,⟨100,by decide⟩,⟨57,by decide⟩,⟨97,by decide⟩,⟨51,by decide⟩,⟨102,by decide⟩,⟨100,by decide⟩,⟨97,by decide⟩],"",0⟩,
  ⟨1,.absorb,.binding,.binding,0,[],"s",2⟩,
  ⟨2,.read,.binding,.binding,2305843009213697249,[],"g1_0",5⟩,
  ⟨3,.absorb,(.reg 5),.binding,0,[],"g1_0",6⟩,
  ⟨4,.read,.binding,.binding,2305843009213697249,[],"g1_1",9⟩,
  ⟨5,.absorb,(.reg 9),.binding,0,[],"g1_1",10⟩,
  ⟨6,.read,.binding,.binding,2305843009213697249,[],"g1_2",13⟩,
  ⟨7,.absorb,(.reg 13),.binding,0,[],"g1_2",14⟩,
  ⟨8,.add,(.reg 5),(.reg 5),0,[],"",16⟩,
  ⟨9,.add,(.reg 16),(.reg 9),0,[],"",18⟩,
  ⟨10,.add,(.reg 18),(.reg 13),0,[],"",20⟩,
  ⟨11,.check,(.reg 20),.binding,0,[],"round1",22⟩,
  ⟨12,.draw,.binding,.binding,0,[⟨115,by decide⟩,⟨117,by decide⟩,⟨109,by decide⟩,⟨99,by decide⟩,⟨104,by decide⟩,⟨101,by decide⟩,⟨99,by decide⟩,⟨107,by decide⟩,⟨46,by decide⟩,⟨99,by decide⟩,⟨49,by decide⟩],"c1",25⟩,
  ⟨13,.read,.binding,.binding,2305843009213697249,[],"g2_0",27⟩,
  ⟨14,.absorb,(.reg 27),.binding,0,[],"g2_0",28⟩,
  ⟨15,.read,.binding,.binding,2305843009213697249,[],"g2_1",31⟩,
  ⟨16,.absorb,(.reg 31),.binding,0,[],"g2_1",32⟩,
  ⟨17,.read,.binding,.binding,2305843009213697249,[],"g2_2",35⟩,
  ⟨18,.absorb,(.reg 35),.binding,0,[],"g2_2",36⟩,
  ⟨19,.add,(.reg 27),(.reg 27),0,[],"",38⟩,
  ⟨20,.add,(.reg 38),(.reg 31),0,[],"",40⟩,
  ⟨21,.add,(.reg 40),(.reg 35),0,[],"",42⟩,
  ⟨22,.mul,(.reg 9),(.reg 25),0,[],"",44⟩,
  ⟨23,.mul,(.reg 25),(.reg 25),0,[],"",46⟩,
  ⟨24,.mul,(.reg 13),(.reg 46),0,[],"",48⟩,
  ⟨25,.add,(.reg 44),(.reg 48),0,[],"",50⟩,
  ⟨26,.add,(.reg 5),(.reg 50),0,[],"",52⟩,
  ⟨27,.check,(.reg 42),(.reg 52),0,[],"round2",54⟩,
  ⟨28,.draw,.binding,.binding,0,[⟨115,by decide⟩,⟨117,by decide⟩,⟨109,by decide⟩,⟨99,by decide⟩,⟨104,by decide⟩,⟨101,by decide⟩,⟨99,by decide⟩,⟨107,by decide⟩,⟨46,by decide⟩,⟨99,by decide⟩,⟨50,by decide⟩],"c2",57⟩,
  ⟨29,.mul,(.reg 31),(.reg 57),0,[],"",58⟩,
  ⟨30,.mul,(.reg 57),(.reg 57),0,[],"",60⟩,
  ⟨31,.mul,(.reg 35),(.reg 60),0,[],"",62⟩,
  ⟨32,.add,(.reg 58),(.reg 62),0,[],"",64⟩,
  ⟨33,.add,(.reg 27),(.reg 64),0,[],"",66⟩,
  ⟨34,.mul,(.reg 25),(.reg 57),0,[],"",68⟩,
  ⟨35,.add,(.reg 68),(.reg 25),0,[],"",70⟩,
  ⟨36,.check,(.reg 66),(.reg 70),0,[],"final",72⟩,
  ⟨37,.expectEnd,.binding,.binding,0,[],"",74⟩,
  ⟨38,.accept,.binding,.binding,0,[],"",76⟩
]
theorem sumcheck_simulation (hash : Hash) (c : Cursor) (t : Tail) (h : Represents c t) :
 TerminalRel Represents (Zkc.Realization.InstructionSequence.run (cursorStep hash) sumcheck c) (Zkc.Realization.InstructionSequence.run (tailStep hash) sumcheck t) := interpreted_run_simulation hash sumcheck c t h
def schnorr : List Instr := [
  ⟨0,.init,.binding,.binding,0,[⟨115,by decide⟩,⟨104,by decide⟩,⟨97,by decide⟩,⟨50,by decide⟩,⟨53,by decide⟩,⟨54,by decide⟩,⟨58,by decide⟩,⟨101,by decide⟩,⟨99,by decide⟩,⟨98,by decide⟩,⟨48,by decide⟩,⟨50,by decide⟩,⟨102,by decide⟩,⟨100,by decide⟩,⟨102,by decide⟩,⟨99,by decide⟩,⟨51,by decide⟩,⟨53,by decide⟩,⟨49,by decide⟩,⟨101,by decide⟩,⟨52,by decide⟩,⟨100,by decide⟩,⟨102,by decide⟩,⟨49,by decide⟩,⟨97,by decide⟩,⟨51,by decide⟩,⟨52,by decide⟩,⟨48,by decide⟩,⟨102,by decide⟩,⟨53,by decide⟩,⟨99,by decide⟩,⟨49,by decide⟩,⟨101,by decide⟩,⟨101,by decide⟩,⟨53,by decide⟩,⟨99,by decide⟩,⟨57,by decide⟩,⟨48,by decide⟩,⟨99,by decide⟩,⟨102,by decide⟩,⟨56,by decide⟩,⟨99,by decide⟩,⟨102,by decide⟩,⟨57,by decide⟩,⟨54,by decide⟩,⟨101,by decide⟩,⟨49,by decide⟩,⟨100,by decide⟩,⟨49,by decide⟩,⟨97,by decide⟩,⟨102,by decide⟩,⟨55,by decide⟩,⟨102,by decide⟩,⟨97,by decide⟩,⟨54,by decide⟩,⟨57,by decide⟩,⟨51,by decide⟩,⟨54,by decide⟩,⟨56,by decide⟩,⟨98,by decide⟩,⟨53,by decide⟩,⟨98,by decide⟩,⟨52,by decide⟩,⟨57,by decide⟩,⟨100,by decide⟩,⟨51,by decide⟩,⟨50,by decide⟩,⟨55,by decide⟩,⟨53,by decide⟩,⟨49,by decide⟩,⟨99,by decide⟩],"",0⟩,
  ⟨1,.absorb,.binding,.binding,0,[],"y",2⟩,
  ⟨2,.read,.binding,.binding,4611686018427394499,[],"commit_A",5⟩,
  ⟨3,.absorb,(.reg 5),.binding,0,[],"commit_A",6⟩,
  ⟨4,.draw,.binding,.binding,0,[⟨115,by decide⟩,⟨99,by decide⟩,⟨104,by decide⟩,⟨110,by decide⟩,⟨111,by decide⟩,⟨114,by decide⟩,⟨114,by decide⟩,⟨46,by decide⟩,⟨99,by decide⟩],"c",9⟩,
  ⟨5,.read,.binding,.binding,2305843009213697249,[],"resp_z",11⟩,
  ⟨6,.absorb,(.reg 11),.binding,0,[],"resp_z",12⟩,
  ⟨7,.constant,.binding,.binding,4,[],"",14⟩,
  ⟨8,.gexp,(.reg 14),(.reg 11),0,[],"",16⟩,
  ⟨9,.gexp,.binding,(.reg 9),0,[],"",18⟩,
  ⟨10,.gmul,(.reg 5),(.reg 18),0,[],"",20⟩,
  ⟨11,.check,(.reg 16),(.reg 20),0,[],"verify",22⟩,
  ⟨12,.expectEnd,.binding,.binding,0,[],"",24⟩,
  ⟨13,.accept,.binding,.binding,0,[],"",26⟩
]
theorem schnorr_simulation (hash : Hash) (c : Cursor) (t : Tail) (h : Represents c t) :
 TerminalRel Represents (Zkc.Realization.InstructionSequence.run (cursorStep hash) schnorr c) (Zkc.Realization.InstructionSequence.run (tailStep hash) schnorr t) := interpreted_run_simulation hash schnorr c t h

end Zkc.Protocols.ScalarBytecode.Schedules
