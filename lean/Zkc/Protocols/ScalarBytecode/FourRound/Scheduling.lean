import Zkc.Protocols.ScalarBytecode.Scheduling

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

namespace Zkc.Protocols.ScalarBytecode.FourRound.Scheduling
open Zkc.Realization.InstructionSequence Zkc.Semantics.OperationContract Zkc.Realization.ByteEncoding Zkc.Semantics.Locality Zkc.Protocols.ScalarBytecode.Execution Zkc.Protocols.ScalarBytecode.Endpoint Zkc.Protocols.ScalarBytecode.Suppliers Zkc.Protocols.ScalarBytecode.Scheduling

/- Actual n4 OIR rows 60..67. Register (row,slot) maps to 2*row+slot.
   Dataflow tokens for sponge/cursor are interpreted by Zkc.Protocols.ScalarBytecode.Endpoint's explicit state.
   The theorem concerns these represented rows; host-file authentication and
   native decoding are separate realization obligations. -/
def lastDraw : Instr := drawI 60 121 [⟨114,by decide⟩,⟨49,by decide⟩,⟨54,by decide⟩,⟨46,by decide⟩,⟨115,by decide⟩,⟨117,by decide⟩,⟨109,by decide⟩,⟨99,by decide⟩,⟨104,by decide⟩,⟨101,by decide⟩,⟨99,by decide⟩,⟨107,by decide⟩,⟨46,by decide⟩,⟨99,by decide⟩,⟨52,by decide⟩]
def lastPoly : List Instr := [
  mulI 61 95 121 122, mulI 62 121 121 124, mulI 63 99 124 126,
  addI 64 122 126 128, addI 65 91 128 130]
def prefixProduct : List Instr := [mulI 66 25 57 132, mulI 67 132 89 134]
def oldBlock := [lastDraw] ++ lastPoly ++ prefixProduct
def newBlock := prefixProduct ++ [lastDraw] ++ lastPoly

/- Independent direct endpoint derivation, including the intervening polynomial.
    No old/new block equation is taken as a premise. -/
set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem source_block {S : Type} (supplier : Supplier S) (hash : Hash) (s : World S) :
    TerminalRel (OpenRel allRegs Eq)
      (run (openStep hash supplier) oldBlock s)
      (run (openStep hash supplier) newBlock s) := by
  simp [TerminalRel,OpenRel,LocalRel,Zkc.Protocols.ScalarBytecode.Frames.CoreRel,allRegs,oldBlock,newBlock,
    prefixProduct,lastDraw,lastPoly,drawI,mulI,addI,run,
    openStep,serve,notify,update,mapStep,eventsOf,effect,request,Zkc.Protocols.ScalarBytecode.Execution.get,put]
  intro n
  by_cases h132 : n = 132
  · subst n; simp
  · by_cases h134 : n = 134
    · subst n; simp
    · simp [h132,h134]

theorem source_context {S : Type} (supplier : Supplier S) (hash : Hash)
    (pre post : List Instr) (s : World S) :
    TerminalRel (OpenRel allRegs Eq)
      (run (openStep hash supplier) (pre ++ (oldBlock ++ post)) s)
      (run (openStep hash supplier) (pre ++ (newBlock ++ post)) s) :=
  open_block_context supplier allRegs hash oldBlock newBlock pre post
    (source_block supplier hash) (fun i _ => all_safe i) s

/-- The certificate and intrinsic route apply to BOTH actual prefix instructions. -/
def firstStable : DrawStableMul 121 := ⟨66,25,57,132,by decide⟩
def secondStable : DrawStableMul 121 := ⟨67,132,89,134,by decide⟩

theorem first_indexed {S : Type} (supplier : Supplier S) (hash : Hash) (s : World S) :
    TerminalRel (OpenRel allRegs Eq)
      (run (openStep hash supplier) [lastDraw,mulI 66 25 57 132] s)
      (run (openStep hash supplier) [mulI 66 25 57 132,lastDraw] s) :=
  indexed_mul_draw supplier hash 60 121 _ firstStable s

theorem second_checked {S : Type} (supplier : Supplier S) (hash : Hash) (s : World S) :
    TerminalRel (OpenRel allRegs Eq)
      (run (openStep hash supplier) [lastDraw,mulI 67 132 89 134] s)
      (run (openStep hash supplier) [mulI 67 132 89 134,lastDraw] s) :=
  checked_mul_draw supplier hash 67 60 132 89 134 121 _ (by decide) s

/- Generated from pinned n4 JSON. Not a verified JSON parser. -/
def sourceOps : List Instr := [
  ⟨0,.init,.binding,.binding,0,[⟨115,by decide⟩,⟨104,by decide⟩,⟨97,by decide⟩,⟨50,by decide⟩,⟨53,by decide⟩,⟨54,by decide⟩,⟨58,by decide⟩,⟨102,by decide⟩,⟨53,by decide⟩,⟨53,by decide⟩,⟨50,by decide⟩,⟨57,by decide⟩,⟨101,by decide⟩,⟨101,by decide⟩,⟨56,by decide⟩,⟨98,by decide⟩,⟨52,by decide⟩,⟨50,by decide⟩,⟨50,by decide⟩,⟨56,by decide⟩,⟨100,by decide⟩,⟨48,by decide⟩,⟨55,by decide⟩,⟨53,by decide⟩,⟨50,by decide⟩,⟨97,by decide⟩,⟨54,by decide⟩,⟨97,by decide⟩,⟨56,by decide⟩,⟨98,by decide⟩,⟨101,by decide⟩,⟨97,by decide⟩,⟨51,by decide⟩,⟨57,by decide⟩,⟨57,by decide⟩,⟨100,by decide⟩,⟨100,by decide⟩,⟨55,by decide⟩,⟨50,by decide⟩,⟨98,by decide⟩,⟨101,by decide⟩,⟨48,by decide⟩,⟨49,by decide⟩,⟨53,by decide⟩,⟨48,by decide⟩,⟨55,by decide⟩,⟨97,by decide⟩,⟨101,by decide⟩,⟨101,by decide⟩,⟨54,by decide⟩,⟨55,by decide⟩,⟨56,by decide⟩,⟨56,by decide⟩,⟨98,by decide⟩,⟨48,by decide⟩,⟨101,by decide⟩,⟨53,by decide⟩,⟨57,by decide⟩,⟨49,by decide⟩,⟨56,by decide⟩,⟨102,by decide⟩,⟨50,by decide⟩,⟨100,by decide⟩,⟨53,by decide⟩,⟨48,by decide⟩,⟨98,by decide⟩,⟨100,by decide⟩,⟨56,by decide⟩,⟨102,by decide⟩,⟨49,by decide⟩,⟨102,by decide⟩],"",0⟩,
  ⟨1,.absorb,.binding,.binding,0,[],"",2⟩,
  ⟨2,.read,.binding,.binding,2305843009213697249,[],"g1_0",5⟩,
  ⟨3,.absorb,.reg 5,.binding,0,[],"",6⟩,
  ⟨4,.read,.binding,.binding,2305843009213697249,[],"g1_1",9⟩,
  ⟨5,.absorb,.reg 9,.binding,0,[],"",10⟩,
  ⟨6,.read,.binding,.binding,2305843009213697249,[],"g1_2",13⟩,
  ⟨7,.absorb,.reg 13,.binding,0,[],"",14⟩,
  addI 8 5 5 16,
  addI 9 16 9 18,
  addI 10 18 13 20,
  ⟨11,.check,.reg 20,.binding,0,[],"round1",22⟩,
  drawI 12 25 [⟨114,by decide⟩,⟨49,by decide⟩,⟨54,by decide⟩,⟨46,by decide⟩,⟨115,by decide⟩,⟨117,by decide⟩,⟨109,by decide⟩,⟨99,by decide⟩,⟨104,by decide⟩,⟨101,by decide⟩,⟨99,by decide⟩,⟨107,by decide⟩,⟨46,by decide⟩,⟨99,by decide⟩,⟨49,by decide⟩],
  ⟨13,.read,.binding,.binding,2305843009213697249,[],"g2_0",27⟩,
  ⟨14,.absorb,.reg 27,.binding,0,[],"",28⟩,
  ⟨15,.read,.binding,.binding,2305843009213697249,[],"g2_1",31⟩,
  ⟨16,.absorb,.reg 31,.binding,0,[],"",32⟩,
  ⟨17,.read,.binding,.binding,2305843009213697249,[],"g2_2",35⟩,
  ⟨18,.absorb,.reg 35,.binding,0,[],"",36⟩,
  addI 19 27 27 38,
  addI 20 38 31 40,
  addI 21 40 35 42,
  mulI 22 9 25 44,
  mulI 23 25 25 46,
  mulI 24 13 46 48,
  addI 25 44 48 50,
  addI 26 5 50 52,
  ⟨27,.check,.reg 42,.reg 52,0,[],"round2",54⟩,
  drawI 28 57 [⟨114,by decide⟩,⟨49,by decide⟩,⟨54,by decide⟩,⟨46,by decide⟩,⟨115,by decide⟩,⟨117,by decide⟩,⟨109,by decide⟩,⟨99,by decide⟩,⟨104,by decide⟩,⟨101,by decide⟩,⟨99,by decide⟩,⟨107,by decide⟩,⟨46,by decide⟩,⟨99,by decide⟩,⟨50,by decide⟩],
  ⟨29,.read,.binding,.binding,2305843009213697249,[],"g3_0",59⟩,
  ⟨30,.absorb,.reg 59,.binding,0,[],"",60⟩,
  ⟨31,.read,.binding,.binding,2305843009213697249,[],"g3_1",63⟩,
  ⟨32,.absorb,.reg 63,.binding,0,[],"",64⟩,
  ⟨33,.read,.binding,.binding,2305843009213697249,[],"g3_2",67⟩,
  ⟨34,.absorb,.reg 67,.binding,0,[],"",68⟩,
  addI 35 59 59 70,
  addI 36 70 63 72,
  addI 37 72 67 74,
  mulI 38 31 57 76,
  mulI 39 57 57 78,
  mulI 40 35 78 80,
  addI 41 76 80 82,
  addI 42 27 82 84,
  ⟨43,.check,.reg 74,.reg 84,0,[],"round3",86⟩,
  drawI 44 89 [⟨114,by decide⟩,⟨49,by decide⟩,⟨54,by decide⟩,⟨46,by decide⟩,⟨115,by decide⟩,⟨117,by decide⟩,⟨109,by decide⟩,⟨99,by decide⟩,⟨104,by decide⟩,⟨101,by decide⟩,⟨99,by decide⟩,⟨107,by decide⟩,⟨46,by decide⟩,⟨99,by decide⟩,⟨51,by decide⟩],
  ⟨45,.read,.binding,.binding,2305843009213697249,[],"g4_0",91⟩,
  ⟨46,.absorb,.reg 91,.binding,0,[],"",92⟩,
  ⟨47,.read,.binding,.binding,2305843009213697249,[],"g4_1",95⟩,
  ⟨48,.absorb,.reg 95,.binding,0,[],"",96⟩,
  ⟨49,.read,.binding,.binding,2305843009213697249,[],"g4_2",99⟩,
  ⟨50,.absorb,.reg 99,.binding,0,[],"",100⟩,
  addI 51 91 91 102,
  addI 52 102 95 104,
  addI 53 104 99 106,
  mulI 54 63 89 108,
  mulI 55 89 89 110,
  mulI 56 67 110 112,
  addI 57 108 112 114,
  addI 58 59 114 116,
  ⟨59,.check,.reg 106,.reg 116,0,[],"round4",118⟩,
  drawI 60 121 [⟨114,by decide⟩,⟨49,by decide⟩,⟨54,by decide⟩,⟨46,by decide⟩,⟨115,by decide⟩,⟨117,by decide⟩,⟨109,by decide⟩,⟨99,by decide⟩,⟨104,by decide⟩,⟨101,by decide⟩,⟨99,by decide⟩,⟨107,by decide⟩,⟨46,by decide⟩,⟨99,by decide⟩,⟨52,by decide⟩],
  mulI 61 95 121 122,
  mulI 62 121 121 124,
  mulI 63 99 124 126,
  addI 64 122 126 128,
  addI 65 91 128 130,
  mulI 66 25 57 132,
  mulI 67 132 89 134,
  mulI 68 134 121 136,
  addI 69 136 25 138,
  ⟨70,.check,.reg 130,.reg 138,0,[],"final",140⟩,
  ⟨71,.expectEnd,.binding,.binding,0,[],"",142⟩,
  ⟨72,.accept,.binding,.binding,0,[],"",144⟩]

theorem source_segment : (sourceOps.drop 60).take 8 = oldBlock := by rfl
def scheduledOps := sourceOps.take 60 ++ (newBlock ++ sourceOps.drop 68)

theorem bound_source_context {S : Type} (supplier : Supplier S) (hash : Hash)
    (s : World S) : TerminalRel (OpenRel allRegs Eq)
      (run (openStep hash supplier) sourceOps s)
      (run (openStep hash supplier) scheduledOps s) := by
  exact source_context supplier hash (sourceOps.take 60) (sourceOps.drop 68) s

theorem source_dispatch {S : Type} (supplier : Supplier S) (hash : Hash)
    (v : Local) (s : S) (hv : v.pc = 0) :
    TerminalRel (OpenRel allRegs Eq)
      (endpoint hash supplier sourceOps sourceOps.length ⟨v,s⟩)
      (endpoint hash supplier scheduledOps scheduledOps.length ⟨v,s⟩) := by
  rw [show endpoint hash supplier sourceOps sourceOps.length ⟨v,s⟩ =
      run (openStep hash supplier) sourceOps ⟨v,s⟩ from endpoint_list hash supplier [] _ _ hv]
  rw [show endpoint hash supplier scheduledOps scheduledOps.length ⟨v,s⟩ =
      run (openStep hash supplier) scheduledOps ⟨v,s⟩ from endpoint_list hash supplier [] _ _ hv]
  exact bound_source_context supplier hash _

/- An independent proof of the SAME block via 12 checked adjacent swaps. -/
theorem block_via_checks {S : Type} (supplier : Supplier S) (hash : Hash)
    (s : World S) : TerminalRel (OpenRel allRegs Eq)
      (run (openStep hash supplier) oldBlock s)
      (run (openStep hash supplier) newBlock s) := by
  have h0 := exchange_context supplier hash (addI 65 91 128 130) (mulI 66 25 57 132)
    [(drawI 60 121 [⟨114,by decide⟩,⟨49,by decide⟩,⟨54,by decide⟩,⟨46,by decide⟩,⟨115,by decide⟩,⟨117,by decide⟩,⟨109,by decide⟩,⟨99,by decide⟩,⟨104,by decide⟩,⟨101,by decide⟩,⟨99,by decide⟩,⟨107,by decide⟩,⟨46,by decide⟩,⟨99,by decide⟩,⟨52,by decide⟩]),(mulI 61 95 121 122),(mulI 62 121 121 124),(mulI 63 99 124 126),(addI 64 122 126 128)] [(mulI 67 132 89 134)] (checked_mul_arith supplier hash true 66 65 25 57 132 91 128 130 (by decide)) s
  have h1 := exchange_context supplier hash (addI 64 122 126 128) (mulI 66 25 57 132)
    [(drawI 60 121 [⟨114,by decide⟩,⟨49,by decide⟩,⟨54,by decide⟩,⟨46,by decide⟩,⟨115,by decide⟩,⟨117,by decide⟩,⟨109,by decide⟩,⟨99,by decide⟩,⟨104,by decide⟩,⟨101,by decide⟩,⟨99,by decide⟩,⟨107,by decide⟩,⟨46,by decide⟩,⟨99,by decide⟩,⟨52,by decide⟩]),(mulI 61 95 121 122),(mulI 62 121 121 124),(mulI 63 99 124 126)] [(addI 65 91 128 130),(mulI 67 132 89 134)] (checked_mul_arith supplier hash true 66 64 25 57 132 122 126 128 (by decide)) s
  have h2 := exchange_context supplier hash (mulI 63 99 124 126) (mulI 66 25 57 132)
    [(drawI 60 121 [⟨114,by decide⟩,⟨49,by decide⟩,⟨54,by decide⟩,⟨46,by decide⟩,⟨115,by decide⟩,⟨117,by decide⟩,⟨109,by decide⟩,⟨99,by decide⟩,⟨104,by decide⟩,⟨101,by decide⟩,⟨99,by decide⟩,⟨107,by decide⟩,⟨46,by decide⟩,⟨99,by decide⟩,⟨52,by decide⟩]),(mulI 61 95 121 122),(mulI 62 121 121 124)] [(addI 64 122 126 128),(addI 65 91 128 130),(mulI 67 132 89 134)] (checked_mul_arith supplier hash false 66 63 25 57 132 99 124 126 (by decide)) s
  have h3 := exchange_context supplier hash (mulI 62 121 121 124) (mulI 66 25 57 132)
    [(drawI 60 121 [⟨114,by decide⟩,⟨49,by decide⟩,⟨54,by decide⟩,⟨46,by decide⟩,⟨115,by decide⟩,⟨117,by decide⟩,⟨109,by decide⟩,⟨99,by decide⟩,⟨104,by decide⟩,⟨101,by decide⟩,⟨99,by decide⟩,⟨107,by decide⟩,⟨46,by decide⟩,⟨99,by decide⟩,⟨52,by decide⟩]),(mulI 61 95 121 122)] [(mulI 63 99 124 126),(addI 64 122 126 128),(addI 65 91 128 130),(mulI 67 132 89 134)] (checked_mul_arith supplier hash false 66 62 25 57 132 121 121 124 (by decide)) s
  have h4 := exchange_context supplier hash (mulI 61 95 121 122) (mulI 66 25 57 132)
    [(drawI 60 121 [⟨114,by decide⟩,⟨49,by decide⟩,⟨54,by decide⟩,⟨46,by decide⟩,⟨115,by decide⟩,⟨117,by decide⟩,⟨109,by decide⟩,⟨99,by decide⟩,⟨104,by decide⟩,⟨101,by decide⟩,⟨99,by decide⟩,⟨107,by decide⟩,⟨46,by decide⟩,⟨99,by decide⟩,⟨52,by decide⟩])] [(mulI 62 121 121 124),(mulI 63 99 124 126),(addI 64 122 126 128),(addI 65 91 128 130),(mulI 67 132 89 134)] (checked_mul_arith supplier hash false 66 61 25 57 132 95 121 122 (by decide)) s
  have h5 := exchange_context supplier hash (drawI 60 121 [⟨114,by decide⟩,⟨49,by decide⟩,⟨54,by decide⟩,⟨46,by decide⟩,⟨115,by decide⟩,⟨117,by decide⟩,⟨109,by decide⟩,⟨99,by decide⟩,⟨104,by decide⟩,⟨101,by decide⟩,⟨99,by decide⟩,⟨107,by decide⟩,⟨46,by decide⟩,⟨99,by decide⟩,⟨52,by decide⟩]) (mulI 66 25 57 132)
    [] [(mulI 61 95 121 122),(mulI 62 121 121 124),(mulI 63 99 124 126),(addI 64 122 126 128),(addI 65 91 128 130),(mulI 67 132 89 134)] (checked_mul_draw supplier hash 66 60 25 57 132 121 [⟨114,by decide⟩,⟨49,by decide⟩,⟨54,by decide⟩,⟨46,by decide⟩,⟨115,by decide⟩,⟨117,by decide⟩,⟨109,by decide⟩,⟨99,by decide⟩,⟨104,by decide⟩,⟨101,by decide⟩,⟨99,by decide⟩,⟨107,by decide⟩,⟨46,by decide⟩,⟨99,by decide⟩,⟨52,by decide⟩] (by decide)) s
  have h6 := exchange_context supplier hash (addI 65 91 128 130) (mulI 67 132 89 134)
    [(mulI 66 25 57 132),(drawI 60 121 [⟨114,by decide⟩,⟨49,by decide⟩,⟨54,by decide⟩,⟨46,by decide⟩,⟨115,by decide⟩,⟨117,by decide⟩,⟨109,by decide⟩,⟨99,by decide⟩,⟨104,by decide⟩,⟨101,by decide⟩,⟨99,by decide⟩,⟨107,by decide⟩,⟨46,by decide⟩,⟨99,by decide⟩,⟨52,by decide⟩]),(mulI 61 95 121 122),(mulI 62 121 121 124),(mulI 63 99 124 126),(addI 64 122 126 128)] [] (checked_mul_arith supplier hash true 67 65 132 89 134 91 128 130 (by decide)) s
  have h7 := exchange_context supplier hash (addI 64 122 126 128) (mulI 67 132 89 134)
    [(mulI 66 25 57 132),(drawI 60 121 [⟨114,by decide⟩,⟨49,by decide⟩,⟨54,by decide⟩,⟨46,by decide⟩,⟨115,by decide⟩,⟨117,by decide⟩,⟨109,by decide⟩,⟨99,by decide⟩,⟨104,by decide⟩,⟨101,by decide⟩,⟨99,by decide⟩,⟨107,by decide⟩,⟨46,by decide⟩,⟨99,by decide⟩,⟨52,by decide⟩]),(mulI 61 95 121 122),(mulI 62 121 121 124),(mulI 63 99 124 126)] [(addI 65 91 128 130)] (checked_mul_arith supplier hash true 67 64 132 89 134 122 126 128 (by decide)) s
  have h8 := exchange_context supplier hash (mulI 63 99 124 126) (mulI 67 132 89 134)
    [(mulI 66 25 57 132),(drawI 60 121 [⟨114,by decide⟩,⟨49,by decide⟩,⟨54,by decide⟩,⟨46,by decide⟩,⟨115,by decide⟩,⟨117,by decide⟩,⟨109,by decide⟩,⟨99,by decide⟩,⟨104,by decide⟩,⟨101,by decide⟩,⟨99,by decide⟩,⟨107,by decide⟩,⟨46,by decide⟩,⟨99,by decide⟩,⟨52,by decide⟩]),(mulI 61 95 121 122),(mulI 62 121 121 124)] [(addI 64 122 126 128),(addI 65 91 128 130)] (checked_mul_arith supplier hash false 67 63 132 89 134 99 124 126 (by decide)) s
  have h9 := exchange_context supplier hash (mulI 62 121 121 124) (mulI 67 132 89 134)
    [(mulI 66 25 57 132),(drawI 60 121 [⟨114,by decide⟩,⟨49,by decide⟩,⟨54,by decide⟩,⟨46,by decide⟩,⟨115,by decide⟩,⟨117,by decide⟩,⟨109,by decide⟩,⟨99,by decide⟩,⟨104,by decide⟩,⟨101,by decide⟩,⟨99,by decide⟩,⟨107,by decide⟩,⟨46,by decide⟩,⟨99,by decide⟩,⟨52,by decide⟩]),(mulI 61 95 121 122)] [(mulI 63 99 124 126),(addI 64 122 126 128),(addI 65 91 128 130)] (checked_mul_arith supplier hash false 67 62 132 89 134 121 121 124 (by decide)) s
  have h10 := exchange_context supplier hash (mulI 61 95 121 122) (mulI 67 132 89 134)
    [(mulI 66 25 57 132),(drawI 60 121 [⟨114,by decide⟩,⟨49,by decide⟩,⟨54,by decide⟩,⟨46,by decide⟩,⟨115,by decide⟩,⟨117,by decide⟩,⟨109,by decide⟩,⟨99,by decide⟩,⟨104,by decide⟩,⟨101,by decide⟩,⟨99,by decide⟩,⟨107,by decide⟩,⟨46,by decide⟩,⟨99,by decide⟩,⟨52,by decide⟩])] [(mulI 62 121 121 124),(mulI 63 99 124 126),(addI 64 122 126 128),(addI 65 91 128 130)] (checked_mul_arith supplier hash false 67 61 132 89 134 95 121 122 (by decide)) s
  have h11 := exchange_context supplier hash (drawI 60 121 [⟨114,by decide⟩,⟨49,by decide⟩,⟨54,by decide⟩,⟨46,by decide⟩,⟨115,by decide⟩,⟨117,by decide⟩,⟨109,by decide⟩,⟨99,by decide⟩,⟨104,by decide⟩,⟨101,by decide⟩,⟨99,by decide⟩,⟨107,by decide⟩,⟨46,by decide⟩,⟨99,by decide⟩,⟨52,by decide⟩]) (mulI 67 132 89 134)
    [(mulI 66 25 57 132)] [(mulI 61 95 121 122),(mulI 62 121 121 124),(mulI 63 99 124 126),(addI 64 122 126 128),(addI 65 91 128 130)] (checked_mul_draw supplier hash 67 60 132 89 134 121 [⟨114,by decide⟩,⟨49,by decide⟩,⟨54,by decide⟩,⟨46,by decide⟩,⟨115,by decide⟩,⟨117,by decide⟩,⟨109,by decide⟩,⟨99,by decide⟩,⟨104,by decide⟩,⟨101,by decide⟩,⟨99,by decide⟩,⟨107,by decide⟩,⟨46,by decide⟩,⟨99,by decide⟩,⟨52,by decide⟩] (by decide)) s
  exact (rel_trans (rel_trans (rel_trans (rel_trans (rel_trans (rel_trans (rel_trans (rel_trans (rel_trans (rel_trans (rel_trans h0 h1) h2) h3) h4) h5) h6) h7) h8) h9) h10) h11)

abbrev View (S : Type) :=
  Exit × List Event × Public × Nat × Bytes × Nat × (Nat → Nat) × S

def view {S : Type} (t : Terminal (World S) Event) : View S :=
  (t.outcome,t.events,t.state.verifier.subject,t.state.verifier.offset,
   t.state.verifier.core.provider,t.state.verifier.core.binding,
   t.state.verifier.core.regs,t.state.external)

theorem view_equal {S : Type} {a b : Terminal (World S) Event}
    (h : TerminalRel (OpenRel allRegs Eq) a b) : view a = view b := by
  rcases h with ⟨ho,⟨⟨hp,hf,hpov,hbind,hregs⟩,hex⟩,hev⟩
  have hr : a.state.verifier.core.regs = b.state.verifier.core.regs :=
    funext (fun n => hregs n trivial)
  simp only [view,Prod.mk.injEq]
  exact ⟨ho,hev,hp,hf,hpov,hbind,hr,hex⟩

/-- Exact property input preservation; the selected predicate is not fixed
    to acceptance. Assumptions of a cryptographic theorem remain external. -/
theorem source_property {S : Type} (supplier : Supplier S) (hash : Hash)
    (s : World S) (property : View S → Prop) :
    property (view (run (openStep hash supplier) sourceOps s)) ↔
    property (view (run (openStep hash supplier) scheduledOps s)) := by
  rw [view_equal (bound_source_context supplier hash s)]

/-- An already supplied pair retains the SAME event prefixes under identity.
    This neither collects forks nor supplies an efficient reset capability. -/
theorem source_pair_property {S : Type} (supplier : Supplier S) (hash : Hash)
    (s t : World S) (property : View S → View S → Prop) :
    property (view (run (openStep hash supplier) sourceOps s))
             (view (run (openStep hash supplier) sourceOps t)) ↔
    property (view (run (openStep hash supplier) scheduledOps s))
             (view (run (openStep hash supplier) scheduledOps t)) := by
  rw [view_equal (bound_source_context supplier hash s),
      view_equal (bound_source_context supplier hash t)]

end Zkc.Protocols.ScalarBytecode.FourRound.Scheduling
