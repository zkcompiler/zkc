import Zkc.Protocols.ScalarBytecode.Messages
import Zkc.Protocols.ScalarBytecode.Certificates
import Zkc.Protocols.ScalarBytecode.Schedules

set_option autoImplicit false

namespace Zkc.Protocols.ScalarBytecode.MessageEvaluation
open Zkc.Realization.InstructionSequence Zkc.Semantics.OperationContract Zkc.Realization.ByteEncoding Zkc.Semantics.Locality

-- Source-line keys are deliberately distinct from OIR register and row numbers.
def project (c : Zkc.Protocols.ScalarBytecode.Execution.Core) : Zkc.Source.LocalArithmetic.Env := fun k =>
 if k = 23 then c.binding else
 if k = 24 then c.regs 5 else if k = 25 then c.regs 9 else
 if k = 26 then c.regs 13 else if k = 28 then c.regs 25 else
 if k = 29 then c.regs 27 else if k = 30 then c.regs 31 else
 if k = 31 then c.regs 35 else if k = 33 then c.regs 57 else 0

def rhs (c : Zkc.Protocols.ScalarBytecode.Execution.Core) := Zkc.Protocols.ScalarBytecode.Certificates.round2Right.expr.eval (project c) []
def lhs (c : Zkc.Protocols.ScalarBytecode.Execution.Core) := Zkc.Protocols.ScalarBytecode.Certificates.round2Left.expr.eval (project c) []
def req (c : Zkc.Protocols.ScalarBytecode.Execution.Core) := Zkc.Protocols.ScalarBytecode.CheckedExpression.request Zkc.Protocols.ScalarBytecode.Certificates.round2Right Zkc.Protocols.ScalarBytecode.Certificates.round2RightCert
 (Zkc.Compiler.Arithmetic.Dag.view Zkc.Protocols.ScalarBytecode.Certificates.occurrences 0 32 (project c))
theorem recipe_reply (c : Zkc.Protocols.ScalarBytecode.Execution.Core) : Zkc.Protocols.ScalarBytecode.CheckedExpression.reply (req c) = .ok (rhs c) :=
 (Zkc.Protocols.ScalarBytecode.Certificates.round2Right_joined (project c) []).1

def pureSlice := (Zkc.Protocols.ScalarBytecode.Schedules.sumcheck.drop 19).take 8
def evaluated (hash : Zkc.Protocols.ScalarBytecode.Execution.Hash) (t : Zkc.Protocols.ScalarBytecode.Execution.Tail) := run (Zkc.Protocols.ScalarBytecode.Execution.tailStep hash) pureSlice t
-- This proves the evaluation equality from Zkc.Protocols.ScalarBytecode.Execution instructions, not a desired premise.
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem actual_operands (hash : Zkc.Protocols.ScalarBytecode.Execution.Hash) (t : Zkc.Protocols.ScalarBytecode.Execution.Tail) :
 (evaluated hash t).outcome = .incomplete ∧
 (evaluated hash t).events = [] ∧
 (evaluated hash t).state.rest = t.rest ∧
 (evaluated hash t).state.offset = t.offset ∧
 (evaluated hash t).state.core.provider = t.core.provider ∧
 (evaluated hash t).state.core.regs 42 = lhs t.core ∧
 (evaluated hash t).state.core.regs 52 = rhs t.core := by
 simp [evaluated,pureSlice,Zkc.Protocols.ScalarBytecode.Schedules.sumcheck,run,Zkc.Protocols.ScalarBytecode.Execution.tailStep,Zkc.Protocols.ScalarBytecode.Execution.tailHandler,
 Zkc.Protocols.ScalarBytecode.Execution.effect,Zkc.Protocols.ScalarBytecode.Execution.request,Zkc.Protocols.ScalarBytecode.Execution.get,Zkc.Protocols.ScalarBytecode.Execution.put,lhs,rhs,project,Zkc.Protocols.ScalarBytecode.Certificates.round2Left,
 Zkc.Protocols.ScalarBytecode.Certificates.round2Right,Zkc.Source.LocalArithmetic.Expr.eval,Zkc.Protocols.ScalarBytecode.Parameters.modulus]

def checkInstr : Zkc.Protocols.ScalarBytecode.Execution.Instr := (Zkc.Protocols.ScalarBytecode.Schedules.sumcheck[27]'(by decide))
def joinedCheck (hash : Zkc.Protocols.ScalarBytecode.Execution.Hash) (t : Zkc.Protocols.ScalarBytecode.Execution.Tail) : Step Zkc.Protocols.ScalarBytecode.Execution.Tail Zkc.Protocols.ScalarBytecode.Execution.Event :=
 let after := (evaluated hash t).state
 match Zkc.Protocols.ScalarBytecode.CheckedExpression.reply (req t.core) with
 | .ok n => Zkc.Protocols.ScalarBytecode.Execution.tailStep hash checkInstr {after with core := Zkc.Protocols.ScalarBytecode.Execution.put after.core 52 n}
 | .reject s => .halt (.reject s) after []
 | .unavailable s => .halt (.unavailable s) after []

theorem put_same (c : Zkc.Protocols.ScalarBytecode.Execution.Core) (n : Nat) : Zkc.Protocols.ScalarBytecode.Execution.put c n (c.regs n) = c := by
 cases c with
 | mk regs provider binding =>
   simp only [Zkc.Protocols.ScalarBytecode.Execution.put]
   congr 1
   funext k
   split <;> simp_all

-- Exact Step equality retains ALL registers, cursor/suffix, provider and events,
-- including rejection. The adapter currently executes the original pure slice.
theorem checked_composition (hash : Zkc.Protocols.ScalarBytecode.Execution.Hash) (t : Zkc.Protocols.ScalarBytecode.Execution.Tail) :
 joinedCheck hash t = Zkc.Protocols.ScalarBytecode.Execution.tailStep hash checkInstr (evaluated hash t).state := by
 unfold joinedCheck
 rw [recipe_reply]
 have hr := (actual_operands hash t).2.2.2.2.2.2
 rw [← hr]
 dsimp only
 rw [put_same]

abbrev Scalar := Zkc.Protocols.ScalarBytecode.Messages.Carrier .scalar
structure Block where
 a : Scalar
 b : Scalar
 c : Scalar

def values (b : Block) : List Nat := [b.a.val,b.b.val,b.c.val]
def blockRequest (b : Block) := Zkc.Protocols.ScalarBytecode.Messages.send Zkc.Protocols.ScalarBytecode.Messages.fixed ⟨1,by decide⟩ .scalar 13 [b.a,b.b,b.c]
def install (c : Zkc.Protocols.ScalarBytecode.Execution.Core) (b : Block) : Zkc.Protocols.ScalarBytecode.Execution.Core :=
 Zkc.Protocols.ScalarBytecode.Execution.put (Zkc.Protocols.ScalarBytecode.Execution.put (Zkc.Protocols.ScalarBytecode.Execution.put c 27 b.a.val) 31 b.b.val) 35 b.c.val

theorem block_legal (b : Block) :
 (Zkc.Protocols.ScalarBytecode.Messages.signature Zkc.Protocols.ScalarBytecode.Messages.fixed).legalArg (blockRequest b).op (blockRequest b).arg := by rfl

theorem block_codec (b : Block) (tail : Bytes) :
 Zkc.Protocols.ScalarBytecode.Codec.readWords 3 (Zkc.Protocols.ScalarBytecode.Codec.wire (values b) ++ tail) = some (values b,tail) := by
 apply Zkc.Protocols.ScalarBytecode.Codec.words_complete (values b)
 intro v hv
 simp only [values,List.mem_cons,List.not_mem_nil,or_false] at hv
 rcases hv with h|h|h <;> subst v
 · exact b.a.isLt
 · exact b.b.isLt
 · exact b.c.isLt

-- Canonical adversarial block members, without any honest polynomial equation.
theorem family_checked_composition (hash : Zkc.Protocols.ScalarBytecode.Execution.Hash) (t : Zkc.Protocols.ScalarBytecode.Execution.Tail) (b : Block) :
 (Zkc.Protocols.ScalarBytecode.Messages.signature Zkc.Protocols.ScalarBytecode.Messages.fixed).legalArg (blockRequest b).op (blockRequest b).arg ∧
 joinedCheck hash {t with core := install t.core b} =
 Zkc.Protocols.ScalarBytecode.Execution.tailStep hash checkInstr (evaluated hash {t with core := install t.core b}).state :=
 ⟨block_legal b,checked_composition hash _⟩

-- Word-level operational bridge at the ACTUAL row13 request, arbitrary unread suffix.
theorem first_word_effect (hash : Zkc.Protocols.ScalarBytecode.Execution.Hash) (core : Zkc.Protocols.ScalarBytecode.Execution.Core) (v : Scalar) (tail : Bytes) :
 Zkc.Protocols.ScalarBytecode.Execution.effect hash (Zkc.Protocols.ScalarBytecode.Execution.request (Zkc.Protocols.ScalarBytecode.Schedules.sumcheck[13]'(by decide)) core) core (Zkc.Protocols.ScalarBytecode.Codec.enc v.val ++ tail) =
 (.ok v.val,core,8,[⟨13,.read,"g2_0",v.val,Zkc.Protocols.ScalarBytecode.Codec.enc v.val⟩]) := by
 have hv : v.val < 2305843009213697249 := v.isLt
 have hv8 : v.val < 256^8 := Nat.lt_trans v.isLt (by decide : Zkc.Protocols.ScalarBytecode.Parameters.modulus < 256^8)
 have row : Zkc.Protocols.ScalarBytecode.Schedules.sumcheck[13]'(by decide) =
     { site := 13, op := .read, literal := 2305843009213697249,
       label := "g2_0", dest := 27 } := rfl
 rw [row]
 simp [Zkc.Protocols.ScalarBytecode.Execution.effect,Zkc.Protocols.ScalarBytecode.Execution.request,Zkc.Protocols.ScalarBytecode.Codec.enc,Zkc.Realization.ByteEncoding.value_be 8 v.val hv8,hv]

theorem first_word_suffix (v : Scalar) (tail : Bytes) :
 Zkc.Protocols.ScalarBytecode.Codec.readScalar (Zkc.Protocols.ScalarBytecode.Codec.enc v.val ++ tail) = some (v.val,tail) := Zkc.Protocols.ScalarBytecode.Codec.scalar_complete _ v.isLt tail

theorem raw_legality (bs : Bytes) (core : Zkc.Protocols.ScalarBytecode.Execution.Core) :
 (Zkc.Protocols.ScalarBytecode.Messages.signature Zkc.Protocols.ScalarBytecode.Messages.fixed).legalArg (Zkc.Protocols.ScalarBytecode.Messages.read Zkc.Protocols.ScalarBytecode.Messages.fixed ⟨1,by decide⟩ .scalar 13 bs).op
   (Zkc.Protocols.ScalarBytecode.Messages.read Zkc.Protocols.ScalarBytecode.Messages.fixed ⟨1,by decide⟩ .scalar 13 bs).arg ∧
 Zkc.Protocols.ScalarBytecode.Execution.sig.legalArg (Zkc.Protocols.ScalarBytecode.Execution.request (Zkc.Protocols.ScalarBytecode.Schedules.sumcheck[13]'(by decide)) core).op
   (Zkc.Protocols.ScalarBytecode.Execution.request (Zkc.Protocols.ScalarBytecode.Schedules.sumcheck[13]'(by decide)) core).arg := ⟨True.intro,True.intro⟩

theorem fixed_formation : Zkc.Protocols.AlgebraicRounds.ParameterFamily.sumcheckFamily.inst (Zkc.Protocols.AlgebraicRounds.ParameterFamily.env2 2 2) = Zkc.Protocols.ScalarBytecode.Messages.fixed := by decide

theorem block_request_values (b : Block) :
 (blockRequest b).arg.map Fin.val = values b := by rfl

end Zkc.Protocols.ScalarBytecode.MessageEvaluation
