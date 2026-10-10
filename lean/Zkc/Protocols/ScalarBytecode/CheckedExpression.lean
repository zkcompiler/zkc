import Zkc.Compiler.Arithmetic.Dag
import Zkc.Semantics.Locality
import Zkc.Protocols.ScalarBytecode.Codec

set_option autoImplicit false

namespace Zkc.Protocols.ScalarBytecode.CheckedExpression
open Zkc.Compiler.Arithmetic.Dag

-- One typed scalar-evaluation operation. Raw Nat egress is checked rather than
-- silently reducing Q to zero. legalArg does not require an honest equation.
def signature : Zkc.Semantics.OperationContract.Signature where
 Op := Unit
 Arg := fun _ => Subject × Certificate × Zkc.Source.LocalArithmetic.View
 Result := fun _ _ => Nat
 legalArg := fun _ a => check a.1 a.2.1 a.2.2 = true
 legalResult := fun _ _ n => n < Zkc.Protocols.ScalarBytecode.Parameters.modulus

def request (s : Subject) (c : Certificate) (v : Zkc.Source.LocalArithmetic.View) : Zkc.Semantics.OperationContract.Request signature :=
 ⟨s.site, (), (s,c,v)⟩
def reply (r : Zkc.Semantics.OperationContract.Request signature) : Zkc.Semantics.OperationContract.Reply signature r :=
 if r.site ≠ r.arg.1.site then .reject "Zkc.Protocols.ScalarBytecode.CheckedExpression-R-SITE"
 else if check r.arg.1 r.arg.2.1 r.arg.2.2 then
   match (runDAG (fun k => (r.arg.2.2 k).getD 0) r.arg.2.1.dag).head? with
   | none => .reject "Zkc.Protocols.ScalarBytecode.CheckedExpression-R-EMPTY"
   | some n => if n < Zkc.Protocols.ScalarBytecode.Parameters.modulus then .ok n else .reject "Zkc.Protocols.ScalarBytecode.CheckedExpression-R-NONCANONICAL"
 else .reject "Zkc.Protocols.ScalarBytecode.CheckedExpression-R-CERTIFICATE"

theorem reply_legal (r : Zkc.Semantics.OperationContract.Request signature) : Zkc.Semantics.OperationContract.LegalReply r (reply r) := by
 unfold reply
 split
 · trivial
 · split
   · split
     · trivial
     · split
       next h => exact h
       next => trivial
   · trivial

-- Includes complete request/certificate/view and initial memory in the action.
def action (s : Subject) (c : Certificate) (os : List Occ) (role : Nat)
 (g : Zkc.Source.LocalArithmetic.Env × Zkc.Source.LocalArithmetic.Memory) := (request s c (view os role s.site g.1), g.2)
theorem view_respecting (s : Subject) (c : Certificate) (os : List Occ) (role : Nat) :
 Zkc.Semantics.Locality.FiberConstant (fun g : Zkc.Source.LocalArithmetic.Env × Zkc.Source.LocalArithmetic.Memory => (view os role s.site g.1,g.2))
   (action s c os role) := by
 intro g h hv
 exact congrArg (fun p : Zkc.Source.LocalArithmetic.View × Zkc.Source.LocalArithmetic.Memory => (request s c p.1,p.2)) hv

-- Joined implication consumes actual checker success and a checked range fact;
-- it supplies source evaluation, typed reply and exact bytes at the SAME site.
theorem accepted_action (s : Subject) (c : Certificate) (os : List Occ)
 (role : Nat) (ρ : Zkc.Source.LocalArithmetic.Env)
 (hc : check s c (view os role s.site ρ) = true)
 (hr : s.expr.eval ρ [] < Zkc.Protocols.ScalarBytecode.Parameters.modulus) (tail : Zkc.Realization.ByteEncoding.Bytes) :
 reply (request s c (view os role s.site ρ)) = .ok (s.expr.eval ρ []) ∧
 Zkc.Protocols.ScalarBytecode.Codec.readScalar (Zkc.Protocols.ScalarBytecode.Codec.enc (s.expr.eval ρ []) ++ tail) = some (s.expr.eval ρ [],tail) := by
 constructor
 · simp [reply, request, hc, local_source s c os role ρ hc, hr]
 · exact Zkc.Protocols.ScalarBytecode.Codec.scalar_complete _ hr tail

-- The raw egress premise is obtained by executing the range guard, not algebra.
theorem successful_egress (s : Subject) (c : Certificate) (os : List Occ)
 (role : Nat) (ρ : Zkc.Source.LocalArithmetic.Env) (n : Nat)
 (hc : check s c (view os role s.site ρ) = true)
 (ho : reply (request s c (view os role s.site ρ)) = .ok n) :
 n = s.expr.eval ρ [] ∧ n < Zkc.Protocols.ScalarBytecode.Parameters.modulus := by
 have hs := local_source s c os role ρ hc
 simp only [reply, request, ne_eq, not_true_eq_false, ↓reduceIte, hc, hs] at ho
 split at ho
 next hr => cases ho; exact ⟨rfl,hr⟩
 next => contradiction

def handler : Zkc.Semantics.OperationContract.Handler signature Zkc.Source.LocalArithmetic.Memory String :=
 fun r m => (reply r,m,["pure-scalar-eval"])
theorem handler_lawful : Zkc.Semantics.OperationContract.LawfulHandler handler := by
 intro r m _
 exact reply_legal r

end Zkc.Protocols.ScalarBytecode.CheckedExpression
