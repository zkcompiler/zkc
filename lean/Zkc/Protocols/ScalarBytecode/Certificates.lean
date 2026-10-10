import Zkc.Protocols.ScalarBytecode.CheckedExpression

set_option autoImplicit false

namespace Zkc.Protocols.ScalarBytecode.Certificates
open Zkc.Compiler.Arithmetic.Dag Zkc.Protocols.ScalarBytecode.CheckedExpression
def occurrences : List Occ := [⟨23,23,0⟩,⟨24,24,0⟩,⟨25,25,0⟩,⟨26,26,0⟩,⟨28,28,0⟩,⟨29,29,0⟩,⟨30,30,0⟩,⟨31,31,0⟩,⟨33,33,0⟩]
def round1Left : Subject := ⟨"sha256:5337dec2241ef509cde1d670883918e0040f3cda434cbe407dfd249bcd9a3fda",27,(.mod (.add (.mod (.add (.mod (.add (.input 24) (.input 24)) 2305843009213697249) (.input 25)) 2305843009213697249) (.input 26)) 2305843009213697249)⟩
def round1LeftCert : Certificate := ⟨"sha256:5337dec2241ef509cde1d670883918e0040f3cda434cbe407dfd249bcd9a3fda",27,[(.mod 0 2305843009213697249),(.add 1 0),(.input 26),(.mod 0 2305843009213697249),(.add 1 0),(.input 25),(.mod 0 2305843009213697249),(.add 0 0),(.input 24)]⟩
theorem round1Left_checked (ρ : Zkc.Source.LocalArithmetic.Env) : check round1Left round1LeftCert (view occurrences 0 round1Left.site ρ) = true := by
  simp [check, round1Left, round1LeftCert, expand, expandOne, wellFormed, bounded, Instr.checkInputs, view, Zkc.Source.LocalArithmetic.project, available, occurrences]
theorem round1Left_joined (ρ : Zkc.Source.LocalArithmetic.Env) (tail : Zkc.Realization.ByteEncoding.Bytes) :
 reply (request round1Left round1LeftCert (view occurrences 0 round1Left.site ρ)) = .ok (round1Left.expr.eval ρ []) ∧
 Zkc.Protocols.ScalarBytecode.Codec.readScalar (Zkc.Protocols.ScalarBytecode.Codec.enc (round1Left.expr.eval ρ []) ++ tail) = some (round1Left.expr.eval ρ [],tail) := by
 apply accepted_action _ _ _ _ _ (round1Left_checked ρ)
 exact Nat.mod_lt _ (by decide : 0 < Zkc.Protocols.ScalarBytecode.Parameters.modulus)
def round1Right : Subject := ⟨"sha256:5337dec2241ef509cde1d670883918e0040f3cda434cbe407dfd249bcd9a3fda",27,(.input 23)⟩
def round1RightCert : Certificate := ⟨"sha256:5337dec2241ef509cde1d670883918e0040f3cda434cbe407dfd249bcd9a3fda",27,[(.input 23)]⟩
theorem round1Right_checked (ρ : Zkc.Source.LocalArithmetic.Env) : check round1Right round1RightCert (view occurrences 0 round1Right.site ρ) = true := by
  simp [check, round1Right, round1RightCert, expand, expandOne, wellFormed, bounded, Instr.checkInputs, view, Zkc.Source.LocalArithmetic.project, available, occurrences]
def round2Left : Subject := ⟨"sha256:5337dec2241ef509cde1d670883918e0040f3cda434cbe407dfd249bcd9a3fda",32,(.mod (.add (.mod (.add (.mod (.add (.input 29) (.input 29)) 2305843009213697249) (.input 30)) 2305843009213697249) (.input 31)) 2305843009213697249)⟩
def round2LeftCert : Certificate := ⟨"sha256:5337dec2241ef509cde1d670883918e0040f3cda434cbe407dfd249bcd9a3fda",32,[(.mod 0 2305843009213697249),(.add 1 0),(.input 31),(.mod 0 2305843009213697249),(.add 1 0),(.input 30),(.mod 0 2305843009213697249),(.add 0 0),(.input 29)]⟩
theorem round2Left_checked (ρ : Zkc.Source.LocalArithmetic.Env) : check round2Left round2LeftCert (view occurrences 0 round2Left.site ρ) = true := by
  simp [check, round2Left, round2LeftCert, expand, expandOne, wellFormed, bounded, Instr.checkInputs, view, Zkc.Source.LocalArithmetic.project, available, occurrences]
theorem round2Left_joined (ρ : Zkc.Source.LocalArithmetic.Env) (tail : Zkc.Realization.ByteEncoding.Bytes) :
 reply (request round2Left round2LeftCert (view occurrences 0 round2Left.site ρ)) = .ok (round2Left.expr.eval ρ []) ∧
 Zkc.Protocols.ScalarBytecode.Codec.readScalar (Zkc.Protocols.ScalarBytecode.Codec.enc (round2Left.expr.eval ρ []) ++ tail) = some (round2Left.expr.eval ρ [],tail) := by
 apply accepted_action _ _ _ _ _ (round2Left_checked ρ)
 exact Nat.mod_lt _ (by decide : 0 < Zkc.Protocols.ScalarBytecode.Parameters.modulus)
def round2Right : Subject := ⟨"sha256:5337dec2241ef509cde1d670883918e0040f3cda434cbe407dfd249bcd9a3fda",32,(.mod (.add (.input 24) (.mod (.add (.mod (.mul (.input 25) (.input 28)) 2305843009213697249) (.mod (.mul (.input 26) (.mod (.mul (.input 28) (.input 28)) 2305843009213697249)) 2305843009213697249)) 2305843009213697249)) 2305843009213697249)⟩
def round2RightCert : Certificate := ⟨"sha256:5337dec2241ef509cde1d670883918e0040f3cda434cbe407dfd249bcd9a3fda",32,[(.mod 0 2305843009213697249),(.add 11 0),(.mod 0 2305843009213697249),(.add 5 0),(.mod 0 2305843009213697249),(.mul 2 0),(.mod 0 2305843009213697249),(.mul 3 3),(.input 26),(.mod 0 2305843009213697249),(.mul 1 0),(.input 28),(.input 25),(.input 24)]⟩
theorem round2Right_checked (ρ : Zkc.Source.LocalArithmetic.Env) : check round2Right round2RightCert (view occurrences 0 round2Right.site ρ) = true := by
  simp [check, round2Right, round2RightCert, expand, expandOne, wellFormed, bounded, Instr.checkInputs, view, Zkc.Source.LocalArithmetic.project, available, occurrences]
theorem round2Right_joined (ρ : Zkc.Source.LocalArithmetic.Env) (tail : Zkc.Realization.ByteEncoding.Bytes) :
 reply (request round2Right round2RightCert (view occurrences 0 round2Right.site ρ)) = .ok (round2Right.expr.eval ρ []) ∧
 Zkc.Protocols.ScalarBytecode.Codec.readScalar (Zkc.Protocols.ScalarBytecode.Codec.enc (round2Right.expr.eval ρ []) ++ tail) = some (round2Right.expr.eval ρ [],tail) := by
 apply accepted_action _ _ _ _ _ (round2Right_checked ρ)
 exact Nat.mod_lt _ (by decide : 0 < Zkc.Protocols.ScalarBytecode.Parameters.modulus)
def finalLeft : Subject := ⟨"sha256:5337dec2241ef509cde1d670883918e0040f3cda434cbe407dfd249bcd9a3fda",34,(.mod (.add (.input 29) (.mod (.add (.mod (.mul (.input 30) (.input 33)) 2305843009213697249) (.mod (.mul (.input 31) (.mod (.mul (.input 33) (.input 33)) 2305843009213697249)) 2305843009213697249)) 2305843009213697249)) 2305843009213697249)⟩
def finalLeftCert : Certificate := ⟨"sha256:5337dec2241ef509cde1d670883918e0040f3cda434cbe407dfd249bcd9a3fda",34,[(.mod 0 2305843009213697249),(.add 11 0),(.mod 0 2305843009213697249),(.add 5 0),(.mod 0 2305843009213697249),(.mul 2 0),(.mod 0 2305843009213697249),(.mul 3 3),(.input 31),(.mod 0 2305843009213697249),(.mul 1 0),(.input 33),(.input 30),(.input 29)]⟩
theorem finalLeft_checked (ρ : Zkc.Source.LocalArithmetic.Env) : check finalLeft finalLeftCert (view occurrences 0 finalLeft.site ρ) = true := by
  simp [check, finalLeft, finalLeftCert, expand, expandOne, wellFormed, bounded, Instr.checkInputs, view, Zkc.Source.LocalArithmetic.project, available, occurrences]
theorem finalLeft_joined (ρ : Zkc.Source.LocalArithmetic.Env) (tail : Zkc.Realization.ByteEncoding.Bytes) :
 reply (request finalLeft finalLeftCert (view occurrences 0 finalLeft.site ρ)) = .ok (finalLeft.expr.eval ρ []) ∧
 Zkc.Protocols.ScalarBytecode.Codec.readScalar (Zkc.Protocols.ScalarBytecode.Codec.enc (finalLeft.expr.eval ρ []) ++ tail) = some (finalLeft.expr.eval ρ [],tail) := by
 apply accepted_action _ _ _ _ _ (finalLeft_checked ρ)
 exact Nat.mod_lt _ (by decide : 0 < Zkc.Protocols.ScalarBytecode.Parameters.modulus)
def finalRight : Subject := ⟨"sha256:5337dec2241ef509cde1d670883918e0040f3cda434cbe407dfd249bcd9a3fda",34,(.mod (.add (.mod (.mul (.input 28) (.input 33)) 2305843009213697249) (.input 28)) 2305843009213697249)⟩
def finalRightCert : Certificate := ⟨"sha256:5337dec2241ef509cde1d670883918e0040f3cda434cbe407dfd249bcd9a3fda",34,[(.mod 0 2305843009213697249),(.add 0 3),(.mod 0 2305843009213697249),(.mul 1 0),(.input 33),(.input 28)]⟩
theorem finalRight_checked (ρ : Zkc.Source.LocalArithmetic.Env) : check finalRight finalRightCert (view occurrences 0 finalRight.site ρ) = true := by
  simp [check, finalRight, finalRightCert, expand, expandOne, wellFormed, bounded, Instr.checkInputs, view, Zkc.Source.LocalArithmetic.project, available, occurrences]
theorem finalRight_joined (ρ : Zkc.Source.LocalArithmetic.Env) (tail : Zkc.Realization.ByteEncoding.Bytes) :
 reply (request finalRight finalRightCert (view occurrences 0 finalRight.site ρ)) = .ok (finalRight.expr.eval ρ []) ∧
 Zkc.Protocols.ScalarBytecode.Codec.readScalar (Zkc.Protocols.ScalarBytecode.Codec.enc (finalRight.expr.eval ρ []) ++ tail) = some (finalRight.expr.eval ρ [],tail) := by
 apply accepted_action _ _ _ _ _ (finalRight_checked ρ)
 exact Nat.mod_lt _ (by decide : 0 < Zkc.Protocols.ScalarBytecode.Parameters.modulus)

end Zkc.Protocols.ScalarBytecode.Certificates
