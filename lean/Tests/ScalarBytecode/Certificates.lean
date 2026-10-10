import Zkc.Protocols.ScalarBytecode.Certificates

set_option autoImplicit false

namespace Tests.ScalarBytecode.Certificates
open Zkc.Compiler.Arithmetic.Dag Zkc.Protocols.ScalarBytecode.CheckedExpression Zkc.Protocols.ScalarBytecode.Certificates

def future : Subject := ⟨"fixture",32,.input 33⟩
def futureCert : Certificate := ⟨"fixture",32,[.input 33]⟩
example : check future futureCert (view occurrences 0 32 (fun _ => 7)) = false := by decide
def badQ : Subject := ⟨"legal-malicious-raw",32,.lit 2305843009213697249⟩
def badQCert : Certificate := ⟨"legal-malicious-raw",32,[.lit 2305843009213697249]⟩
example : check badQ badQCert (fun _ => none) = true := by decide
example : reply (request badQ badQCert (fun _ => none)) = .reject "Zkc.Protocols.ScalarBytecode.CheckedExpression-R-NONCANONICAL" := by rfl

end Tests.ScalarBytecode.Certificates
