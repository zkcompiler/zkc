import Tools.Artifact.Codec
import Tools.Interactive.GenericTypes

set_option autoImplicit false
private def Except.isError {α : Type} {ε : Type} : Except ε α → Bool
  | .error _ => true
  | .ok _ => false

private instance {α ε : Type} [BEq α] [BEq ε] : BEq (Except ε α) where
  beq a b := match a,b with
    | .ok x, .ok y => x == y
    | .error x, .error y => x == y
    | _,_ => false

namespace Tests.MatrixReference
open Tools.Interactive ScalarReference Zkc.Algebra

private def fixture (d : Domain) : Data (Scalar d) :=
  .matrix ⟨2,3,[⟨0,1,3⟩,⟨1,0,4⟩,⟨1,2,-1⟩]⟩
private def suite (d : Domain) : Bool :=
  compute d "matrix.mul_vector" [] [fixture d,.vector [2,5,7]] == .ok [.vector [15,1]] &&
  compute d "matrix.transpose_mul_vector" [] [fixture d,.vector [2,3]] == .ok [.vector [12,6,-3]] &&
  compute d "matrix.bilinear" [] [fixture d,.vector [2,3],.vector [2,5,7]] == .ok [.field 33] &&
  compute d "matrix.shape_check" ["2","3"] [fixture d] == .ok [.boolean true] &&
  compute d "matrix.shape_check" ["3","2"] [fixture d] == .ok [.boolean false] &&
  compute d "matrix.mul_vector" [] [fixture d,.vector [2,5]] == .error "matrix-shape" &&
  compute d "matrix.transpose_mul_vector" [] [fixture d,.vector [2,5,7]] == .error "matrix-shape" &&
  compute d "matrix.bilinear" [] [fixture d,.vector [2],.vector [2,5,7]] == .error "matrix-shape" &&
  compute d "matrix.shape_check" ["65537","0"] [fixture d] == .error "kernel-attributes" &&
  compute d "matrix.shape_check" ["01","0"] [fixture d] == .error "noncanonical-natural" &&
  compute d "matrix.mul_vector" [] [.matrix ⟨2,0,[]⟩,.vector []] == .ok [.vector [0,0]] &&
  compute d "matrix.transpose_mul_vector" [] [.matrix ⟨0,3,[]⟩,.vector []] == .ok [.vector [0,0,0]] &&
  compute d "matrix.bilinear" [] [.matrix ⟨0,3,[]⟩,.vector [],.vector [1,2,3]] == .ok [.field 0]

example : suite .bls = true := by native_decide
example : suite .ristretto = true := by native_decide
example : suite .koalaBear = true := by native_decide
example : suite .bn254 = true := by native_decide

private def wireSuite (d : Domain) : Except String Bool := do
  let m := fixture d
  let b ← Tools.Artifact.arithmeticWire d m
  let decoded ← Tools.Artifact.decodeArithmeticWire d "matrix" b
  let other := if d == .bls then Domain.ristretto else Domain.bls
  let header := Tools.Artifact.magic.push (← Tools.Artifact.arithmeticTag d "matrix")
  let zeros := header ++ Tools.Artifact.little 4 0 ++ Tools.Artifact.little 4 3 ++ Tools.Artifact.little 4 0
  let empty ← Tools.Artifact.decodeArithmeticWire d "matrix" zeros
  let mut allTruncated := true
  for n in [:b.size] do
    allTruncated := allTruncated && (Tools.Artifact.decodeArithmeticWire d "matrix" (b.extract 0 n)).isError
  return decoded == m && allTruncated && empty == .matrix ⟨0,3,[]⟩ &&
    (Tools.Artifact.decodeArithmeticWire other "matrix" b).isError &&
    (Tools.Artifact.decodeArithmeticWire d "matrix" (b.push 0)).isError &&
    (Tools.Artifact.arithmeticWire d (.matrix ⟨2,3,[⟨0,1,0⟩]⟩)).isError &&
    (Tools.Artifact.arithmeticWire d (.matrix ⟨2,3,[⟨0,1,1⟩,⟨0,1,2⟩]⟩)).isError &&
    (Tools.Artifact.arithmeticWire d (.matrix ⟨2,3,[⟨1,1,1⟩,⟨0,1,2⟩]⟩)).isError &&
    (Tools.Artifact.arithmeticWire d (.matrix ⟨2,3,[⟨2,0,1⟩]⟩)).isError &&
    (Tools.Artifact.arithmeticWire d (.matrix ⟨65537,0,[]⟩)).isError
example : wireSuite .bls = .ok true := by native_decide
example : wireSuite .ristretto = .ok true := by native_decide
example : wireSuite .koalaBear = .ok true := by native_decide
example : wireSuite .bn254 = .ok true := by native_decide
private def malformedWireSuite (d : Domain) : Except String Bool := do
  let header := Tools.Artifact.magic.push (← Tools.Artifact.arithmeticTag d "matrix")
  let width := Tools.Artifact.arithmeticWidth d
  let wire := fun (rows columns : Nat) (entries : List (Nat × Nat × Nat)) =>
    header ++ Tools.Artifact.little 4 rows ++ Tools.Artifact.little 4 columns ++
      Tools.Artifact.little 4 entries.length ++ entries.foldl (fun b (r,c,a) =>
        b ++ Tools.Artifact.little 4 r ++ Tools.Artifact.little 4 c ++ Tools.Artifact.little width a) ByteArray.empty
  let bad := [wire 2 3 [(0,1,0)], wire 2 3 [(0,1,d.modulus)],
    wire 2 3 [(0,1,3),(0,1,4)], wire 2 3 [(1,0,3),(0,1,4)],
    wire 2 3 [(2,0,1)], wire 2 3 [(0,3,1)], wire 0 3 [(0,0,1)],
    wire 65537 0 [], wire (2^32-1) (2^32-1) [],
    header ++ Tools.Artifact.little 4 65536 ++ Tools.Artifact.little 4 65536 ++ Tools.Artifact.little 4 1048577]
  return bad.all fun bytes => (Tools.Artifact.decodeArithmeticWire d "matrix" bytes).isError
example : malformedWireSuite .bls = .ok true := by native_decide
example : malformedWireSuite .ristretto = .ok true := by native_decide
example : malformedWireSuite .koalaBear = .ok true := by native_decide
example : malformedWireSuite .bn254 = .ok true := by native_decide
end Tests.MatrixReference
