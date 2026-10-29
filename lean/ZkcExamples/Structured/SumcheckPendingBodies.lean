module

public import Zkc.Source.Structured.ProtocolOperations

@[expose] public section

/-! Typed source patterns used by the Sumcheck mathematical library.
Applicability requires complete typed body equality in the admitted source;
names and signatures alone provide no law. Generated scalar library associations
prove these equalities in the kernel. -/
namespace ZkcExamples.Structured.SumcheckPendingBodies
open Zkc.Source Zkc.Source.Structured

abbrev pendingHelper : Helper := ⟨"zkl_c0a3a2b8b5f989e0e9c138a171631d20dc8bd296769b6ee7636d2d79a8518ba0", .local, [.field "bls12-381.fr"], [.vector "bls12-381.fr", .field "bls12-381.fr"]⟩

def pendingBody : Region dialect [.field "bls12-381.fr"] [.vector "bls12-381.fr", .field "bls12-381.fr"] :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.exec (.vectorEmpty "bls12-381.fr")) .nil .nil <|
  .ret (.cons .here (.cons (.there .here) .nil))

abbrev openClaimHelper : Helper := ⟨"zkl_e8df957aab384c1d5416600c13a571512206e97abfbf6e0e9cddac5c84860d07", .local, [.vector "bls12-381.fr", .field "bls12-381.fr"], [.vector "bls12-381.fr", .field "bls12-381.fr"]⟩

def openClaimBody : Region dialect [.vector "bls12-381.fr", .field "bls12-381.fr"] [.vector "bls12-381.fr", .field "bls12-381.fr"] :=
  .ret (.cons .here (.cons (.there .here) .nil))

abbrev atPrefixHelper : Helper := ⟨"zkl_c36a2d2c6bd38573735fb9b90d1a3848c562d2c1f688234e2b669408e9c9eea9", .local, [.vector "bls12-381.fr", .field "bls12-381.fr"], [.vector "bls12-381.fr", .field "bls12-381.fr"]⟩

def atPrefixBody : Region dialect [.vector "bls12-381.fr", .field "bls12-381.fr"] [.vector "bls12-381.fr", .field "bls12-381.fr"] :=
  .ret (.cons .here (.cons (.there .here) .nil))

end ZkcExamples.Structured.SumcheckPendingBodies
