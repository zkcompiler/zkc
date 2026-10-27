#ifndef ZKC_DIALECT_PROTOCOL_IR_ORACLETYPES_TD
#define ZKC_DIALECT_PROTOCOL_IR_ORACLETYPES_TD

include "zkc/Dialect/Protocol/IR/OracleAttrs.td"

def OracleHandle : TypeDef<ProtocolDialect, "OracleHandle"> {
  let mnemonic = "oracle";
  let summary = "logical role-family handle with an occurrence-selected anchor";
  let parameters = (ins "::zkc::protocol_ir::OracleKindAttr":$kind);
  let assemblyFormat = "`<` $kind `>`";
  let genVerifyDecl = 1;
}

// The default uint64_t field parser admits negative two's-complement values.
// A logical cardinality instead rejects negatives before narrowing.
def OracleSequenceMaximum : AttrOrTypeParameter<"uint64_t", "nonnegative maximum length"> {
  let parser = [{ [&]() -> ::mlir::FailureOr<uint64_t> {
    auto location = $_parser.getCurrentLocation();
    ::llvm::APInt value;
    if ($_parser.parseInteger(value))
      return ::mlir::failure();
    if (value.isNegative() || value.getActiveBits() > 64) {
      $_parser.emitError(location, "oracle sequence maximum must be a uint64 natural");
      return ::mlir::failure();
    }
    return value.getZExtValue();
  }() }];
}

def OracleSequence : TypeDef<ProtocolDialect, "OracleSequence"> {
  let mnemonic = "oracle_sequence";
  let summary = "bounded ordered sequence of logical oracle handles";
  let parameters = (ins "::zkc::protocol_ir::OracleKindAttr":$kind,
                        OracleSequenceMaximum:$maximum);
  let assemblyFormat = "`<` $kind `,` $maximum `>`";
  let genVerifyDecl = 1;
}

#endif
