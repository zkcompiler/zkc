#ifndef ZKC_DIALECT_PROTOCOL_IR_ORACLEATTRS_TD
#define ZKC_DIALECT_PROTOCOL_IR_ORACLEATTRS_TD

include "mlir/IR/AttrTypeBase.td"
include "zkc/Dialect/Protocol/IR/ProtocolDialect.td"

// The library identity selects Data/Query/Answer associations. It is not a
// commitment scheme, leaf layout, occurrence anchor or serialized native type.
def OracleKind : AttrDef<ProtocolDialect, "OracleKind"> {
  let mnemonic = "oracle_kind";
  let summary = "checked oracle library kind with typed static arguments";
  let parameters = (ins StringRefParameter<"Library kind identity">:$identity,
                        "::mlir::ArrayAttr":$arguments);
  let assemblyFormat = "`<` $identity `,` $arguments `>`";
  let genVerifyDecl = 1;
  let extraClassDeclaration = [{
    ::mlir::Type getDataType() const;
    ::mlir::Type getQueryType() const;
    ::mlir::Type getAnswerType() const;
    ::std::vector<::zkc::protocol::OracleShapeDimension> getShapeDimensions() const;
    ::std::optional<uint64_t> getStaticShape(::llvm::StringRef name) const;
    ::mlir::LogicalResult verifyShapeBounds(
        ::llvm::function_ref<::mlir::InFlightDiagnostic()> emit,
        ::mlir::DictionaryAttr bounds) const;
  }];
}

#endif
