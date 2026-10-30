#ifndef ZKC_DIALECT_RUNTIME_IR_RUNTIMEATTRS_TD
#define ZKC_DIALECT_RUNTIME_IR_RUNTIMEATTRS_TD
include "mlir/IR/AttrTypeBase.td"
include "mlir/IR/EnumAttr.td"
include "zkc/Dialect/Runtime/IR/RuntimeDialect.td"
def RuntimeAssetReference : AttrDef<RuntimeDialect, "AssetReference"> {
  let mnemonic = "asset";
  let summary = "an asset format and exact digest, without authorization";
  let parameters = (ins StringRefParameter<>:$format,
    "::mlir::DenseI8ArrayAttr":$digest);
  let assemblyFormat = "`<` $format `,` $digest `>`";
  let genVerifyDecl = 1;
}
def RuntimeOriginStepKind : I32EnumAttr<"OriginStepKind", "source path step", [
  I32EnumAttrCase<"Apply", 0, "apply">,
  I32EnumAttrCase<"Repeat", 1, "repeat">
]> {
  let cppNamespace = "::zkc::runtime";
  let genSpecializedAttr = 0;
}
def RuntimeOriginStep : AttrDef<RuntimeDialect, "OriginStep"> {
  let mnemonic = "origin_step";
  let parameters = (ins EnumParameter<RuntimeOriginStepKind>:$kind,
    StringRefParameter<>:$protocol, StringRefParameter<>:$site);
  let assemblyFormat = "`<` $kind `,` $protocol `,` $site `>`";
  let genVerifyDecl = 1;
}
def RuntimeQueryOrigin : AttrDef<RuntimeDialect, "QueryOrigin"> {
  let mnemonic = "query_origin";
  let parameters = (ins StringRefParameter<>:$protocol,
    StringRefParameter<>:$site, "uint64_t":$serviceInput,
    StringRefParameter<>:$service, StringRefParameter<>:$method,
    StringRefParameter<>:$owner);
  let assemblyFormat = "`<` $protocol `,` $site `,` $serviceInput `,` $service `,` $method `,` $owner `>`";
  let genVerifyDecl = 1;
}
def RuntimeMessageOrigin : AttrDef<RuntimeDialect, "MessageOrigin"> {
  let mnemonic = "message_origin";
  let parameters = (ins StringRefParameter<>:$protocol,
    StringRefParameter<>:$site, StringRefParameter<>:$schema,
    StringRefParameter<>:$sender, StringRefParameter<>:$receiver);
  let assemblyFormat = "`<` $protocol `,` $site `,` $schema `,` $sender `,` $receiver `>`";
  let genVerifyDecl = 1;
}
def RuntimeStartOrigin : AttrDef<RuntimeDialect, "StartOrigin"> {
  let mnemonic = "start_origin";
  let parameters = (ins StringRefParameter<>:$protocol, StringRefParameter<>:$site);
  let assemblyFormat = "`<` $protocol `,` $site `>`";
  let genVerifyDecl = 1;
}
def RuntimeNativeOrigin : AttrDef<RuntimeDialect, "NativeOrigin"> {
  let mnemonic = "origin";
  let summary = "bounded source-relative occurrence without transcript authority";
  let parameters = (ins StringRefParameter<>:$entry,
    OptionalArrayRefParameter<"::zkc::runtime::OriginStepAttr">:$path,
    "::mlir::Attribute":$event);
  let assemblyFormat = "`<` $entry (`path` `[` $path^ `]`)? `,` $event `>`";
  let genVerifyDecl = 1;
}
#endif
