include "mlir/IR/AttrTypeBase.td"
include "mlir/Interfaces/SideEffectInterfaces.td"
include "zkc/Interfaces/SourceOpInterface.td"
include "zkc/Dialect/Constraints.td"
def ServiceDialect : Dialect {
  let name = "service";
  let cppNamespace = "::zkc::service";
  let useDefaultTypePrinterParser = 1;
}
def Count : TypeDef<ServiceDialect, "Count"> {
  let mnemonic = "count";
  let summary = "service count";
}
def Vector : TypeDef<ServiceDialect, "Vector"> {
  let mnemonic = "vector";
  let summary = "service vector";
}
def Predicate : TypeDef<ServiceDialect, "Predicate"> {
  let mnemonic = "predicate";
  let summary = "service predicate";
}
class ServiceOp<string name, list<Trait> traits>
    : Op<ServiceDialect, name,
         !listconcat(traits, [DeclareOpInterfaceMethods<SourceOpInterface>])> {
  let hasVerifier = 1;
}
def RequestOp : ServiceOp<"request", [MemoryEffects<[MemWrite]>]> {
  let summary = "Request a vector whose length is determined by the argument";
  let arguments = (ins Zkc_Flow:$before, Count:$count);
  let results = (outs Zkc_Flow:$after, Vector:$value);
}
def SendOp : ServiceOp<"send", [MemoryEffects<[MemWrite]>]> {
  let summary = "Send a count and return whether it is zero";
  let arguments = (ins Zkc_Flow:$before, Count:$count);
  let results = (outs Zkc_Flow:$after, Predicate:$value);
}
def RequestAndSendOp
    : ServiceOp<"request_and_send", [MemoryEffects<[MemWrite]>]> {
  let summary = "Request a vector and send its sum within one source operation";
  let arguments = (ins Zkc_Flow:$before, Count:$count);
  let results = (outs Zkc_Flow:$after, Predicate:$value);
}
def SumOp : ServiceOp<"sum", [Pure]> {
  let summary = "Sum the natural representatives of the vector entries";
  let arguments = (ins Vector:$vector);
  let results = (outs Count:$value);
}
// Negative-control operation: identical descriptor and signature, wrong
// identity.
def ForeignSendOp : ServiceOp<"foreign_send", [MemoryEffects<[MemWrite]>]> {
  let arguments = (ins Zkc_Flow:$before, Count:$count);
  let results = (outs Zkc_Flow:$after, Predicate:$value);
}
