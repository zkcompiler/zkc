#ifndef ZKC_DIALECT_TYPE_BINDINGS_TD
#define ZKC_DIALECT_TYPE_BINDINGS_TD
include "mlir/IR/AttrTypeBase.td"
include "zkc/Contracts/Declarations/Schema.td"

// One ordinary function per owner. Include generated fragments at file scope,
// after the owner's private callbacks/aliases have been declared. The generator
// opens cppNamespace; helper symbols are resolved in that namespace.
class ZKC_TypeAdapterOwner<string ns, string function> {
  string cppNamespace = ns;
  string cppFunction = function;
}
class ZKC_TypeBinding<ZKC_Type logical> {
  ZKC_Type logicalType = logical;
}
class ZKC_DirectBinding<ZKC_Type logical, TypeDef native, string helper,
                        ZKC_TypeAdapterOwner table> : ZKC_TypeBinding<logical> {
  TypeDef nativeType = native;
  string cppHelper = helper;
  ZKC_TypeAdapterOwner owner = table;
}
// Heads are fully qualified native C++ class names (also for builtin carriers).
// They describe all recognized heads, not arbitrary predicates. Tagged sharing
// between custom bindings is allowed; runtime encoding must still be unique.
class ZKC_CustomBinding<ZKC_Type logical, list<string> heads, string decode,
                        string encode, ZKC_TypeAdapterOwner table>
    : ZKC_TypeBinding<logical> {
  list<string> nativeHeads = heads;
  string cppDecode = decode;
  string cppEncode = encode;
  ZKC_TypeAdapterOwner owner = table;
}
class ZKC_UnavailableBinding<ZKC_Type logical, string explanation>
    : ZKC_TypeBinding<logical> {
  string reason = explanation;
}
// Syntax carriers have their own coverage obligations; no fake ZKC_Type record.
class ZKC_SpecialType<string constructor> { string name = constructor; }
class ZKC_SpecialBinding<ZKC_SpecialType logical, list<string> heads,
                         string decode, string encode,
                         ZKC_TypeAdapterOwner table> {
  ZKC_SpecialType specialType = logical;
  list<string> nativeHeads = heads;
  string cppDecode = decode;
  string cppEncode = encode;
  ZKC_TypeAdapterOwner owner = table;
}
#endif
