#ifndef ZKC_INTERFACES_CATALOGTYPE_TD
#define ZKC_INTERFACES_CATALOGTYPE_TD
include "mlir/IR/AttrTypeBase.td"
include "mlir/IR/Interfaces.td"
def CatalogTypeInterface : TypeInterface<"CatalogTypeInterface"> {
  let cppNamespace = "::zkc";
  let description = [{
    Observe a native type's catalog constructor and ordered static arguments.
    Domain and Slot identities are StringAttr, complete types are TypeAttr,
    and naturals are unsigned 64-bit IntegerAttr. This is an observation of
    existing native storage, not another stored type or an admission result.
    Shared carriers such as builtin integers may return no application.
    Membership supplies no profile, codec, physical installation or proof.
    Nominal variants retain their own structural identity and alternatives;
    they do not pretend to be a catalog constructor.
  }];
  let methods = [InterfaceMethod<"Observe the catalog application, if any",
    "std::optional<::zkc::CatalogTypeApplication>", "getCatalogApplication">];
}
#endif
