#ifndef ZKC_INTERFACES_COLLECTION_TD
#define ZKC_INTERFACES_COLLECTION_TD

include "mlir/IR/AttrTypeBase.td"
include "mlir/IR/Interfaces.td"

def CollectionTypeInterface : TypeInterface<"CollectionTypeInterface"> {
  let cppNamespace = "::zkc";
  let description = [{
    Observation of a collection's nominal family, element, rank and intrinsic
    extents. Interface membership grants no finite-operation, profile, wire,
    custody or implementation admission. Clients check the admitted family
    separately. Learned value extents do not change the logical family.

    An unknown or out-of-range extent is nullopt. Callers must check the rank
    first; nullopt does not establish that an axis exists. A known zero extent
    is distinct from an unknown extent.
  }];
  let methods = [
    InterfaceMethod<"The nominal collection family",
      "::zkc::CollectionKind", "getCollectionKind">,
    InterfaceMethod<"The exact element type",
      "::mlir::Type", "getElementType">,
    InterfaceMethod<"The number of collection axes", "unsigned", "getRank">,
    InterfaceMethod<"The type-guaranteed extent, or nullopt",
      "std::optional<uint64_t>", "getStaticExtent", (ins "unsigned":$axis)>
  ];
}

#endif
