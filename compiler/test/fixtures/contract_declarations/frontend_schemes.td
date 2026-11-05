// Complete internal structural installation control.
#ifndef ZKC_TEST_FRONTEND_SCHEMES
#define ZKC_TEST_FRONTEND_SCHEMES
include "zkc/Contracts/Declarations/Schema.td"
def StructuralSchemeRecord0 : ZKC_ContractPattern<"contract", 0, [], "", -1>;
def StructuralSchemeRecord1 : ZKC_ContractPattern<"sequence", -1, [StructuralSchemeRecord0], "unsized", -1>;
def StructuralSchemeRecord2 : ZKC_SchemePort<"descriptor", [StructuralSchemeRecord1], "">;
def StructuralSchemeRecord3 : ZKC_ContractPattern<"contract", 0, [], "", -1>;
def StructuralSchemeRecord4 : ZKC_SchemePort<"descriptor", [StructuralSchemeRecord3], "">;
def StructuralSchemeRecord5 : ZKC_ContractPattern<"contract", 0, [], "", -1>;
def StructuralSchemeRecord6 : ZKC_ContractPattern<"sequence", -1, [StructuralSchemeRecord5], "unsized", -1>;
def StructuralSchemeRecord7 : ZKC_FrontendScheme<"DescriptorAppend", "Append", ["Contract"], [], [StructuralSchemeRecord2, StructuralSchemeRecord4], StructuralSchemeRecord6> { int ordinal = 0; }
def StructuralSchemeRecord8 : ZKC_ContractPattern<"contract", 0, [], "", -1>;
def StructuralSchemeRecord9 : ZKC_ContractPattern<"sequence", -1, [StructuralSchemeRecord8], "unsized", -1>;
def StructuralSchemeRecord10 : ZKC_SchemePort<"descriptor", [StructuralSchemeRecord9], "">;
def StructuralSchemeRecord11 : ZKC_ContractPattern<"contract", 0, [], "", -1>;
def StructuralSchemeRecord12 : ZKC_ContractPattern<"sequence", -1, [StructuralSchemeRecord11], "unsized", -1>;
def StructuralSchemeRecord13 : ZKC_SchemePort<"descriptor", [StructuralSchemeRecord12], "">;
def StructuralSchemeRecord14 : ZKC_ContractPattern<"contract", 0, [], "", -1>;
def StructuralSchemeRecord15 : ZKC_ContractPattern<"sequence", -1, [StructuralSchemeRecord14], "unsized", -1>;
def StructuralSchemeRecord16 : ZKC_FrontendScheme<"DescriptorConcat", "Concat", ["Contract"], [], [StructuralSchemeRecord10, StructuralSchemeRecord13], StructuralSchemeRecord15> { int ordinal = 1; }
def StructuralSchemeRecord17 : ZKC_ContractPattern<"contract", 0, [], "", -1>;
def StructuralSchemeRecord18 : ZKC_ContractPattern<"sequence", -1, [StructuralSchemeRecord17], "extent", 1>;
def StructuralSchemeRecord19 : ZKC_SchemePort<"descriptor", [StructuralSchemeRecord18], "">;
def StructuralSchemeRecord20 : ZKC_ContractPattern<"contract", 0, [], "", -1>;
def StructuralSchemeRecord21 : ZKC_SchemePort<"descriptor", [StructuralSchemeRecord20], "">;
def StructuralSchemeRecord22 : ZKC_ContractPattern<"contract", 0, [], "", -1>;
def StructuralSchemeRecord23 : ZKC_ContractPattern<"sequence", -1, [StructuralSchemeRecord22], "extent", 1>;
def StructuralSchemeRecord24 : ZKC_FrontendScheme<"DescriptorReplace", "Replace", ["Contract", "OptionalExtent"], [NatParameter], [StructuralSchemeRecord19, StructuralSchemeRecord21], StructuralSchemeRecord23> { int ordinal = 2; }
def StructuralSchemeRecord25 : ZKC_ContractPattern<"contract", 0, [], "", -1>;
def StructuralSchemeRecord26 : ZKC_ContractPattern<"sequence", -1, [StructuralSchemeRecord25], "extent", 1>;
def StructuralSchemeRecord27 : ZKC_SchemePort<"descriptor", [StructuralSchemeRecord26], "">;
def StructuralSchemeRecord28 : ZKC_ContractPattern<"contract", 0, [], "", -1>;
def StructuralSchemeRecord29 : ZKC_ContractPattern<"sequence", -1, [StructuralSchemeRecord28], "unsized", -1>;
def StructuralSchemeRecord30 : ZKC_FrontendScheme<"DescriptorForgetExtent", "ForgetExtent", ["Contract", "OptionalExtent"], [], [StructuralSchemeRecord27], StructuralSchemeRecord29> { int ordinal = 3; }
def StructuralSchemeRecord31 : ZKC_ContractPattern<"contract", 0, [], "", -1>;
def StructuralSchemeRecord32 : ZKC_ContractPattern<"sequence", -1, [StructuralSchemeRecord31], "unsized", -1>;
def StructuralSchemeRecord33 : ZKC_SchemePort<"descriptor", [StructuralSchemeRecord32], "">;
def StructuralSchemeRecord34 : ZKC_ContractPattern<"contract", 0, [], "", -1>;
def StructuralSchemeRecord35 : ZKC_ContractPattern<"sequence", -1, [StructuralSchemeRecord34], "static", 0>;
def StructuralSchemeRecord36 : ZKC_FrontendScheme<"DescriptorCheckExtent", "CheckExtent", ["Contract"], [NatParameter], [StructuralSchemeRecord33], StructuralSchemeRecord35> { int ordinal = 4; }
def StructuralSchemeRecord37 : ZKC_ContractPattern<"contract", 0, [], "", -1>;
def StructuralSchemeRecord38 : ZKC_ContractPattern<"contract", 1, [], "", -1>;
def StructuralSchemeRecord39 : ZKC_SchemePort<"selectedView", [StructuralSchemeRecord37, StructuralSchemeRecord38], "">;
def StructuralSchemeRecord40 : ZKC_ContractPattern<"contract", 0, [], "", -1>;
def StructuralSchemeRecord41 : ZKC_SchemePort<"descriptor", [StructuralSchemeRecord40], "">;
def StructuralSchemeRecord42 : ZKC_ContractPattern<"contract", 1, [], "", -1>;
def StructuralSchemeRecord43 : ZKC_SchemePort<"descriptor", [StructuralSchemeRecord42], "">;
def StructuralSchemeRecord44 : ZKC_ContractPattern<"contract", 1, [], "", -1>;
def StructuralSchemeRecord45 : ZKC_FrontendScheme<"DescriptorFold", "Fold", ["Contract", "Contract"], [NatParameter], [StructuralSchemeRecord39, StructuralSchemeRecord41, StructuralSchemeRecord43], StructuralSchemeRecord44> { int ordinal = 5; }
def StructuralSchemeRecord46 : ZKC_ContractHeadDeclaration<"descriptor.product", "zkc::descriptor", "Product", "descriptor_product", 0> { int ordinal = 0; }
def StructuralSchemeRecord47 : ZKC_ContractHeadDeclaration<"descriptor.sequence", "zkc::descriptor", "Sequence", "descriptor_sequence", 0> { int ordinal = 1; }
def StructuralSchemeRecord48 : ZKC_ContractPattern<"contract", 0, [], "", -1>;
def StructuralSchemeRecord49 : ZKC_ContractPattern<"sequence", -1, [StructuralSchemeRecord48], "unsized", -1>;
def StructuralSchemeRecord50 : ZKC_SchemePort<"descriptor", [StructuralSchemeRecord49], "xs">;
def StructuralSchemeRecord51 : ZKC_ContractPattern<"contract", 0, [], "", -1>;
def StructuralSchemeRecord52 : ZKC_SchemePort<"descriptor", [StructuralSchemeRecord51], "item">;
def StructuralSchemeRecord53 : ZKC_ContractPattern<"contract", 0, [], "", -1>;
def StructuralSchemeRecord54 : ZKC_ContractPattern<"sequence", -1, [StructuralSchemeRecord53], "unsized", -1>;
def StructuralSchemeRecord55 : ZKC_ViewSchemeDeclaration<"descriptor.append", "zkc::descriptor", "append", [], [StructuralSchemeRecord50, StructuralSchemeRecord52], StructuralSchemeRecord54, "DescriptorAppend", 0> { int ordinal = 2; }
def StructuralSchemeRecord56 : ZKC_ContractPattern<"contract", 0, [], "", -1>;
def StructuralSchemeRecord57 : ZKC_ContractPattern<"sequence", -1, [StructuralSchemeRecord56], "unsized", -1>;
def StructuralSchemeRecord58 : ZKC_SchemePort<"descriptor", [StructuralSchemeRecord57], "left">;
def StructuralSchemeRecord59 : ZKC_ContractPattern<"contract", 0, [], "", -1>;
def StructuralSchemeRecord60 : ZKC_ContractPattern<"sequence", -1, [StructuralSchemeRecord59], "unsized", -1>;
def StructuralSchemeRecord61 : ZKC_SchemePort<"descriptor", [StructuralSchemeRecord60], "right">;
def StructuralSchemeRecord62 : ZKC_ContractPattern<"contract", 0, [], "", -1>;
def StructuralSchemeRecord63 : ZKC_ContractPattern<"sequence", -1, [StructuralSchemeRecord62], "unsized", -1>;
def StructuralSchemeRecord64 : ZKC_ViewSchemeDeclaration<"descriptor.concat", "zkc::descriptor", "concat", [], [StructuralSchemeRecord58, StructuralSchemeRecord61], StructuralSchemeRecord63, "DescriptorConcat", 0> { int ordinal = 3; }
def StructuralSchemeRecord65 : ZKC_SourceStatic<"Index", NatParameter>;
def StructuralSchemeRecord66 : ZKC_ContractPattern<"contract", 0, [], "", -1>;
def StructuralSchemeRecord67 : ZKC_ContractPattern<"sequence", -1, [StructuralSchemeRecord66], "extent", 1>;
def StructuralSchemeRecord68 : ZKC_SchemePort<"descriptor", [StructuralSchemeRecord67], "xs">;
def StructuralSchemeRecord69 : ZKC_ContractPattern<"contract", 0, [], "", -1>;
def StructuralSchemeRecord70 : ZKC_SchemePort<"descriptor", [StructuralSchemeRecord69], "item">;
def StructuralSchemeRecord71 : ZKC_ContractPattern<"contract", 0, [], "", -1>;
def StructuralSchemeRecord72 : ZKC_ContractPattern<"sequence", -1, [StructuralSchemeRecord71], "extent", 1>;
def StructuralSchemeRecord73 : ZKC_ViewSchemeDeclaration<"descriptor.replace", "zkc::descriptor", "replace", [StructuralSchemeRecord65], [StructuralSchemeRecord68, StructuralSchemeRecord70], StructuralSchemeRecord72, "DescriptorReplace", 0> { int ordinal = 4; }
def StructuralSchemeRecord74 : ZKC_ContractPattern<"contract", 0, [], "", -1>;
def StructuralSchemeRecord75 : ZKC_ContractPattern<"sequence", -1, [StructuralSchemeRecord74], "extent", 1>;
def StructuralSchemeRecord76 : ZKC_SchemePort<"descriptor", [StructuralSchemeRecord75], "xs">;
def StructuralSchemeRecord77 : ZKC_ContractPattern<"contract", 0, [], "", -1>;
def StructuralSchemeRecord78 : ZKC_ContractPattern<"sequence", -1, [StructuralSchemeRecord77], "unsized", -1>;
def StructuralSchemeRecord79 : ZKC_ViewSchemeDeclaration<"descriptor.unsized", "zkc::descriptor", "unsized", [], [StructuralSchemeRecord76], StructuralSchemeRecord78, "DescriptorForgetExtent", 0> { int ordinal = 5; }
def StructuralSchemeRecord80 : ZKC_SourceStatic<"Length", NatParameter>;
def StructuralSchemeRecord81 : ZKC_ContractPattern<"contract", 0, [], "", -1>;
def StructuralSchemeRecord82 : ZKC_ContractPattern<"sequence", -1, [StructuralSchemeRecord81], "unsized", -1>;
def StructuralSchemeRecord83 : ZKC_SchemePort<"descriptor", [StructuralSchemeRecord82], "xs">;
def StructuralSchemeRecord84 : ZKC_ContractPattern<"contract", 0, [], "", -1>;
def StructuralSchemeRecord85 : ZKC_ContractPattern<"sequence", -1, [StructuralSchemeRecord84], "static", 0>;
def StructuralSchemeRecord86 : ZKC_ViewSchemeDeclaration<"descriptor.sized", "zkc::descriptor", "sized", [StructuralSchemeRecord80], [StructuralSchemeRecord83], StructuralSchemeRecord85, "DescriptorCheckExtent", 0> { int ordinal = 6; }
def StructuralSchemeRecord87 : ZKC_SourceStatic<"Count", NatParameter>;
def StructuralSchemeRecord88 : ZKC_ContractPattern<"contract", 0, [], "", -1>;
def StructuralSchemeRecord89 : ZKC_ContractPattern<"contract", 1, [], "", -1>;
def StructuralSchemeRecord90 : ZKC_SchemePort<"selectedView", [StructuralSchemeRecord88, StructuralSchemeRecord89], "member">;
def StructuralSchemeRecord91 : ZKC_ContractPattern<"contract", 0, [], "", -1>;
def StructuralSchemeRecord92 : ZKC_SchemePort<"descriptor", [StructuralSchemeRecord91], "context">;
def StructuralSchemeRecord93 : ZKC_ContractPattern<"contract", 1, [], "", -1>;
def StructuralSchemeRecord94 : ZKC_SchemePort<"descriptor", [StructuralSchemeRecord93], "seed">;
def StructuralSchemeRecord95 : ZKC_ContractPattern<"contract", 1, [], "", -1>;
def StructuralSchemeRecord96 : ZKC_ViewSchemeDeclaration<"descriptor.fold", "zkc::descriptor", "fold", [StructuralSchemeRecord87], [StructuralSchemeRecord90, StructuralSchemeRecord92, StructuralSchemeRecord94], StructuralSchemeRecord95, "DescriptorFold", 0> { int ordinal = 7; }
#endif
