include "zkc/Contracts/Declarations/Schema.td"
def FSort : ZKC_Sort<"Field">;
def GSort : ZKC_Sort<"Group">;
def FDomain : ZKC_Domain<FSort>;
def GDomain : ZKC_Domain<GSort>;
def F : ZKC_Root<"F", FDomain>;
def G : ZKC_Root<"G", GDomain>;
def Scalar : ZKC_Member<"Scalar", GDomain, FDomain>;
def GS : ZKC_Project<G, Scalar>;
def Element : ZKC_Type<"field", [FDomain]>;
def GroupElement : ZKC_Type<"group", [GDomain]>;
def Ring : ZKC_Capability<"CommRing", [FDomain]>;
def Field : ZKC_Capability<"Field", [FDomain]>;
def Multiply : ZKC_Operation<"field.mul", [F],
    [ZKC_Apply<Element, [F]>, ZKC_Apply<Element, [F]>],
    [ZKC_Apply<Element, [F]>], [ZKC_Holds<Ring, [F]>]>;
def ExportMultiply : ZKC_OperationExport<"zkc::algebra", "mul", Multiply, ["left", "right"]>;
def ExportElement : ZKC_TypeExport<"zkc::algebra", "Element", Element>;
def MultiplyOperator : ZKC_Operator<"*", [Element, Element], Multiply, [0, 1]>;
