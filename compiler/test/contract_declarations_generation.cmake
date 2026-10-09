# Only the project's neutral include root is provided: no LLVM/MLIR .td files.
file(MAKE_DIRECTORY "${ZKC_DECLARATION_TEST_DIRECTORY}")
set(failures "")
function(declaration_case name definitions expected_error)
  set(input "${ZKC_DECLARATION_TEST_DIRECTORY}/${name}.td")
  file(WRITE "${input}" "include \"minimal.td\"\n${definitions}\n")
  foreach(action gen-contract-declarations dump-contract-declarations)
    set(output "${ZKC_DECLARATION_TEST_DIRECTORY}/${name}-${action}.txt")
    file(REMOVE "${output}")
    execute_process(COMMAND "${ZKC_TABLEGEN}" "-${action}"
      -I "${ZKC_DECLARATION_INCLUDE}" -I "${ZKC_DECLARATION_FIXTURES}"
      "${input}" -o "${output}"
      RESULT_VARIABLE result OUTPUT_VARIABLE stdout ERROR_VARIABLE stderr)
    file(WRITE "${output}.log" "${stdout}${stderr}")
    if(expected_error STREQUAL "")
      if(NOT result EQUAL 0)
        list(APPEND failures "${name}/${action}: ${stderr}")
      endif()
    else()
      string(FIND "${stderr}" "${expected_error}" position)
      if(NOT result MATCHES "^[1-9][0-9]*$" OR position EQUAL -1 OR EXISTS "${output}")
        list(APPEND failures "${name}/${action}: expected '${expected_error}': ${stderr}")
      endif()
    endif()
  endforeach()
  set(failures "${failures}" PARENT_SCOPE)
endfunction()
declaration_case(valid "" "")
declaration_case(duplicate-type [=[
def Duplicate : ZKC_Type<"field", [FDomain]>;
]=] "duplicate type ownership")
declaration_case(duplicate-operation [=[
def Duplicate : ZKC_Operation<"field.mul", [], [], []>;
]=] "duplicate operation ownership")
declaration_case(duplicate-capability [=[
def Duplicate : ZKC_Capability<"Field", [FDomain]>;
]=] "duplicate capability ownership")
declaration_case(duplicate-member [=[
def Duplicate : ZKC_Member<"Scalar", GDomain, FDomain>;
]=] "duplicate associated member ownership")
declaration_case(duplicate-rule [=[
def A : ZKC_Implication<Field, Ring>;
def B : ZKC_Implication<Field, Ring>;
]=] "duplicate capability implication")
declaration_case(rule-arity [=[
def GroupCapability : ZKC_Capability<"Group", [GDomain]>;
def Bad : ZKC_Implication<GroupCapability, Ring>;
]=] "capability implication parameter mismatch")
declaration_case(unscoped [=[
def Missing : ZKC_Operation<"bad.scope", [], [ZKC_Apply<Element, [F]>], []>;
]=] "unscoped typed reference")
declaration_case(projection-order [=[
def Missing : ZKC_Operation<"bad.scope", [GS, G], [], []>;
]=] "associated projection must follow its scoped parent")
declaration_case(projection-kind [=[
def BadProjection : ZKC_Project<F, Scalar>;
def Bad : ZKC_Operation<"bad.member", [F, BadProjection], [], []>;
]=] "associated member parameter mismatch")
declaration_case(duplicate-root [=[
def AnotherF : ZKC_Root<"F", FDomain>;
def Bad : ZKC_Operation<"bad.root", [F, AnotherF], [], []>;
]=] "invalid or duplicate formal root")
declaration_case(duplicate-term [=[
def Bad : ZKC_Operation<"bad.term", [G, GS, GS], [], []>;
]=] "duplicate scoped projection")
declaration_case(constructor-arity [=[
def Bad : ZKC_Operation<"bad.arity", [], [ZKC_Apply<Element>], []>;
]=] "parameter arity mismatch")
declaration_case(constructor-kind [=[
def Bad : ZKC_Operation<"bad.kind", [G], [ZKC_Apply<Element, [G]>], []>;
]=] "parameter kind or sort mismatch")
declaration_case(predicate-kind [=[
def Bad : ZKC_Operation<"bad.predicate", [G], [], [], [ZKC_Holds<Ring, [G]>]>;
]=] "parameter kind or sort mismatch")
declaration_case(predicate-arity [=[
def Bad : ZKC_Operation<"bad.predicate", [], [], [], [ZKC_Holds<Ring, []>]>;
]=] "parameter arity mismatch")
declaration_case(structural-type-application [=[
def N : ZKC_Natural<4>;
def ScalarType : ZKC_Apply<Element, [F]>;
def Bulk : ZKC_Type<"bulk", [TypeParameter, NatParameter], PrivateImmutable>;
def Good : ZKC_Operation<"bulk.identity", [F, N, ScalarType],
  [ZKC_Apply<Bulk, [ScalarType, N]>], [ZKC_Apply<Bulk, [ScalarType, N]>]>;
]=] "")
declaration_case(application-forward-reference [=[
def ScalarType : ZKC_Apply<Element, [F]>;
def Bad : ZKC_Operation<"bad.application", [ScalarType, F], [], []>;
]=] "type application must follow its scoped arguments")
declaration_case(duplicate-application [=[
def A : ZKC_Apply<Element, [F]>;
def B : ZKC_Apply<Element, [F]>;
def Bad : ZKC_Operation<"bad.application", [F, A, B], [], []>;
]=] "duplicate scoped application")
declaration_case(duplicate-natural [=[
def A : ZKC_Natural<4>;
def B : ZKC_Natural<4>;
def Bad : ZKC_Operation<"bad.natural", [A, B], [], []>;
]=] "duplicate scoped constant")
declaration_case(natural-limit [=[
def N : ZKC_Natural<1048577>;
def Bad : ZKC_Operation<"bad.natural", [N], [], []>;
]=] "natural static argument limit")
declaration_case(natural-kind [=[
def N : ZKC_Natural<4> { let parameter = TypeParameter; }
def Bad : ZKC_Operation<"bad.natural", [N], [], []>;
]=] "invalid natural static kind")
declaration_case(application-kind [=[
def A : ZKC_Apply<Element, [F]> { let parameter = NatParameter; }
def Bad : ZKC_Operation<"bad.application", [F, A], [], []>;
]=] "invalid type application kind or head")
declaration_case(common-type-parameter [=[
def Good : ZKC_Type<"new_type", [TypeParameter], PrivateImmutable>;
]=] "")
declaration_case(common-nat-parameter [=[
def Good : ZKC_Type<"new_type", [NatParameter], PrivateImmutable>;
]=] "")
declaration_case(applied-public-custody [=[
def Bad : ZKC_Type<"public_bulk", [TypeParameter]> {
  let custody = PublicValue;
}
]=] "applied types require an explicit complete-type codec model")
declaration_case(reserved-domain-sort [=[
def Bad : ZKC_Sort<"Type">;
]=] "reserved static kind used as a domain sort")
declaration_case(common-operation-type [=[
def T : ZKC_Root<"T", TypeParameter>;
def Good : ZKC_Operation<"new.generic", [T], [], []>;
]=] "")
declaration_case(unknown-parameter-validator [=[
def Unknown : ZKC_Parameters<"ExecuteUserCode", 0, 0>;
def Bad : ZKC_Operation<"bad.validator", [], [], []> { let parameters = Unknown; }
]=] "unsupported parameter validator or bounds")
declaration_case(parameter-bounds [=[
def Wrong : ZKC_Parameters<"FieldLiteral", 0, 1>;
def Bad : ZKC_Operation<"bad.bounds", [], [], []> { let parameters = Wrong; }
]=] "unsupported parameter validator or bounds")
declaration_case(permissions [=[
def Bad : ZKC_Type<"bad", [], Affine, 1, 1>;
]=] "incoherent type permissions")
declaration_case(literal-field-missing [=[
def Bad : ZKC_Operation<"new.literal", [F], [], [ZKC_Apply<Element,[F]>]> {
  let parameters = FieldLiteral;
}
]=] "field literal validator requires exactly one field term")
declaration_case(literal-field-unscoped [=[
def Bad : ZKC_Operation<"new.literal", [], [], []> {
  let parameters = FieldLiteral;
  let parameterField = F;
}
]=] "unscoped parameter field")
declaration_case(literal-field-sort [=[
def Bad : ZKC_Operation<"new.literal", [G], [], []> {
  let parameters = FieldLiteral;
  let parameterField = G;
}
]=] "parameter field must have Field sort")
declaration_case(literal-field-projection [=[
def Good : ZKC_Operation<"new.literal", [G,GS], [], [ZKC_Apply<Element,[GS]>]> {
  let parameters = FieldLiteral;
  let parameterField = GS;
}
]=] "")
declaration_case(unknown-stage [=[
def Unknown : ZKC_Stage<"EventuallySource">;
def Bad : ZKC_Operation<"bad.stage", [], [], []> { let stage = Unknown; }
]=] "unknown authoring stage")
declaration_case(retired-effect [=[
def Bad : ZKC_Operation<"bad.effect", [], [], []> { let effect = "local"; }
]=] "Value 'effect' unknown")
declaration_case(duplicate-facet [=[
def Bad : ZKC_Operation<"bad.facet", [], [], []> { let facets = [PublicReplay, PublicReplay]; }
]=] "duplicate semantic facet")
declaration_case(unknown-facet [=[
def Unknown : ZKC_Facet;
def Bad : ZKC_Operation<"bad.facet", [], [], []> { let facets = [Unknown]; }
]=] "unsupported semantic facet")
declaration_case(facet-port [=[
def Bad : ZKC_Operation<"bad.facet", [], [], []> { let facets = [ZKC_History<0,0>]; }
]=] "facet port outside signature")
declaration_case(history-successor [=[
def Bad : ZKC_Operation<"bad.history", [F,G], [ZKC_Apply<Element,[F]>], [ZKC_Apply<GroupElement,[G]>]> {
  let facets = [ZKC_History<0,0>];
}
]=] "history successor type mismatch")
declaration_case(facet-carrier [=[
def Bad : ZKC_Operation<"bad.sample", [F], [ZKC_Apply<Element,[F]>], [ZKC_Apply<Element,[F]>]> {
  let facets = [ZKC_Sampling<Entropy,FieldSample>];
}
]=] "facet port constructor mismatch")
declaration_case(source-export-stage [=[
def Hidden : ZKC_Operation<"hidden.draw", [], [], []> { let stage = Construction; }
def Leak : ZKC_OperationExport<"zkc::random", "draw", Hidden, []>;
]=] "source export requires a source operation")
declaration_case(duplicate-export [=[
def Duplicate : ZKC_OperationExport<"zkc::algebra", "mul", Multiply, ["x","y"]>;
]=] "duplicate source export ownership")
declaration_case(capability-type-export-collision [=[
def Collision : ZKC_CapabilityExport<"zkc::algebra", "Element", Field>;
]=] "duplicate source export ownership")
declaration_case(capability-operation-export-collision [=[
def Collision : ZKC_CapabilityExport<"zkc::algebra", "mul", Field>;
]=] "duplicate source export ownership")
declaration_case(capability-export-collision [=[
def First : ZKC_CapabilityExport<"zkc::algebra", "Field", Field>;
def Collision : ZKC_CapabilityExport<"zkc::algebra", "Field", Ring>;
]=] "duplicate source export ownership")
declaration_case(type-operation-export-collision [=[
def Collision : ZKC_OperationExport<"zkc::algebra", "Element", Multiply, ["left","right"]>;
]=] "duplicate source export ownership")
# Qualified carrier paths distinguish these names. Neither a global name
# restriction nor one export per constructor belongs in the generator.
declaration_case(type-export-names-in-different-modules [=[
def OtherElement : ZKC_TypeExport<"zkc::curve", "Element", GroupElement>;
]=] "")
declaration_case(type-export-alias [=[
def Alias : ZKC_TypeExport<"zkc::algebra", "FieldElement", Element>;
]=] "")
declaration_case(capability-export-names-in-different-modules [=[
def OtherElement : ZKC_CapabilityExport<"zkc::curve", "Element", Field>;
def OtherMultiply : ZKC_CapabilityExport<"zkc::curve", "mul", Ring>;
]=] "")
declaration_case(label-arity [=[
def Bad : ZKC_OperationExport<"zkc::algebra", "bad", Multiply, ["x"]>;
]=] "source export input label arity")
declaration_case(label-duplicate [=[
def Bad : ZKC_OperationExport<"zkc::algebra", "bad", Multiply, ["x","x"]>;
]=] "invalid or duplicate input label")
declaration_case(operator-duplicate [=[
def Bad : ZKC_Operator<"*", [Element,Element], Multiply, [0,1]>;
]=] "duplicate operator tuple")
declaration_case(operator-bijection [=[
def Bad : ZKC_Operator<"+", [Element,Element], Multiply, [0,0]>;
]=] "operator order must be a port bijection")
declaration_case(operator-head [=[
def Bad : ZKC_Operator<"+", [GroupElement,Element], Multiply, [0,1]>;
]=] "operator operand constructor mismatch")
declaration_case(operator-stage [=[
def Hidden : ZKC_Operation<"hidden.mul", [F], [ZKC_Apply<Element,[F]>,ZKC_Apply<Element,[F]>], [ZKC_Apply<Element,[F]>]> { let stage = Physical; }
def Bad : ZKC_Operator<"+", [Element,Element], Hidden, [0,1]>;
]=] "operator requires an exported source operation")
declaration_case(alias-labels [=[
def Alias : ZKC_OperationExport<"zkc::algebra", "product", Multiply, ["x","y"]>;
]=] "operation aliases must share input labels")
declaration_case(family-case-duplicate [=[
def Family : ZKC_TypeFamily<"family">;
def A : ZKC_TypeFamilyCase<Family, Element, Element>;
def B : ZKC_TypeFamilyCase<Family, Element, Element>;
]=] "duplicate source family case")
declaration_case(family-case-kind [=[
def Family : ZKC_TypeFamily<"family">;
def Bad : ZKC_TypeFamilyCase<Family, Element, GroupElement>;
]=] "source family parameter mismatch")
declaration_case(empty-family [=[
def Family : ZKC_TypeFamily<"family">;
]=] "source family requires a case")
declaration_case(associated-type-kind [=[
def Bad : ZKC_AssociatedType<FDomain, "Element", GroupElement>;
]=] "associated source type parameter mismatch")
declaration_case(associated-type-duplicate [=[
def A : ZKC_AssociatedType<FDomain, "Element", Element>;
def B : ZKC_AssociatedType<FDomain, "Element", Element>;
]=] "duplicate associated source type")
declaration_case(capability-export-arity [=[
def Binary : ZKC_Capability<"Binary", [FDomain,FDomain]>;
def Bad : ZKC_CapabilityExport<"zkc::algebra", "Binary", Binary>;
]=] "source capability requires a unary domain predicate")
declaration_case(good-family [=[
def Family : ZKC_TypeFamily<"family">;
def Case : ZKC_TypeFamilyCase<Family, Element, Element>;
def Export : ZKC_TypeExport<"zkc::algebra", "Family", Family>;
def Member : ZKC_AssociatedType<FDomain, "Element", Element>;
def Capability : ZKC_CapabilityExport<"zkc::algebra", "Field", Field>;
def Alias : ZKC_OperationExport<"zkc::algebra", "product", Multiply, ["left","right"]>;
]=] "")
declaration_case(type-nat-generation [=[
include "type_nat.td"
]=] "")
declaration_case(type-nat-reversed [=[
include "type_nat.td"
def Wrong : ZKC_Operation<"fixture.wrong", [ElementType, Length],
    [ZKC_Apply<ArrayType, [Length, ElementType]>], []> {
  let commonGeneric = 0;
}
]=] "parameter kind or sort mismatch")
# Complete-Type ports are construction observation inputs, never an untyped
# escape hatch for common programs or generated result types.
declaration_case(direct-type-common [=[
def T : ZKC_Root<"T", TypeParameter>;
def Bad : ZKC_Operation<"bad.direct", [T], [T], []>;
]=] "direct Type ports require a scoped construction type")
declaration_case(direct-type-output [=[
def T : ZKC_Root<"T", TypeParameter>;
def Bad : ZKC_Operation<"bad.direct", [T], [], [T]> {
  let stage = Construction; let commonGeneric = 0;
}
]=] "direct Type ports require a scoped construction type")
declaration_case(direct-type-unobserved [=[
def T : ZKC_Root<"T", TypeParameter>;
def Bad : ZKC_Operation<"bad.direct", [T], [T], []> {
  let stage = Construction; let commonGeneric = 0;
}
]=] "complete-type port must be an observation payload")
declaration_case(direct-type-observation [=[
def T : ZKC_Root<"T", TypeParameter>;
def State : ZKC_Type<"transcript", [], Affine, 0, 0>;
def Good : ZKC_Operation<"good.direct", [T], [ZKC_Apply<State>, T], [ZKC_Apply<State>]> {
  let stage = Construction; let commonGeneric = 0;
  let facets = [ZKC_Observation<0,1,0>, ZKC_History<0,0>];
}
]=] "")
# Kinded fixture must generate successfully but never become common admission.
execute_process(COMMAND "${ZKC_TABLEGEN}" -dump-contract-declarations
  -I "${ZKC_DECLARATION_INCLUDE}" "${ZKC_DECLARATION_FIXTURES}/type_nat.td"
  RESULT_VARIABLE result OUTPUT_VARIABLE fixture ERROR_VARIABLE stderr)
if(NOT result EQUAL 0)
  list(APPEND failures "Type/Nat fixture failed: ${stderr}")
else()
  string(JSON kind GET "${fixture}" types 0 parameters 0 kind)
  string(JSON natural GET "${fixture}" types 0 parameters 1 kind)
  string(JSON admitted GET "${fixture}" types 0 commonGeneric)
  if(NOT kind STREQUAL "Type" OR NOT natural STREQUAL "Nat" OR admitted)
    list(APPEND failures "Type/Nat fixture acquired common admission")
  endif()
endif()
# Byte-for-byte reproducibility of both production generation actions.
foreach(action gen-contract-declarations dump-contract-declarations)
  execute_process(COMMAND "${ZKC_TABLEGEN}" "-${action}"
    -I "${ZKC_DECLARATION_INCLUDE}" "${ZKC_DECLARATION_INCLUDE}/zkc/Contracts/Declarations.td"
    RESULT_VARIABLE first_result OUTPUT_VARIABLE first ERROR_VARIABLE stderr)
  execute_process(COMMAND "${ZKC_TABLEGEN}" "-${action}"
    -I "${ZKC_DECLARATION_INCLUDE}" "${ZKC_DECLARATION_INCLUDE}/zkc/Contracts/Declarations.td"
    RESULT_VARIABLE second_result OUTPUT_VARIABLE second ERROR_VARIABLE second_stderr)
  if(NOT first_result EQUAL 0 OR NOT second_result EQUAL 0 OR NOT first STREQUAL second)
    list(APPEND failures "nondeterministic ${action}: ${stderr}${second_stderr}")
  endif()
endforeach()
execute_process(COMMAND "${ZKC_TABLEGEN}" -I "${ZKC_DECLARATION_INCLUDE}"
  "${ZKC_DECLARATION_FIXTURES}/minimal.td"
  RESULT_VARIABLE missing_action OUTPUT_VARIABLE stdout ERROR_VARIABLE stderr)
if(missing_action EQUAL 0)
  list(APPEND failures "generation without an explicit action succeeded")
endif()
if(failures)
  list(JOIN failures "\n" diagnostic)
  message(FATAL_ERROR "${diagnostic}")
endif()
message(STATUS "Neutral declarations: structural controls and deterministic output passed")
