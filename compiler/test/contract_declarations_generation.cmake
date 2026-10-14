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
declaration_case(resource-participant-family [=[
def Bad : ZKC_Type<"token", [], Affine, 0, 1> { let participants = 1; }
]=] "participant families require Copy data")
declaration_case(message-without-constructor [=[
def Bad : ZKC_Type<"opaque", [], PrivateImmutable, 1, 1> { let message = 1; }
]=] "message frames require native decoder authority")
declaration_case(mathematics-without-local-data [=[
def Bad : ZKC_Type<"static", [], PublicValue, 1, 1> {
  let nativeLocal = 0; let mathematical = 1;
}
]=] "mathematical native data requires reusable local data")

declaration_case(managed-history-missing-state [=[
def Bad : ZKC_Operation<"bad.history", [], [], []> {
  let facets = [ManagedHistory];
}
]=] "managed authoring requires an explicit source history transition")
declaration_case(managed-history-data-state [=[
def State : ZKC_Type<"state", [], PrivateImmutable, 1, 1>;
def Bad : ZKC_Operation<"bad.history", [], [ZKC_Apply<State>], [ZKC_Apply<State>]> {
  let facets = [ZKC_History<0, 0>, ManagedHistory];
}
]=] "facet port constructor mismatch")
declaration_case(managed-history-late-stage [=[
def State : ZKC_Type<"transcript", [], Affine, 0, 0>;
def Bad : ZKC_Operation<"bad.history", [], [ZKC_Apply<State>], [ZKC_Apply<State>]> {
  let stage = Construction;
  let facets = [ZKC_History<0, 0>, ManagedHistory];
}
]=] "managed authoring requires an explicit source history transition")
declaration_case(source-history-missing-state [=[
def Bad : ZKC_Operation<"bad.history", [], [], []> {
  let facets = [SourceHistory];
}
]=] "source history requires an explicit data-state transition")
declaration_case(source-history-managed-state [=[
def State : ZKC_Type<"state", [], Affine, 0, 0>;
def Bad : ZKC_Operation<"bad.history", [], [ZKC_Apply<State>], [ZKC_Apply<State>]> {
  let facets = [ZKC_History<0, 0>, SourceHistory];
}
]=] "source history state must be copyable and discardable data")
declaration_case(source-history-successor [=[
def State : ZKC_Type<"state", [], PrivateImmutable, 1, 1>;
def Other : ZKC_Type<"other", [], PrivateImmutable, 1, 1>;
def Bad : ZKC_Operation<"bad.history", [], [ZKC_Apply<State>], [ZKC_Apply<Other>]> {
  let facets = [ZKC_History<0, 0>, SourceHistory];
}
]=] "history successor type mismatch")
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
declaration_case(unknown-property [=[
def Bad : ZKC_Operation<"bad.property", [], [], []> { let unexpected = "value"; }
]=] "Value 'unexpected' unknown")
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
declaration_case(duplicate-export [=[
def Duplicate : ZKC_TypeExport<"zkc::algebra", "Element", Element>;
]=] "duplicate source export ownership")
declaration_case(capability-type-export-collision [=[
def Collision : ZKC_CapabilityExport<"zkc::algebra", "Element", Field>;
]=] "duplicate source export ownership")
declaration_case(capability-export-collision [=[
def First : ZKC_CapabilityExport<"zkc::algebra", "Field", Field>;
def Collision : ZKC_CapabilityExport<"zkc::algebra", "Field", Ring>;
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
# Mathematical laws are declaration facets. These are consistency controls,
# not claims about a provider's implementation of an equation.
declaration_case(mathematical-field [=[
include "zkc/Contracts/Declarations/Mathematical.td"
def Good : ZKC_Operation<"law.add", [F],
  [ZKC_Apply<Element,[F]>, ZKC_Apply<Element,[F]>], [ZKC_Apply<Element,[F]>],
  [ZKC_Holds<Field,[F]>]> { let facets = [ZKC_Mathematical<MathFieldAdd>]; }
]=] "")
declaration_case(mathematical-different-root [=[
include "zkc/Contracts/Declarations/Mathematical.td"
def H : ZKC_Root<"H", FDomain>;
def Bad : ZKC_Operation<"law.add", [F,H],
  [ZKC_Apply<Element,[F]>, ZKC_Apply<Element,[H]>], [ZKC_Apply<Element,[F]>],
  [ZKC_Holds<Field,[F]>]> { let facets = [ZKC_Mathematical<MathFieldAdd>]; }
]=] "mathematical signature nominal ports or associated scalar mismatch")
declaration_case(mathematical-result-root [=[
include "zkc/Contracts/Declarations/Mathematical.td"
def H : ZKC_Root<"H", FDomain>;
def Bad : ZKC_Operation<"law.add", [F,H],
  [ZKC_Apply<Element,[F]>, ZKC_Apply<Element,[F]>], [ZKC_Apply<Element,[H]>],
  [ZKC_Holds<Field,[H]>]> { let facets = [ZKC_Mathematical<MathFieldAdd>]; }
]=] "mathematical signature nominal ports or associated scalar mismatch")
declaration_case(mathematical-capability [=[
include "zkc/Contracts/Declarations/Mathematical.td"
def Bad : ZKC_Operation<"law.add", [F],
  [ZKC_Apply<Element,[F]>, ZKC_Apply<Element,[F]>], [ZKC_Apply<Element,[F]>],
  [ZKC_Holds<Ring,[F]>]> { let facets = [ZKC_Mathematical<MathFieldAdd>]; }
]=] "mathematical capability on exact nominal domain required")
declaration_case(mathematical-duplicate [=[
include "zkc/Contracts/Declarations/Mathematical.td"
def Bad : ZKC_Operation<"law.add", [F],
  [ZKC_Apply<Element,[F]>, ZKC_Apply<Element,[F]>], [ZKC_Apply<Element,[F]>],
  [ZKC_Holds<Field,[F]>]> {
  let facets = [ZKC_Mathematical<MathFieldAdd>, ZKC_Mathematical<MathFieldMultiply>];
}
]=] "duplicate semantic facet")
declaration_case(mathematical-associated-scalar [=[
include "zkc/Contracts/Declarations/Mathematical.td"
def Action : ZKC_Capability<"ScalarAction", [GDomain]>;
def Good : ZKC_Operation<"law.scale", [G,GS],
  [ZKC_Apply<GroupElement,[G]>, ZKC_Apply<Element,[GS]>], [ZKC_Apply<GroupElement,[G]>],
  [ZKC_Holds<Action,[G]>]> { let facets = [ZKC_Mathematical<MathGroupScale>]; }
]=] "")
declaration_case(mathematical-wrong-scalar [=[
include "zkc/Contracts/Declarations/Mathematical.td"
def Action : ZKC_Capability<"ScalarAction", [GDomain]>;
def Bad : ZKC_Operation<"law.scale", [G,F],
  [ZKC_Apply<GroupElement,[G]>, ZKC_Apply<Element,[F]>], [ZKC_Apply<GroupElement,[G]>],
  [ZKC_Holds<Action,[G]>]> { let facets = [ZKC_Mathematical<MathGroupScale>]; }
]=] "mathematical signature nominal ports or associated scalar mismatch")
declaration_case(mathematical-access-family [=[
include "zkc/Contracts/Declarations/Mathematical.td"
def N : ZKC_Root<"N", NatParameter>;
def Array : ZKC_Type<"field_array", [FDomain,NatParameter], PrivateImmutable>;
def Index : ZKC_Type<"index">;
def Bad : ZKC_Operation<"law.access", [F,N],
  [ZKC_Apply<Array,[F,N]>, ZKC_Apply<Index>], [ZKC_Apply<Element,[F]>],
  [ZKC_Holds<Field,[F]>]> { let facets = [ZKC_Mathematical<MathContainerAt>]; }
]=] "mathematical signature nominal ports or associated scalar mismatch")
declaration_case(linear-wrong-associated-scalar [=[
def Action : ZKC_Capability<"ScalarAction", [GDomain]>;
def Vector : ZKC_Type<"vector", [FDomain], PrivateImmutable>;
def Groups : ZKC_Type<"groups", [GDomain], PrivateImmutable>;
def Bad : ZKC_Operation<"law.msm", [G,F],
  [ZKC_Apply<Vector,[F]>, ZKC_Apply<Groups,[G]>], [ZKC_Apply<GroupElement,[G]>],
  [ZKC_Holds<Action,[G]>]> { let facets = [ZKC_Contraction<0,1>]; }
]=] "linear facet nominal ports or associated scalar mismatch")

function(recipe_case name definitions expected_error)
  set(input "${ZKC_DECLARATION_TEST_DIRECTORY}/recipe-${name}.td")
  file(WRITE "${input}" "include \"zkc/Contracts/Declarations.td\"\ninclude \"${ZKC_DECLARATION_INCLUDE}/../lib/Transforms/RecipeSchema.td\"\n${definitions}\n")
  set(output "${ZKC_DECLARATION_TEST_DIRECTORY}/recipe-${name}.inc")
  file(REMOVE "${output}")
  execute_process(COMMAND "${ZKC_TABLEGEN}" -gen-mathematical-recipes
    -I "${ZKC_DECLARATION_INCLUDE}" "${input}" -o "${output}"
    RESULT_VARIABLE result OUTPUT_VARIABLE stdout ERROR_VARIABLE stderr)
  if(expected_error STREQUAL "")
    if(NOT result EQUAL 0)
      list(APPEND failures "recipe-${name}: ${stderr}")
    endif()
  else()
    string(FIND "${stderr}" "${expected_error}" position)
    if(NOT result MATCHES "^[1-9][0-9]*$" OR position EQUAL -1 OR EXISTS "${output}")
      list(APPEND failures "recipe-${name}: expected '${expected_error}': ${stderr}")
    endif()
  endif()
  set(failures "${failures}" PARENT_SCOPE)
endfunction()
recipe_case(field-lanes [=[
def Good : ZKC_LaneRecipe<OpFieldAdd, OpVectorAdd>;
]=] "")
recipe_case(group-permutation [=[
def Good : ZKC_LaneRecipe<OpCurveScale, OpCurveScaleEach, [1,0]>;
]=] "")
recipe_case(group-wrong-order [=[
def Bad : ZKC_LaneRecipe<OpCurveScale, OpCurveScaleEach>;
]=] "recipe endpoint input nominal type mismatch")
recipe_case(wrong-family [=[
def Bad : ZKC_LaneRecipe<OpFieldAdd, OpFieldAdd>;
]=] "recipe endpoint input nominal type mismatch")
recipe_case(wrong-result [=[
def Bad : ZKC_LaneRecipe<OpFieldMul, OpVectorDot>;
]=] "recipe endpoint result nominal type mismatch")
recipe_case(wrong-static-mapping [=[
def Bad : ZKC_LaneRecipe<OpFieldAdd, OpVectorAdd> { let staticArguments = [1]; }
]=] "recipe requires the source domain root mapping")
recipe_case(missing-meaning [=[
def Bad : ZKC_LaneRecipe<OpFieldInverse, OpVectorInverse>;
]=] "recipe source requires mathematical laws")
recipe_case(missing-endpoint [=[
def Bad : ZKC_LaneRecipe<OpFieldAdd, MissingEndpoint>;
]=] "Variable not defined: 'MissingEndpoint'")
recipe_case(subtraction-reduction [=[
def Bad : ZKC_ReductionRecipe<OpFieldSub, OpVectorSum, "Direct", [0]>;
]=] "reduction recipe requires associative total combiner and empty identity")
recipe_case(msm [=[
def Good : ZKC_ReductionRecipe<OpCurveAdd, OpCurveMsm, "Contraction", [1,0]> {
  let term = OpCurveScale;
}
]=] "")
recipe_case(msm-wrong-domain [=[
def Bad : ZKC_ReductionRecipe<OpCurveAdd, OpCurveMsm, "Contraction", [1,0]> {
  let term = OpCurveScale; let staticSourceOperand = 1;
}
]=] "recipe static source must supply the nominal root, not an associated scalar")
recipe_case(matrix-row [=[
def Good : ZKC_ReductionRecipe<OpFieldAdd, OpMatrixRowDot, "MatrixRow"> {
  let term = OpFieldMul;
}
]=] "")
recipe_case(matrix-index-arity [=[
def Bad : ZKC_ReductionRecipe<OpFieldAdd, OpVectorDot, "MatrixRow"> {
  let term = OpFieldMul;
}
]=] "recipe endpoint arity mismatch")

recipe_case(direct-input-role [=[
def Bad : ZKC_ReductionRecipe<OpFieldAdd, OpVectorSum, "Direct", [1]>;
]=] "direct reduction has exactly one semantic input role")
recipe_case(direct-static-role [=[
def Bad : ZKC_ReductionRecipe<OpFieldAdd, OpVectorSum, "Direct", [0]> {
  let staticSourceOperand = 1;
}
]=] "direct reduction static source must use its single input")
recipe_case(matrix-role-order [=[
def Bad : ZKC_ReductionRecipe<OpFieldAdd, OpMatrixRowDot, "MatrixRow", [1,0]> {
  let term = OpFieldMul;
}
]=] "matrix recipe requires matrix then vector roles")

recipe_case(matrix-contraction-forms [=[
def Bilinear : ZKC_MatrixContractionRecipe<OpFieldAdd, OpFieldMul,
    OpMatrixBilinear, "Bilinear", OpFieldAdd, [0,1,2], [], [0,1]>;
def Rows : ZKC_MatrixContractionRecipe<OpFieldAdd, OpFieldMul,
    OpMatrixMulVector, "Rows", OpVectorAdd, [0,1], [0], [1]>;
def Columns : ZKC_MatrixContractionRecipe<OpFieldAdd, OpFieldMul,
    OpMatrixTransposeMulVector, "Columns", OpVectorAdd, [0,1], [1], [0]>;
]=] "")
recipe_case(matrix-contraction-combiner [=[
def Bad : ZKC_MatrixContractionRecipe<OpFieldSub, OpFieldMul,
    OpMatrixBilinear, "Bilinear", OpFieldAdd, [0,1,2], [], [0,1]>;
]=] "matrix contraction requires field sum and product meanings")
recipe_case(matrix-contraction-term [=[
def Bad : ZKC_MatrixContractionRecipe<OpFieldAdd, OpFieldAdd,
    OpMatrixBilinear, "Bilinear", OpFieldAdd, [0,1,2], [], [0,1]>;
]=] "matrix contraction requires field sum and product meanings")
recipe_case(matrix-contraction-law-premises [=[
def RecipeLaws : ZKC_ScalarLaws<"FieldRing", "FieldBinary"> {
  let associative = 1; let commutative = 1;
  let leftIdentity = "Zero"; let rightIdentity = "Zero";
}
def RecipeMeaning : ZKC_MathematicalIdentity<"FieldAdd", 0> {
  let laws = RecipeLaws;
}
def RecipeF : ZKC_Root<"F", FieldDomain>;
def RecipeAdd : ZKC_Operation<"fixture.add", [RecipeF],
    [ZKC_Apply<TypeField,[RecipeF]>, ZKC_Apply<TypeField,[RecipeF]>],
    [ZKC_Apply<TypeField,[RecipeF]>], [ZKC_Holds<CapabilityField,[RecipeF]>]> {
  let facets = [ZKC_Mathematical<RecipeMeaning>];
}
def Bad : ZKC_MatrixContractionRecipe<RecipeAdd, OpFieldMul,
    OpMatrixBilinear, "Bilinear", OpFieldAdd, [0,1,2], [], [0,1]>;
]=] "matrix contraction requires total commutative field laws")
recipe_case(matrix-contraction-empty-identity [=[
def RecipeLaws : ZKC_ScalarLaws<"FieldRing", "FieldBinary"> {
  let associative = 1; let commutative = 1; let total = 1;
  let leftIdentity = "One"; let rightIdentity = "One";
}
def RecipeMeaning : ZKC_MathematicalIdentity<"FieldAdd", 0> {
  let laws = RecipeLaws;
}
def RecipeF : ZKC_Root<"F", FieldDomain>;
def RecipeAdd : ZKC_Operation<"fixture.add", [RecipeF],
    [ZKC_Apply<TypeField,[RecipeF]>, ZKC_Apply<TypeField,[RecipeF]>],
    [ZKC_Apply<TypeField,[RecipeF]>], [ZKC_Holds<CapabilityField,[RecipeF]>]> {
  let facets = [ZKC_Mathematical<RecipeMeaning>];
}
def Bad : ZKC_MatrixContractionRecipe<RecipeAdd, OpFieldMul,
    OpMatrixBilinear, "Bilinear", OpFieldAdd, [0,1,2], [], [0,1]>;
]=] "matrix contraction requires additive zero and annihilator")
recipe_case(matrix-contraction-form [=[
def Bad : ZKC_MatrixContractionRecipe<OpFieldAdd, OpFieldMul,
    OpMatrixBilinear, "Unknown", OpFieldAdd, [0,1,2], [], [0,1]>;
]=] "unknown matrix contraction form")
recipe_case(matrix-contraction-permutation [=[
def Bad : ZKC_MatrixContractionRecipe<OpFieldAdd, OpFieldMul,
    OpMatrixBilinear, "Bilinear", OpFieldAdd, [0,1,1], [], [0,1]>;
]=] "recipe operand mapping must be a permutation")
recipe_case(matrix-contraction-left-right [=[
def Bad : ZKC_MatrixContractionRecipe<OpFieldAdd, OpFieldMul,
    OpMatrixBilinear, "Bilinear", OpFieldAdd, [0,2,1], [], [0,1]>;
]=] "matrix contraction requires matrix then ordered vector roles")
recipe_case(matrix-contraction-matrix-role [=[
def Bad : ZKC_MatrixContractionRecipe<OpFieldAdd, OpFieldMul,
    OpMatrixMulVector, "Rows", OpVectorAdd, [1,0], [0], [1]>;
]=] "matrix contraction requires matrix then ordered vector roles")
recipe_case(matrix-contraction-operand-arity [=[
def Bad : ZKC_MatrixContractionRecipe<OpFieldAdd, OpFieldMul,
    OpMatrixBilinear, "Bilinear", OpFieldAdd, [0,1], [], [0,1]>;
]=] "matrix contraction operand mapping arity")
recipe_case(matrix-contraction-row-axis [=[
def Bad : ZKC_MatrixContractionRecipe<OpFieldAdd, OpFieldMul,
    OpMatrixMulVector, "Rows", OpVectorAdd, [0,1], [1], [0]>;
]=] "matrix contraction free and reduced axis roles mismatch")
recipe_case(matrix-contraction-column-axis [=[
def Bad : ZKC_MatrixContractionRecipe<OpFieldAdd, OpFieldMul,
    OpMatrixTransposeMulVector, "Columns", OpVectorAdd, [0,1], [0], [1]>;
]=] "matrix contraction free and reduced axis roles mismatch")
recipe_case(matrix-contraction-bilinear-axes [=[
def Bad : ZKC_MatrixContractionRecipe<OpFieldAdd, OpFieldMul,
    OpMatrixBilinear, "Bilinear", OpFieldAdd, [0,1,2], [0], [1]>;
]=] "matrix contraction free and reduced axis roles mismatch")
recipe_case(matrix-contraction-wrong-orientation [=[
def Bad : ZKC_MatrixContractionRecipe<OpFieldAdd, OpFieldMul,
    OpMatrixTransposeMulVector, "Rows", OpVectorAdd, [0,1], [0], [1]>;
]=] "matrix contraction endpoint does not implement axis roles")
recipe_case(matrix-contraction-target-arity [=[
def Bad : ZKC_MatrixContractionRecipe<OpFieldAdd, OpFieldMul,
    OpMatrixBilinear, "Rows", OpVectorAdd, [0,1], [0], [1]>;
]=] "matrix contraction endpoint arity mismatch")
recipe_case(matrix-contraction-target-type [=[
def Bad : ZKC_MatrixContractionRecipe<OpFieldAdd, OpFieldMul,
    OpVectorDot, "Rows", OpVectorAdd, [0,1], [0], [1]>;
]=] "matrix contraction endpoint input nominal type mismatch")
recipe_case(matrix-contraction-target-result [=[
def RecipeF : ZKC_Root<"F", FieldDomain>;
def Wrong : ZKC_Operation<"fixture.matrix_result", [RecipeF],
    [ZKC_Apply<TypeMatrix,[RecipeF]>, ZKC_Apply<TypeVector,[RecipeF]>],
    [ZKC_Apply<TypeField,[RecipeF]>], [ZKC_Holds<CapabilityField,[RecipeF]>]>;
def Bad : ZKC_MatrixContractionRecipe<OpFieldAdd, OpFieldMul,
    Wrong, "Rows", OpVectorAdd, [0,1], [0], [1]>;
]=] "matrix contraction endpoint result nominal type mismatch")
recipe_case(matrix-contraction-target-capability [=[
def RecipeF : ZKC_Root<"F", FieldDomain>;
def Wrong : ZKC_Operation<"fixture.matrix_capability", [RecipeF],
    [ZKC_Apply<TypeMatrix,[RecipeF]>, ZKC_Apply<TypeVector,[RecipeF]>],
    [ZKC_Apply<TypeVector,[RecipeF]>]>;
def Bad : ZKC_MatrixContractionRecipe<OpFieldAdd, OpFieldMul,
    Wrong, "Rows", OpVectorAdd, [0,1], [0], [1]>;
]=] "matrix contraction endpoint requires the source field capability")
recipe_case(matrix-contraction-target-parameters [=[
def RecipeF : ZKC_Root<"F", FieldDomain>;
def Wrong : ZKC_Operation<"fixture.matrix_parameters", [RecipeF],
    [ZKC_Apply<TypeMatrix,[RecipeF]>, ZKC_Apply<TypeVector,[RecipeF]>],
    [ZKC_Apply<TypeVector,[RecipeF]>], [ZKC_Holds<CapabilityField,[RecipeF]>]> {
  let parameters = NaturalParameter;
}
def Bad : ZKC_MatrixContractionRecipe<OpFieldAdd, OpFieldMul,
    Wrong, "Rows", OpVectorAdd, [0,1], [0], [1]>;
]=] "recipe endpoint parameters unsupported")
recipe_case(matrix-contraction-seed-shape [=[
def Bad : ZKC_MatrixContractionRecipe<OpFieldAdd, OpFieldMul,
    OpMatrixMulVector, "Rows", OpFieldAdd, [0,1], [0], [1]>;
]=] "matrix contraction endpoint input nominal type mismatch")
recipe_case(matrix-contraction-seed-scalar-meaning [=[
def Bad : ZKC_MatrixContractionRecipe<OpFieldAdd, OpFieldMul,
    OpMatrixBilinear, "Bilinear", OpFieldSub, [0,1,2], [], [0,1]>;
]=] "matrix contraction seed combiner meaning mismatch")
recipe_case(matrix-contraction-seed-vector-meaning [=[
def Bad : ZKC_MatrixContractionRecipe<OpFieldAdd, OpFieldMul,
    OpMatrixMulVector, "Rows", OpVectorSub, [0,1], [0], [1]>;
]=] "matrix contraction seed combiner meaning mismatch")
recipe_case(matrix-contraction-static-mapping [=[
def Bad : ZKC_MatrixContractionRecipe<OpFieldAdd, OpFieldMul,
    OpMatrixBilinear, "Bilinear", OpFieldAdd, [0,1,2], [], [0,1]> {
  let staticArguments = [1];
}
]=] "recipe requires the source domain root mapping")
recipe_case(matrix-contraction-duplicate [=[
def A : ZKC_MatrixContractionRecipe<OpFieldAdd, OpFieldMul,
    OpMatrixMulVector, "Rows", OpVectorAdd, [0,1], [0], [1]>;
def B : ZKC_MatrixContractionRecipe<OpFieldAdd, OpFieldMul,
    OpMatrixMulVector, "Rows", OpVectorAdd, [0,1], [0], [1]>;
]=] "duplicate matrix contraction recipe meaning")

declaration_case(mathematical-identity-role [=[
def Laws : ZKC_ScalarLaws<"FieldRing", "FieldBinary"> {
  let leftIdentity = "GroupIdentity";
}
def Meaning : ZKC_MathematicalIdentity<"BadIdentity", 0> { let laws = Laws; }
def Bad : ZKC_Operation<"law.identity", [F],
  [ZKC_Apply<Element,[F]>, ZKC_Apply<Element,[F]>], [ZKC_Apply<Element,[F]>],
  [ZKC_Holds<Field,[F]>]> { let facets = [ZKC_Mathematical<Meaning>]; }
]=] "scalar identity law has incompatible nominal role")
declaration_case(mathematical-action-role [=[
def Laws : ZKC_ScalarLaws<"FieldRing", "FieldBinary"> { let scalarAction = 1; }
def Meaning : ZKC_MathematicalIdentity<"BadAction", 0> { let laws = Laws; }
def Bad : ZKC_Operation<"law.action", [F],
  [ZKC_Apply<Element,[F]>, ZKC_Apply<Element,[F]>], [ZKC_Apply<Element,[F]>],
  [ZKC_Holds<Field,[F]>]> { let facets = [ZKC_Mathematical<Meaning>]; }
]=] "scalar action law requires ordered group and associated scalar ports")

if(failures)
  list(JOIN failures "\n" diagnostic)
  message(FATAL_ERROR "${diagnostic}")
endif()
message(STATUS "Neutral declarations: structural controls and deterministic output passed")
