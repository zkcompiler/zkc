# This test drives the build's own TableGen tool. The caller supplies its
# executable, TableGen include directories, and a dedicated output directory.
foreach(required ZKC_TABLEGEN ZKC_TABLEGEN_INCLUDES ZKC_MAPPING_TEST_DIRECTORY)
  if(NOT DEFINED ${required})
    message(FATAL_ERROR "Missing ${required}")
  endif()
endforeach()
file(MAKE_DIRECTORY "${ZKC_MAPPING_TEST_DIRECTORY}")
set(include_args ${ZKC_TABLEGEN_INCLUDES})
list(TRANSFORM include_args PREPEND -I)
set(preamble [=[
include "mlir/IR/OpBase.td"
include "zkc/Dialect/Base.td"
include "zkc/Contracts/Declarations.td"
def MappingTestDialect : ZKCDialect {
  let name = "mapping_test";
}
class MappingTestOp<string name>
    : Op<MappingTestDialect, name>, ZKC_ContractMapping {
  let arguments = (ins StrAttr:$site, ArrayAttr:$parameters,
    OptionalAttr<FlatSymbolRefAttr>:$binding);
}
// Negative controls mutate real declarations. Positive cases always reference
// installed declarations, never a dummy signature created to pass generation.
class MappingTestVariant<ZKC_Operation original>
    : ZKC_Operation<"mapping.variant", original.scope, original.inputs,
                    original.outputs, original.requirements> {
  let stage = original.stage;
  let parameters = original.parameters;
  let parameterField = original.parameterField;
  let facets = original.facets;
  let commonGeneric = original.commonGeneric;
}
]=])
set(failures "")
set(positive_cases 0)
set(refusal_cases 0)
function(mapping_case name definitions expected_error)
  set(input "${ZKC_MAPPING_TEST_DIRECTORY}/${name}.td")
  set(output "${ZKC_MAPPING_TEST_DIRECTORY}/${name}.inc")
  set(case_preamble "${preamble}")
  if(ARGC GREATER 3)
    set(case_preamble "${ARGV3}")
  endif()
  file(WRITE "${input}" "${case_preamble}\n${definitions}\n")
  # A prior successful output must not conceal a failed generation.
  file(REMOVE "${output}")
  execute_process(COMMAND "${ZKC_TABLEGEN}" -gen-contract-mappings ${include_args} "${input}" -o "${output}"
    RESULT_VARIABLE result OUTPUT_VARIABLE stdout ERROR_VARIABLE stderr)
  file(WRITE "${ZKC_MAPPING_TEST_DIRECTORY}/${name}.log" "${stdout}${stderr}")
  if(expected_error STREQUAL "")
    math(EXPR positive_cases "${positive_cases} + 1")
    if(NOT result STREQUAL "0" OR NOT EXISTS "${output}")
      list(APPEND failures "${name}: expected successful generation: ${stderr}")
    endif()
  else()
    math(EXPR refusal_cases "${refusal_cases} + 1")
    string(FIND "${stderr}" "${expected_error}" position)
    if(NOT result MATCHES "^[1-9][0-9]*$" OR position EQUAL -1 OR EXISTS "${output}")
      list(APPEND failures "${name}: expected refusal '${expected_error}': ${stderr}")
    endif()
  endif()
  set(positive_cases "${positive_cases}" PARENT_SCOPE)
  set(refusal_cases "${refusal_cases}" PARENT_SCOPE)
  set(failures "${failures}" PARENT_SCOPE)
endfunction()

# Compare the complete row multiset, so extra associations and prefix rows fail
# as well as missing associations. Expectations are independent literal pairs.
function(expect_rows name pairs)
  set(expected "")
  foreach(pair IN LISTS pairs)
    string(REGEX MATCH "\\{\"([^\"]+)\", \"([^\"]+)\"\\}" matched "${pair}")
    if(NOT matched)
      message(FATAL_ERROR "Malformed expected mapping: ${pair}")
    endif()
    list(APPEND expected
      "{\"${CMAKE_MATCH_1}\", \"${CMAKE_MATCH_2}\"}"
      "{\"${CMAKE_MATCH_2}\", \"${CMAKE_MATCH_1}\"}")
  endforeach()
  set(generated "")
  if(EXISTS "${ZKC_MAPPING_TEST_DIRECTORY}/${name}.inc")
    file(READ "${ZKC_MAPPING_TEST_DIRECTORY}/${name}.inc" generated)
  endif()
  string(REGEX MATCHALL "\\{\"[^\"]+\", \"[^\"]+\"\\}" actual "${generated}")
  list(SORT actual)
  list(SORT expected)
  if(NOT actual STREQUAL expected)
    list(APPEND failures "${name}: generated mappings differ from the independent exact rows")
  endif()
  set(failures "${failures}" PARENT_SCOPE)
endfunction()

mapping_case(multiple-contracts [=[
def Many : MappingTestOp<"many"> {
  let contracts = [OpFieldAdd, OpFieldMul];
}
]=] "")
string(REPLACE "MappingTestDialect : ZKCDialect" "MappingTestDialect : Dialect" unsafe_preamble "${preamble}")
mapping_case(unsafe-dialect [=[
def A : MappingTestOp<"a"> { let contracts = [OpFieldAdd]; }
]=] "mapped operations require a ZKCDialect" "${unsafe_preamble}")
string(REPLACE "let name = \"mapping_test\";"
  "let name = \"mapping_test\"; let extraClassDeclaration = [{ void registerTypes(); /* StrictProperties */ }];"
  replaced_hook_preamble "${preamble}")
mapping_case(replaced-property-hook [=[
def A : MappingTestOp<"a"> { let contracts = [OpFieldAdd]; }
]=] "mapped dialects must retain strict property registration" "${replaced_hook_preamble}")
string(REPLACE "let name = \"mapping_test\";"
  "let name = \"mapping_test\"; let extraClassDeclaration = ZkcStrictPropertyRegistration # [{ void registerTypes(); }];"
  extended_hook_preamble "${preamble}")
mapping_case(extended-property-hook [=[
def A : MappingTestOp<"a"> { let contracts = [OpFieldAdd]; }
]=] "" "${extended_hook_preamble}")
mapping_case(missing-site [=[
def A : MappingTestOp<"a"> {
  let contracts = [OpFieldAdd];
  let arguments = (ins ArrayAttr:$parameters, OptionalAttr<FlatSymbolRefAttr>:$binding);
}
]=] "invalid or missing mapped operation property: site")
mapping_case(wrong-parameters [=[
def A : MappingTestOp<"a"> {
  let contracts = [OpFieldAdd];
  let arguments = (ins StrAttr:$site, StrAttr:$parameters, OptionalAttr<FlatSymbolRefAttr>:$binding);
}
]=] "invalid or missing mapped operation property: parameters")
mapping_case(wrong-binding [=[
def A : MappingTestOp<"a"> {
  let contracts = [OpFieldAdd];
  let arguments = (ins StrAttr:$site, ArrayAttr:$parameters, FlatSymbolRefAttr:$binding);
}
]=] "invalid or missing mapped operation property: binding")
mapping_case(unsafe-property-parser [=[
def A : MappingTestOp<"a"> {
  let contracts = [OpFieldAdd];
  let assemblyFormat = "prop-dict attr-dict";
}
]=] "mapped operations cannot use prop-dict assembly")
expect_rows(multiple-contracts
  [=[{"field.add", "mapping_test.many"};{"field.mul", "mapping_test.many"}]=])
mapping_case(reordered-contracts [=[
def Many : MappingTestOp<"many"> {
  let contracts = [OpFieldMul, OpFieldAdd];
}
]=] "")

# Logical declarations need not have a distinguished native operation.
mapping_case(unmapped-declarations "" "")
expect_rows(unmapped-declarations "")

mapping_case(duplicate-contract [=[
def A : MappingTestOp<"a"> { let contracts = [OpFieldAdd]; }
def B : MappingTestOp<"b"> { let contracts = [OpFieldAdd]; }
]=] "conflicting contract association")
mapping_case(repeated-contract [=[
def A : MappingTestOp<"a"> { let contracts = [OpFieldAdd, OpFieldAdd]; }
]=] "conflicting contract association")
mapping_case(unknown-property [=[
def A : MappingTestOp<"a"> { let unexpected = [OpIndexedTranscriptObserveData]; }
]=] "Value 'unexpected' unknown")
mapping_case(duplicate-operation [=[
def A : MappingTestOp<"a"> { let contracts = [OpFieldAdd]; }
def B : MappingTestOp<"a"> { let contracts = [OpFieldMul]; }
]=] "duplicate mapped operation name")
mapping_case(unmapped-operation-collision [=[
def A : Op<MappingTestDialect, "a">;
def B : MappingTestOp<"a"> { let contracts = [OpFieldAdd]; }
]=] "duplicate mapped operation name")
mapping_case(missing-contract [=[
def A : MappingTestOp<"a">;
]=] "contract mapping requires a logical declaration")
mapping_case(non-operation [=[
def A : ZKC_ContractMapping { let contracts = [OpFieldAdd]; }
]=] "contract mapping must belong to an Op record")
mapping_case(unknown-declaration [=[
def A : MappingTestOp<"a"> { let contracts = [OpNotDeclared]; }
]=] "Variable not defined: 'OpNotDeclared'")
mapping_case(string-contract [=[
def A : MappingTestOp<"a"> { let contracts = ["field.add"]; }
]=] "Element type mismatch for list")
mapping_case(wrong-record-kind [=[
def A : MappingTestOp<"a"> { let contracts = [TypeField]; }
]=] "Element type mismatch for list")
mapping_case(input-arity [=[
def A : MappingTestOp<"a"> { let contracts = [OpFieldAdd, OpFieldInverse]; }
]=] "incompatible mapped contract signatures")
mapping_case(output-arity [=[
def A : MappingTestOp<"a"> { let contracts = [OpResourceUnitPass, OpResourceUnitConsume]; }
]=] "incompatible mapped contract signatures")
mapping_case(port-types [=[
def A : MappingTestOp<"a"> { let contracts = [OpFieldAdd, OpFieldEqual]; }
]=] "incompatible mapped contract signatures")
mapping_case(scope-sorts [=[
def A : MappingTestOp<"a"> { let contracts = [OpFieldAdd, OpCurveAdd]; }
]=] "incompatible mapped contract signatures")
mapping_case(requirements [=[
def Changed : MappingTestVariant<OpFieldAdd> {
  let requirements = [ZKC_Holds<CapabilityCommRing, [OpFieldAddF]>];
}
def A : MappingTestOp<"a"> { let contracts = [OpFieldAdd, Changed]; }
]=] "incompatible mapped contract signatures")
mapping_case(scope-order [=[
def Changed : MappingTestVariant<OpPcsEqual> {
  let scope = [OpPcsEqualC, OpPcsEqualPointField, OpPcsEqualEvaluationField,
               OpPcsEqualValueField];
}
def A : MappingTestOp<"a"> { let contracts = [OpPcsEqual, Changed]; }
]=] "incompatible mapped contract signatures")
mapping_case(associated-argument [=[
def Changed : MappingTestVariant<OpPcsOpen> {
  let outputs = [ZKC_Apply<TypeField, [OpPcsOpenPointField]>,
                 ZKC_Apply<TypeProof, [OpPcsOpenC]>];
}
def A : MappingTestOp<"a"> { let contracts = [OpPcsOpen, Changed]; }
]=] "incompatible mapped contract signatures")
mapping_case(parameter-validator [=[
def Changed : MappingTestVariant<OpFieldAdd> { let parameters = NaturalParameter; }
def A : MappingTestOp<"a"> { let contracts = [OpFieldAdd, Changed]; }
]=] "incompatible mapped contract signatures")
mapping_case(authoring-stage [=[
def Changed : MappingTestVariant<OpFieldAdd> { let stage = Construction; }
def A : MappingTestOp<"a"> { let contracts = [OpFieldAdd, Changed]; }
]=] "incompatible mapped contract signatures")
mapping_case(indexed-transcript-signatures [=[
def A : MappingTestOp<"a"> {
  let contracts = [OpIndexedTranscriptChallenge, OpIndexedTranscriptObserveData];
}
]=] "incompatible mapped contract signatures")
mapping_case(observation-missing-history [=[
def Changed : MappingTestVariant<OpIndexedTranscriptObserveData> {
  let facets = [ZKC_Observation<0, 1, 0>];
}
def A : MappingTestOp<"a"> { let contracts = [Changed]; }
]=] "transcript facet requires matching history ports")

# Mapping generation must reuse neutral validation, including ownership and
# typed references; a valid-looking contract name alone grants no association.
mapping_case(duplicate-logical-owner [=[
def Changed : MappingTestVariant<OpFieldAdd> { let name = OpFieldAdd.name; }
def A : MappingTestOp<"a"> { let contracts = [Changed]; }
]=] "duplicate operation ownership")
mapping_case(duplicate-type-owner [=[
def Duplicate : ZKC_Type<"field", [FieldDomain]>;
def A : MappingTestOp<"a"> { let contracts = [OpFieldAdd]; }
]=] "duplicate type ownership")
mapping_case(unscoped-reference [=[
def Changed : MappingTestVariant<OpFieldAdd> { let scope = []; }
def A : MappingTestOp<"a"> { let contracts = [Changed]; }
]=] "unscoped typed reference")
mapping_case(invalid-key [=[
def Changed : MappingTestVariant<OpFieldAdd> { let name = "field.*"; }
def A : MappingTestOp<"a"> { let contracts = [Changed]; }
]=] "invalid operation key")
mapping_case(logical-owner-is-native-op [=[
def Changed : MappingTestVariant<OpFieldAdd>, MappingTestOp<"hybrid"> {
  let contracts = [OpFieldAdd];
}
]=] "logical declaration must not be an Op record")
mapping_case(mapped-logical-owner-is-native-op [=[
def Changed : MappingTestVariant<OpFieldAdd>, Op<MappingTestDialect, "hybrid">;
def A : MappingTestOp<"a"> { let contracts = [Changed]; }
]=] "logical declaration must not be an Op record")
mapping_case(unmapped-logical-owner-is-native-op [=[
def Changed : MappingTestVariant<OpFieldAdd>, Op<MappingTestDialect, "hybrid">;
]=] "logical declaration must not be an Op record")

# Reuse the hand-authored oracle, never derive expected pairs from TableGen or
# from the generated lookup functions. Compare both directions exhaustively.
mapping_case(maintained [=[include "zkc/Dialect/IR.td"]=] "" "")
file(READ "${CMAKE_CURRENT_LIST_DIR}/contract_mappings.cpp" oracle_source)
string(REGEX MATCH "constexpr ExpectedMapping expected\\[\\] = \\{([^;]*)\\};"
  oracle "${oracle_source}")
if(NOT oracle)
  message(FATAL_ERROR "Independent mapping oracle not found")
endif()
# clang-format can wrap a literal pair across lines; spelling remains exact.
string(REGEX REPLACE ",[ \t\r\n]+" ", " oracle "${oracle}")
string(REGEX MATCHALL "\\{\"[^\"]+\", \"[^\"]+\"\\}" expected_pairs "${oracle}")
expect_rows(maintained "${expected_pairs}")
mapping_case(maintained-repeat [=[include "zkc/Dialect/IR.td"]=] "" "")
foreach(pair IN ITEMS "multiple-contracts;reordered-contracts" "maintained;maintained-repeat")
  list(GET pair 0 left)
  list(GET pair 1 right)
  execute_process(COMMAND "${CMAKE_COMMAND}" -E compare_files
    "${ZKC_MAPPING_TEST_DIRECTORY}/${left}.inc"
    "${ZKC_MAPPING_TEST_DIRECTORY}/${right}.inc" RESULT_VARIABLE result)
  if(NOT result STREQUAL "0")
    list(APPEND failures "${left}/${right}: nondeterministic generation")
  endif()
endforeach()

if(failures)
  list(JOIN failures "\n" details)
  message(FATAL_ERROR "Contract mapping generation failures:\n${details}")
endif()
message(STATUS "Contract mapping generation: ${positive_cases} positive and ${refusal_cases} refusal cases passed")
