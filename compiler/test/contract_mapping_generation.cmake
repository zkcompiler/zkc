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
def MappingTestDialect : Dialect {
  let name = "mapping_test";
}
class MappingTestOp<string name>
    : Op<MappingTestDialect, name>, ZKC_ContractMapping;
]=])
set(failures "")
function(mapping_case name definitions expected_error)
  set(input "${ZKC_MAPPING_TEST_DIRECTORY}/${name}.td")
  set(output "${ZKC_MAPPING_TEST_DIRECTORY}/${name}.inc")
  file(WRITE "${input}" "${preamble}\n${definitions}\n")
  # A prior successful output must not conceal a failed generation.
  file(REMOVE "${output}")
  execute_process(COMMAND "${ZKC_TABLEGEN}" ${include_args} "${input}" -o "${output}"
    RESULT_VARIABLE result OUTPUT_VARIABLE stdout ERROR_VARIABLE stderr)
  file(WRITE "${ZKC_MAPPING_TEST_DIRECTORY}/${name}.log" "${stdout}${stderr}")
  if(expected_error STREQUAL "")
    if(NOT result EQUAL 0)
      list(APPEND failures "${name}: expected successful generation: ${stderr}")
    endif()
  else()
    string(FIND "${stderr}" "${expected_error}" position)
    if(result EQUAL 0 OR position EQUAL -1 OR EXISTS "${output}")
      list(APPEND failures "${name}: expected refusal '${expected_error}': ${stderr}")
    endif()
  endif()
  set(failures "${failures}" PARENT_SCOPE)
endfunction()

mapping_case(multiple-keys [=[
def Many : MappingTestOp<"many"> {
  let contractKeys = ["field.add", "field.mul"];
  let contractFamilies = ["transcript.observe."];
}
]=] "")
set(generated "")
if(EXISTS "${ZKC_MAPPING_TEST_DIRECTORY}/multiple-keys.inc")
  file(READ "${ZKC_MAPPING_TEST_DIRECTORY}/multiple-keys.inc" generated)
endif()
foreach(row IN ITEMS
    [=[{"field.add", "mapping_test.many", false}]=]
    [=[{"field.mul", "mapping_test.many", false}]=]
    [=[{"transcript.observe.", "mapping_test.many", true}]=]
    [=[{"mapping_test.many", "field.add", false}]=]
    [=[{"mapping_test.many", "field.mul", false}]=]
    [=[{"mapping_test.many", "transcript.observe.", true}]=])
  string(FIND "${generated}" "${row}" position)
  if(position EQUAL -1)
    list(APPEND failures "missing generated association: ${row}")
  endif()
endforeach()

mapping_case(duplicate-key [=[
def A : MappingTestOp<"a"> { let contractKeys = ["field.add"]; }
def B : MappingTestOp<"b"> { let contractKeys = ["field.add"]; }
]=] "conflicting contract association")
mapping_case(repeated-key [=[
def A : MappingTestOp<"a"> { let contractKeys = ["field.add", "field.add"]; }
]=] "conflicting contract association")
mapping_case(duplicate-family [=[
def A : MappingTestOp<"a"> { let contractFamilies = ["transcript.observe."]; }
def B : MappingTestOp<"b"> { let contractFamilies = ["transcript.observe."]; }
]=] "conflicting contract association")
mapping_case(nested-family [=[
def A : MappingTestOp<"a"> { let contractFamilies = ["transcript."]; }
def B : MappingTestOp<"b"> { let contractFamilies = ["transcript.observe."]; }
]=] "conflicting contract association")
mapping_case(exact-in-family [=[
def A : MappingTestOp<"a"> { let contractFamilies = ["transcript.observe."]; }
def B : MappingTestOp<"b"> { let contractKeys = ["transcript.observe.field"]; }
]=] "conflicting contract association")
mapping_case(same-operation-overlap [=[
def A : MappingTestOp<"a"> {
  let contractKeys = ["transcript.observe.field"];
  let contractFamilies = ["transcript.observe."];
}
]=] "conflicting contract association")
mapping_case(duplicate-operation [=[
def A : MappingTestOp<"a"> { let contractKeys = ["field.add"]; }
def B : MappingTestOp<"a"> { let contractKeys = ["field.mul"]; }
]=] "duplicate mapped operation name")
mapping_case(missing-key [=[
def A : MappingTestOp<"a">;
]=] "contract mapping requires a key or family")
mapping_case(non-operation [=[
def A : ZKC_ContractMapping { let contractKeys = ["field.add"]; }
]=] "contract mapping must belong to an Op record")
mapping_case(undelimited-family [=[
def A : MappingTestOp<"a"> { let contractFamilies = ["transcript.observe"]; }
]=] "invalid contract key or family")
mapping_case(wildcard-key [=[
def A : MappingTestOp<"a"> { let contractKeys = ["field.*"]; }
]=] "invalid contract key or family")
mapping_case(empty-key [=[
def A : MappingTestOp<"a"> { let contractKeys = [""]; }
]=] "invalid contract key or family")
mapping_case(empty-segment [=[
def A : MappingTestOp<"a"> { let contractFamilies = ["transcript..observe."]; }
]=] "invalid contract key or family")

if(failures)
  list(JOIN failures "\n" details)
  message(FATAL_ERROR "Contract mapping generation failures:\n${details}")
endif()
message(STATUS "Contract mapping generation: one positive and 13 refusal cases passed")
