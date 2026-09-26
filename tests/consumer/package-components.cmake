# Configure independent requests, including the optional claim/IR bridge.
foreach(mode required optional claimtranslation)
  set(source "${TEST_ROOT}/${mode}")
  file(MAKE_DIRECTORY "${source}")
  if(mode STREQUAL "required")
    set(request "COMPONENTS MissingComponent")
    set(check "")
  elseif(mode STREQUAL "optional")
    set(request "COMPONENTS Claims OPTIONAL_COMPONENTS MissingComponent")
    set(check "if(ZkcCompiler_MissingComponent_FOUND)\nmessage(FATAL_ERROR \"unknown component reported found\")\nendif()")
  else()
    set(request "COMPONENTS ClaimTranslation")
    set(check "if(NOT ZkcCompiler_ClaimTranslation_FOUND)\nmessage(FATAL_ERROR \"claim translation component missing\")\nendif()")
  endif()
  file(WRITE "${source}/CMakeLists.txt"
    "cmake_minimum_required(VERSION 3.20)\nproject(ComponentControl LANGUAGES C CXX)\nfind_package(ZkcCompiler REQUIRED CONFIG ${request})\n${check}\n")
  execute_process(COMMAND "${CMAKE_COMMAND}" -S "${source}" -B "${source}/build"
    "-DZkcCompiler_DIR=${PACKAGE_DIR}" "-DMLIR_DIR=${MLIR_DIR}"
    "-DCMAKE_C_COMPILER=${C_COMPILER}" "-DCMAKE_CXX_COMPILER=${CXX_COMPILER}"
    RESULT_VARIABLE result OUTPUT_VARIABLE output ERROR_VARIABLE error)
  if(mode STREQUAL "required")
    if(result EQUAL 0 OR NOT error MATCHES "Unknown ZkcCompiler component: MissingComponent")
      message(FATAL_ERROR "required unknown component did not refuse: ${output} ${error}")
    endif()
  elseif(NOT result EQUAL 0)
    message(FATAL_ERROR "${mode} component request refused: ${output} ${error}")
  endif()
endforeach()
