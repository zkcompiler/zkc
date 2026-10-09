"""Real CMake export/discovery controls using small independently linked clients."""

import os
import shutil
import subprocess
from pathlib import Path

import pytest

from workspace import ROOT


def write(path, text):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text)


def write_version(path, version):
    write(path, f'''
set(PACKAGE_VERSION "{version}")
if(PACKAGE_FIND_VERSION VERSION_EQUAL PACKAGE_VERSION)
  set(PACKAGE_VERSION_COMPATIBLE TRUE)
  set(PACKAGE_VERSION_EXACT TRUE)
endif()
''')


def run(work, *arguments, success=True, env=None):
    result = subprocess.run(list(map(str, arguments)), capture_output=True, text=True, timeout=60, env=env)
    with (work / "commands.log").open("a") as log:
        log.write(f"{list(map(str, arguments))}\n{result.stdout}{result.stderr}\n")
    assert (result.returncode == 0) == success, result.stdout + result.stderr
    return result.stdout + result.stderr


@pytest.fixture(scope="module", params=["static", "shared"])
def sdk(request, tmp_path_factory):
    if not shutil.which("cmake") or not shutil.which("c++"):
        pytest.skip("CMake and a C++ compiler are required")
    work = tmp_path_factory.mktemp(f"sdk-{request.param}")
    dependencies = work / "dependencies"
    for name in ("llvm", "mlir"):
        write(dependencies / f"include/{name}/Marker.h", "#pragma once\n")
    write(dependencies / "lib/cmake/LLVM/LLVMConfig.cmake", f'''
set(LLVM_PACKAGE_VERSION 23.1.2)
set(LLVM_INCLUDE_DIRS "{dependencies}/include")
set(LLVM_CMAKE_DIR "{dependencies}/lib/cmake/LLVM")
set(LLVM_DEFINITIONS "-DFIXTURE_LLVM=1")
if(NOT TARGET LLVM)
  add_library(LLVM INTERFACE IMPORTED)
endif()
''')
    write(dependencies / "lib/cmake/MLIR/MLIRConfig.cmake", f'''
set(LLVM_VERSION 23.1.2)
find_package(LLVM ${{LLVM_VERSION}} EXACT REQUIRED CONFIG
  HINTS "${{CMAKE_CURRENT_LIST_DIR}}/../LLVM")
set(MLIR_INCLUDE_DIRS "{dependencies}/include")
set(MLIR_CMAKE_DIR "{dependencies}/lib/cmake/MLIR")
set(MLIR_TABLEGEN_EXE "mlir-tblgen")
set(MLIR_PDLL_TABLEGEN_EXE "mlir-pdll")
if(NOT TARGET MLIR)
  add_library(MLIR INTERFACE IMPORTED)
endif()
''')
    for name in ("LLVM", "MLIR"):
        write_version(dependencies / f"lib/cmake/{name}/{name}ConfigVersion.cmake", "23.1.2")
    source = work / "source"
    parts = {
        "Support": ([], "1"),
        "Contracts": (["Support"], "support() + 1"),
        "Program": (["Contracts"], "contracts() + 1"),
        "Relation": (["Contracts"], "contracts() + 1"),
        "Language": (["Contracts", "Relation"], "contracts() + relation() + program()"),
        "IR": (["Program", "Relation"], "program() + relation() + vendor_public()"),
        "Translation": (["IR", "Language"], "ir() + language()"),
        "Transforms": (["IR"], "ir() + vendor_private()"),
        "Compiler": (["Translation", "Transforms"], "translation() + transforms()"),
        "Driver": (["Compiler"], "compiler() + 1"),
    }
    cmake = [f'''cmake_minimum_required(VERSION 3.21)
project(SDKFixture VERSION 0.0.0 LANGUAGES CXX)
find_package(MLIR REQUIRED CONFIG)
include("{ROOT}/compiler/cmake/InstallSDK.cmake")
add_library(VendorPublic STATIC VendorPublic.cpp)
add_library(VendorPrivate STATIC VendorPrivate.cpp)
set_target_properties(VendorPublic VendorPrivate PROPERTIES POSITION_INDEPENDENT_CODE ON)
set_target_properties(VendorPublic PROPERTIES EXPORT_NAME Public)
set_target_properties(VendorPrivate PROPERTIES EXPORT_NAME Private)
install(TARGETS VendorPublic VendorPrivate EXPORT VendorTargets ARCHIVE DESTINATION lib)
install(EXPORT VendorTargets NAMESPACE Vendor:: FILE VendorConfig.cmake DESTINATION lib/cmake/Vendor)
set(ZKC_CONTRIBUTION_FIND_DEPENDENCIES "find_dependency(Vendor)\\n")
''']
    write(source / "VendorPublic.cpp", "int vendor_public() { return 40; }\n")
    write(source / "VendorPrivate.cpp", "int vendor_private() { return 2; }\n")
    for name, (links, expression) in parts.items():
        write(source / f"include/zkc/{name}/Api.h", f"#pragma once\nint {name.lower()}();\n")
        includes = "".join(f"#include <zkc/{link}/Api.h>\n" for link in links)
        external = "#include <mlir/Marker.h>\nint vendor_public();\n" if name == "IR" else ""
        if name == "Transforms":
            external = "int vendor_private();\n"
        if name == "Language":
            external = "#include <zkc/Program/Api.h>\n"
        write(source / f"{name}.cpp", includes + external + f"int {name.lower()}() {{ return {expression}; }}\n")
        cmake.append(f'''
add_library(Zkc{name} {name}.cpp)
set_target_properties(Zkc{name} PROPERTIES EXPORT_NAME {name} INSTALL_RPATH "$ORIGIN")
target_include_directories(Zkc{name} PUBLIC $<BUILD_INTERFACE:${{CMAKE_CURRENT_SOURCE_DIR}}/include> $<INSTALL_INTERFACE:include>)
''')
        if links:
            cmake.append(f"target_link_libraries(Zkc{name} PUBLIC {' '.join('Zkc' + link for link in links)})\n")
    cmake.append('''
target_link_libraries(ZkcSupport PUBLIC LLVM)
target_link_libraries(ZkcIR PUBLIC MLIR VendorPublic)
target_include_directories(ZkcIR PRIVATE ${MLIR_INCLUDE_DIRS})
target_link_libraries(ZkcTransforms PRIVATE VendorPrivate)
add_library(ZkcFixture::Program ALIAS ZkcProgram)
target_link_libraries(ZkcLanguage PRIVATE ZkcFixture::Program)
''')
    for tool in ("zkc-compile", "zkc-opt", "zkc-tblgen"):
        write(source / f"{tool}.cpp", "int main() { return 0; }\n")
        cmake.append(f"add_executable({tool} {tool}.cpp)\n")
    cmake.append('''
zkc_install_sdk(COMPONENTS ZkcSupport ZkcContracts ZkcLanguage ZkcRelation ZkcProgram
  ZkcIR ZkcTranslation ZkcTransforms ZkcCompiler ZkcDriver
  TOOLS zkc-compile zkc-opt zkc-tblgen)
install(DIRECTORY include/ DESTINATION include)
''')
    write(source / "CMakeLists.txt", "".join(cmake))
    prefix = work / "original"
    run(work, "cmake", "-S", source, "-B", work / "build",
        f"-DCMAKE_PREFIX_PATH={dependencies}", f"-DCMAKE_INSTALL_PREFIX={prefix}",
        f"-DBUILD_SHARED_LIBS={'ON' if request.param == 'shared' else 'OFF'}")
    run(work, "cmake", "--build", work / "build", "--parallel", "4")
    run(work, "cmake", "--install", work / "build")
    relocated = work / "relocated"
    prefix.rename(relocated)
    # The downstream consumer must use the installation, never the fixture tree.
    shutil.rmtree(source)
    shutil.rmtree(work / "build")
    return work, relocated, dependencies


def configure(sdk, tmp_path, body, *, options=(), success=True, main=None):
    work, prefix, dependencies = sdk
    write(tmp_path / "CMakeLists.txt", "cmake_minimum_required(VERSION 3.21)\n"
          "project(SDKClient LANGUAGES CXX)\n" + body)
    if main:
        write(tmp_path / "main.cpp", main)
    output = run(work, "cmake", "-S", tmp_path, "-B", tmp_path / "build",
                 f"-DCMAKE_PREFIX_PATH={prefix};{dependencies}", *options, success=success)
    if main and success:
        run(work, "cmake", "--build", tmp_path / "build", "--parallel", "4")
        run(work, tmp_path / "build/client")
    return output


@pytest.mark.parametrize("component,result", [("Support", 1), ("Contracts", 2),
                                               ("Program", 3), ("Relation", 3), ("Language", 8)])
def test_llvm_only_discovery_and_link(sdk, tmp_path, component, result):
    configure(sdk, tmp_path, f'''
find_package(ZkcCompiler REQUIRED CONFIG COMPONENTS {component})
if(NOT ZkcCompiler_{component}_FOUND OR TARGET Zkc::IR OR TARGET MLIR OR TARGET Vendor::Public OR TARGET Zkc::zkc-opt)
  message(FATAL_ERROR "LLVM-only discovery crossed a component boundary")
endif()
add_executable(client main.cpp)
target_link_libraries(client PRIVATE Zkc::{component})
''', options=["-DCMAKE_DISABLE_FIND_PACKAGE_MLIR=TRUE", "-DCMAKE_DISABLE_FIND_PACKAGE_Vendor=TRUE"],
              main=f"#include <llvm/Marker.h>\n#include <zkc/{component}/Api.h>\n"
                   f"int main() {{ return {component.lower()}() != {result}; }}\n")


def test_repeat_expand_and_default(sdk, tmp_path):
    configure(sdk, tmp_path, '''
set(CMAKE_DISABLE_FIND_PACKAGE_MLIR TRUE)
find_package(ZkcCompiler REQUIRED CONFIG COMPONENTS Program)
get_target_property(before Zkc::Support INTERFACE_INCLUDE_DIRECTORIES)
find_package(ZkcCompiler REQUIRED CONFIG COMPONENTS Program)
get_target_property(after Zkc::Support INTERFACE_INCLUDE_DIRECTORIES)
if(NOT before STREQUAL after OR TARGET Zkc::IR)
  message(FATAL_ERROR "repeated discovery changed the imported target")
endif()
set(CMAKE_DISABLE_FIND_PACKAGE_MLIR FALSE)
find_package(ZkcCompiler REQUIRED CONFIG COMPONENTS IR)
if(TARGET Zkc::Transforms OR TARGET Zkc::Compiler)
  message(FATAL_ERROR "IR discovery imported upward components")
endif()
find_package(ZkcCompiler REQUIRED CONFIG COMPONENTS Compiler)
if(TARGET Zkc::Driver OR TARGET Zkc::zkc-opt)
  message(FATAL_ERROR "Compiler imported CLI targets")
endif()
find_package(ZkcCompiler REQUIRED CONFIG)
if(NOT ZkcCompiler_Tools_FOUND OR NOT TARGET Zkc::zkc-tblgen)
  message(FATAL_ERROR "default discovery omitted tools")
endif()
add_executable(client main.cpp)
target_link_libraries(client PRIVATE Zkc::Driver)
''', main="#include <zkc/Driver/Api.h>\n#include <mlir/Marker.h>\nint main() { return driver() != 103; }\n")


def test_private_component_export_closure(sdk, tmp_path):
    _, prefix, _ = sdk
    exported = (prefix / "lib/cmake/ZkcCompiler/ZkcLanguageTargets.cmake").read_text()
    static = "$<LINK_ONLY:Zkc::Program>" in exported
    assert static == ("STATIC IMPORTED" in exported)
    configure(sdk, tmp_path, f'''
find_package(ZkcCompiler REQUIRED CONFIG COMPONENTS Language)
if({'NOT ' if static else ''}TARGET Zkc::Program)
  message(FATAL_ERROR "private dependency closure does not match the exported link interface")
endif()
add_executable(client main.cpp)
target_link_libraries(client PRIVATE Zkc::Language)
''', options=["-DCMAKE_DISABLE_FIND_PACKAGE_MLIR=TRUE"],
              main="#include <zkc/Language/Api.h>\nint main() { return language() != 8; }\n")


def test_unsupported_component_link_expression_is_rejected(tmp_path):
    write(tmp_path / "CMakeLists.txt", f'''
cmake_minimum_required(VERSION 3.21)
project(UnsupportedSDKLink LANGUAGES NONE)
include("{ROOT}/compiler/cmake/InstallSDK.cmake")
add_library(ZkcProgram INTERFACE)
add_library(ZkcSupport INTERFACE)
set_target_properties(ZkcProgram PROPERTIES EXPORT_NAME Program)
set_target_properties(ZkcSupport PROPERTIES EXPORT_NAME Support)
target_link_libraries(ZkcProgram INTERFACE "$<$<BOOL:1>:ZkcSupport>")
zkc_install_sdk(COMPONENTS ZkcProgram ZkcSupport)
''')
    output = run(tmp_path, "cmake", "-S", tmp_path, "-B", tmp_path / "build", success=False)
    assert "Unsupported SDK component link expression" in output


@pytest.mark.parametrize("missing", ["MLIR", "Vendor"])
def test_optional_native_dependency_absence(sdk, tmp_path, missing):
    configure(sdk, tmp_path, f'''
find_package(ZkcCompiler REQUIRED CONFIG COMPONENTS Program OPTIONAL_COMPONENTS IR Compiler Unknown)
if(NOT ZkcCompiler_FOUND OR NOT ZkcCompiler_Program_FOUND OR ZkcCompiler_IR_FOUND
    OR ZkcCompiler_Compiler_FOUND OR ZkcCompiler_Unknown_FOUND OR TARGET Zkc::IR)
  message(FATAL_ERROR "optional absence changed required component availability")
endif()
set(CMAKE_DISABLE_FIND_PACKAGE_{missing} FALSE)
find_package(ZkcCompiler REQUIRED CONFIG COMPONENTS IR)
if(NOT ZkcCompiler_IR_FOUND OR NOT TARGET Zkc::IR OR ZkcCompiler_NOT_FOUND_MESSAGE)
  message(FATAL_ERROR "native discovery could not recover after dependency absence")
endif()
''', options=[f"-DCMAKE_DISABLE_FIND_PACKAGE_{missing}=TRUE"])


@pytest.mark.parametrize("components,message,options", [
    ("COMPONENTS Unknown", "Unknown ZkcCompiler component: Unknown", ["-DCMAKE_DISABLE_FIND_PACKAGE_LLVM=TRUE"]),
    ("COMPONENTS program", "Unknown ZkcCompiler component: program", []),
    ("COMPONENTS IR", "Dependencies unavailable for ZkcCompiler component: IR", ["-DCMAKE_DISABLE_FIND_PACKAGE_MLIR=TRUE"]),
    ("COMPONENTS Program", "Dependencies unavailable for ZkcCompiler component: Program", ["-DCMAKE_DISABLE_FIND_PACKAGE_LLVM=TRUE"]),
    ("COMPONENTS IR", "Dependencies unavailable for ZkcCompiler component: IR", ["-DCMAKE_DISABLE_FIND_PACKAGE_Vendor=TRUE"]),
])
def test_required_refusals(sdk, tmp_path, components, message, options):
    output = configure(sdk, tmp_path, f"find_package(ZkcCompiler REQUIRED CONFIG {components})\n",
                       options=options, success=False)
    assert message in output


def test_unknown_cannot_be_supplied_by_callers_and_retry(sdk, tmp_path):
    configure(sdk, tmp_path, '''
add_library(Zkc::Unknown INTERFACE IMPORTED)
find_package(ZkcCompiler QUIET CONFIG COMPONENTS Unknown)
if(ZkcCompiler_FOUND OR ZkcCompiler_Unknown_FOUND)
  message(FATAL_ERROR "caller target forged a component")
endif()
find_package(ZkcCompiler REQUIRED CONFIG COMPONENTS Program OPTIONAL_COMPONENTS Unknown)
if(NOT ZkcCompiler_FOUND OR ZkcCompiler_Unknown_FOUND OR ZkcCompiler_NOT_FOUND_MESSAGE)
  message(FATAL_ERROR "stale package refusal after valid discovery")
endif()
''')


def copy_dependency(sdk, tmp_path, name, version):
    _, _, dependencies = sdk
    wrong = tmp_path / name
    for suffix in ("Config.cmake", "ConfigVersion.cmake"):
        write(wrong / f"{name}{suffix}", (dependencies / f"lib/cmake/{name}/{name}{suffix}").read_text()
              .replace("23.1.2", version))
    return wrong


def test_exact_llvm_abi_is_required_without_mlir(sdk, tmp_path):
    wrong = copy_dependency(sdk, tmp_path, "LLVM", "23.1.3")
    output = configure(sdk, tmp_path, "find_package(ZkcCompiler REQUIRED CONFIG COMPONENTS Program)\n",
                       options=[f"-DLLVM_DIR={wrong}", "-DCMAKE_DISABLE_FIND_PACKAGE_MLIR=TRUE"], success=False)
    assert "Dependencies unavailable for ZkcCompiler component: Program" in output


def test_native_build_variables_survive_discovery(sdk, tmp_path):
    configure(sdk, tmp_path, '''
foreach(component IR Compiler IR)
  find_package(ZkcCompiler REQUIRED CONFIG COMPONENTS ${component})
  foreach(variable MLIR_CMAKE_DIR MLIR_TABLEGEN_EXE MLIR_PDLL_TABLEGEN_EXE
      MLIR_INCLUDE_DIRS LLVM_CMAKE_DIR LLVM_INCLUDE_DIRS LLVM_DEFINITIONS LLVM_VERSION)
    if(NOT DEFINED ${variable} OR "${${variable}}" STREQUAL "")
      message(FATAL_ERROR "upstream build variable was hidden: ${variable}")
    endif()
  endforeach()
  if(NOT EXISTS "${MLIR_CMAKE_DIR}/MLIRConfig.cmake" OR
      NOT MLIR_TABLEGEN_EXE STREQUAL "mlir-tblgen" OR NOT LLVM_VERSION STREQUAL "23.1.2")
    message(FATAL_ERROR "upstream build variables changed")
  endif()
endforeach()
''')


@pytest.mark.parametrize("mode", ["compiler", "repeated"])
def test_installed_upstream_native_build_variables(sdk, tmp_path, mode):
    llvm_config = shutil.which("llvm-config")
    if not llvm_config:
        pytest.skip("installed upstream llvm-config is required")
    work, prefix, _ = sdk
    if run(work, llvm_config, "--version").strip() != "23.1.2":
        pytest.skip("installed LLVM must match the fixture ABI")
    llvm = Path(run(work, llvm_config, "--cmakedir").strip())
    mlir = llvm.parent / "mlir"
    if not (mlir / "MLIRConfig.cmake").is_file():
        pytest.skip("installed upstream MLIR is required")
    # The script starts a fresh C/C++ configure and includes real upstream
    # TableGen/AddMLIR modules using variables exposed solely by SDK discovery.
    run(work, "cmake", f"-DPACKAGE_DIR={prefix}/lib/cmake/ZkcCompiler",
        f"-DLLVM_DIR={llvm}", f"-DMLIR_DIR={mlir}", f"-DTEST_ROOT={tmp_path}",
        f"-DMODE={mode}",
        f"-DC_COMPILER={shutil.which('cc')}", f"-DCXX_COMPILER={shutil.which('c++')}",
        "-P", ROOT / "tests/consumer/package-components.cmake",
        env=os.environ | {"CMAKE_PREFIX_PATH": str(prefix)})


def test_native_discovery_uses_mlir_llvm_hint(sdk, tmp_path):
    _, prefix, dependencies = sdk
    configure(sdk, tmp_path, f'''
set(CMAKE_PREFIX_PATH "{prefix}")
find_package(ZkcCompiler REQUIRED CONFIG COMPONENTS IR)
get_filename_component(selected_llvm "${{LLVM_DIR}}" REALPATH)
if(NOT selected_llvm STREQUAL "{dependencies}/lib/cmake/LLVM")
  message(FATAL_ERROR "native LLVM preflight ignored MLIR's installation")
endif()
''', options=[f"-DMLIR_DIR={dependencies}/lib/cmake/MLIR"])


@pytest.mark.parametrize("component", ["Program", "IR"])
@pytest.mark.parametrize("missing", [False, True])
def test_optional_package_llvm_unavailable(sdk, tmp_path, component, missing):
    wrong = copy_dependency(sdk, tmp_path, "LLVM", "23.1.3")
    options = ["-DCMAKE_DISABLE_FIND_PACKAGE_LLVM=TRUE"] if missing else [f"-DLLVM_DIR={wrong}"]
    configure(sdk, tmp_path, f'''
foreach(attempt RANGE 1 2)
  find_package(ZkcCompiler QUIET CONFIG COMPONENTS {component})
  if(ZkcCompiler_FOUND OR ZkcCompiler_{component}_FOUND OR TARGET Zkc::Support OR TARGET MLIR)
    message(FATAL_ERROR "unavailable LLVM was accepted or replaced")
  endif()
endforeach()
''', options=options)
    work, _, _ = sdk
    run(work, "cmake", "-S", tmp_path, "-B", tmp_path / "build")


@pytest.mark.parametrize("required", [False, True])
def test_wrong_mlir_does_not_replace_independent_llvm(sdk, tmp_path, required):
    wrong = copy_dependency(sdk, tmp_path, "MLIR", "23.1.3")
    # The bad MLIR's config must never run: upstream would require the wrong LLVM.
    output = configure(sdk, tmp_path, f'''
find_package(ZkcCompiler REQUIRED CONFIG COMPONENTS Program)
get_target_property(before Zkc::Support INTERFACE_INCLUDE_DIRECTORIES)
find_package(ZkcCompiler {'REQUIRED' if required else 'QUIET'} CONFIG COMPONENTS IR)
if(ZkcCompiler_FOUND OR ZkcCompiler_IR_FOUND OR TARGET Zkc::IR OR TARGET MLIR)
  message(FATAL_ERROR "wrong MLIR ABI was accepted or replaced")
endif()
find_package(ZkcCompiler REQUIRED CONFIG COMPONENTS Program OPTIONAL_COMPONENTS IR)
get_target_property(after Zkc::Support INTERFACE_INCLUDE_DIRECTORIES)
if(NOT ZkcCompiler_FOUND OR NOT ZkcCompiler_Program_FOUND OR ZkcCompiler_IR_FOUND
    OR TARGET MLIR OR NOT before STREQUAL after OR NOT LLVM_PACKAGE_VERSION STREQUAL "23.1.2")
  message(FATAL_ERROR "optional native failure poisoned independent LLVM")
endif()
''', options=[f"-DMLIR_DIR={wrong}"], success=not required)
    if required:
        assert "Dependencies unavailable for ZkcCompiler component: IR" in output
    else:
        work, _, _ = sdk
        run(work, "cmake", "-S", tmp_path, "-B", tmp_path / "build")


def test_preloaded_wrong_llvm_is_not_replaced(sdk, tmp_path):
    wrong = copy_dependency(sdk, tmp_path, "LLVM", "23.1.3")
    _, _, dependencies = sdk
    configure(sdk, tmp_path, f'''
find_package(LLVM REQUIRED CONFIG)
set(LLVM_DIR "{dependencies}/lib/cmake/LLVM")
find_package(ZkcCompiler QUIET CONFIG COMPONENTS Program IR)
if(ZkcCompiler_FOUND OR ZkcCompiler_Program_FOUND OR ZkcCompiler_IR_FOUND OR TARGET Zkc::Support)
  message(FATAL_ERROR "loaded incompatible LLVM was replaced")
endif()
if(NOT ZkcCompiler_NOT_FOUND_MESSAGE MATCHES "found 23.1.3")
  message(FATAL_ERROR "incompatible loaded LLVM diagnostic missing")
endif()
''', options=[f"-DLLVM_DIR={wrong}"])


def test_native_config_cannot_change_llvm_abi(sdk, tmp_path):
    wrong = copy_dependency(sdk, tmp_path, "MLIR", "23.1.2")
    with (wrong / "MLIRConfig.cmake").open("a") as config:
        config.write("set(LLVM_PACKAGE_VERSION 23.1.3)\n")
    configure(sdk, tmp_path, '''
find_package(ZkcCompiler QUIET CONFIG COMPONENTS Program IR)
if(ZkcCompiler_FOUND OR ZkcCompiler_Program_FOUND OR ZkcCompiler_IR_FOUND OR TARGET Zkc::Support)
  message(FATAL_ERROR "native discovery accepted a mixed LLVM ABI")
endif()
''', options=[f"-DMLIR_DIR={wrong}"])


def test_sibling_directory_discovery(sdk, tmp_path):
    for name in ("first", "second"):
        write(tmp_path / name / "CMakeLists.txt", '''
find_package(ZkcCompiler REQUIRED CONFIG COMPONENTS Program)
if(NOT TARGET Zkc::Program OR NOT TARGET Zkc::Contracts)
  message(FATAL_ERROR "component targets lost in sibling scope")
endif()
''')
    configure(sdk, tmp_path, "add_subdirectory(first)\nadd_subdirectory(second)\n",
              options=["-DCMAKE_DISABLE_FIND_PACKAGE_MLIR=TRUE"])


def test_component_requests_cannot_mix_installations(sdk, tmp_path):
    _, prefix, _ = sdk
    second = tmp_path / "second-install"
    shutil.copytree(prefix, second)
    output = configure(sdk, tmp_path, f'''
find_package(ZkcCompiler REQUIRED CONFIG COMPONENTS Program)
set(ZkcCompiler_DIR "{second}/lib/cmake/ZkcCompiler")
find_package(ZkcCompiler REQUIRED CONFIG COMPONENTS Language)
''', success=False)
    assert "belongs to a different installation" in output


def test_caller_target_cannot_replace_known_component(sdk, tmp_path):
    output = configure(sdk, tmp_path, '''
add_library(Zkc::Program INTERFACE IMPORTED)
find_package(ZkcCompiler REQUIRED CONFIG COMPONENTS Program)
''', success=False)
    assert "belongs to a different installation" in output
