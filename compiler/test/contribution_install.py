"""Install/relocate a finite contributed API with public and private vendor links.

This builds tiny C++ libraries through the real contribution/link/export helpers;
full MLIR extension behavior belongs to the separate installed-domain consumer.
"""
from pathlib import Path
import os
import subprocess

from tools import ROOT, records


def main():
    work = records()
    compiler = ROOT / "compiler"
    cache = Path(os.environ["ZKC_CTEST_COMPONENTS"]).parent / "CMakeCache.txt"
    settings = dict((line.split("=", 1)[0].split(":", 1)[0], line.split("=", 1)[1]) for line in cache.read_text().splitlines()
                    if ":" in line and "=" in line and not line.startswith(("#", "//")))
    mlir = settings["MLIR_DIR"]
    llvm = settings["LLVM_DIR"]
    cxx = settings["CMAKE_CXX_COMPILER"]
    cc = settings["CMAKE_C_COMPILER"]

    def write(path, text):
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)

    def run(*args, success=True):
        result = subprocess.run(list(map(str, args)), capture_output=True, text=True, check=False, timeout=60)
        with (work / "commands.log").open("a") as log:
            log.write(f"{list(map(str, args))}\n{result.stdout}{result.stderr}\n")
        assert (result.returncode == 0) == success, result.stdout + result.stderr
        return result

    def configure(source, build, *args):
        run("cmake", "-S", source, "-B", build, "-G", "Ninja",
            f"-DCMAKE_CXX_COMPILER={cxx}", f"-DCMAKE_C_COMPILER={cc}", f"-DMLIR_DIR={mlir}", f"-DLLVM_DIR={llvm}", *args)

    vendor, prefix = work / "vendor", work / "prefix"
    write(vendor / "include/vendor/Value.h", "#pragma once\nstruct VendorValue { int value; };\nint vendor_value();\n")
    write(vendor / "Public.cpp", "#include <vendor/Value.h>\nint vendor_value() { return 31; }\n")
    write(vendor / "Private.cpp", "int vendor_private() { return 11; }\n")
    write(vendor / "CMakeLists.txt", '''cmake_minimum_required(VERSION 3.21)
project(Vendor LANGUAGES C CXX)
add_library(Public STATIC Public.cpp)
add_library(Private STATIC Private.cpp)
set_target_properties(Public Private PROPERTIES POSITION_INDEPENDENT_CODE ON)
target_include_directories(Public PUBLIC $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/include> $<INSTALL_INTERFACE:include>)
install(TARGETS Public Private EXPORT VendorTargets ARCHIVE DESTINATION lib)
install(DIRECTORY include/ DESTINATION include)
install(EXPORT VendorTargets NAMESPACE Vendor:: FILE VendorConfig.cmake DESTINATION lib/cmake/Vendor)
''')
    configure(vendor, work / "vendor-build", f"-DCMAKE_INSTALL_PREFIX={prefix}")
    run("cmake", "--build", work / "vendor-build")
    run("cmake", "--install", work / "vendor-build")

    source = work / "contribution"
    write(source / "include/probe/Declarations.td", "// Empty semantic contribution.\n")
    write(source / "include/probe/Native.td", "// No additional dialect.\n")
    write(source / "include/probe/Api.h", "#pragma once\n#include <vendor/Value.h>\nVendorValue contributed_value();\n")
    (source / "include/probe/Alias.hpp").symlink_to("Api.h")
    write(source / "Internal.h", "#pragma once\nint vendor_private();\n")
    write(source / "IR.cpp", "#include <probe/Api.h>\n#include \"Internal.h\"\nVendorValue contributed_value() { return {vendor_value() + vendor_private()}; }\n")
    write(source / "include/probe/Transform.hpp", "#pragma once\n#include <vendor/Value.h>\nVendorValue contributed_transform();\n")
    write(source / "PassInternal.hpp", "#pragma once\nint vendor_private();\n")
    write(source / "Transform.cpp", '#include <probe/Transform.hpp>\n#include "PassInternal.hpp"\nVendorValue contributed_transform() { return {vendor_value() + vendor_private()}; }\n')
    write(source / "Support.cpp", "void contributed_support() {}\n")
    write(source / "CMakeLists.txt", f'''cmake_minimum_required(VERSION 3.21)
project(ContributedPackage LANGUAGES C CXX)
find_package(MLIR REQUIRED CONFIG)
find_package(Vendor REQUIRED CONFIG)
include("{compiler}/cmake/ZkcContributions.cmake")
zkc_add_contribution(NAME probe DECLARATIONS include/probe/Declarations.td BINDINGS include/probe/Native.td
  INCLUDE_DIRECTORIES "${{CMAKE_CURRENT_SOURCE_DIR}}/include"
  PRIVATE_HEADERS Internal.h PassInternal.hpp IR_SOURCES IR.cpp TRANSFORM_SOURCES Transform.cpp
  TRANSFORM_HEADERS include/probe/Transform.hpp PassInternal.hpp
  FIND_DEPENDENCIES Vendor PUBLIC_LINK_LIBRARIES Vendor::Public LINK_LIBRARIES Vendor::Private
  PUBLIC_TRANSFORM_LINK_LIBRARIES Vendor::Public TRANSFORM_LINK_LIBRARIES Vendor::Private)
zkc_assemble_contributions("${{CMAKE_CURRENT_BINARY_DIR}}/include")
add_library(ZkcSupport Support.cpp)
add_library(ZkcIR ${{ZKC_CONTRIBUTION_SOURCES}})
add_library(ZkcTransforms ${{ZKC_CONTRIBUTION_TRANSFORM_SOURCES}})
set_target_properties(ZkcSupport PROPERTIES EXPORT_NAME Support)
set_target_properties(ZkcIR PROPERTIES EXPORT_NAME IR)
set_target_properties(ZkcTransforms PROPERTIES EXPORT_NAME Transforms)
foreach(target ZkcIR ZkcTransforms)
  target_include_directories(${{target}} PUBLIC $<BUILD_INTERFACE:${{CMAKE_CURRENT_SOURCE_DIR}}/include> $<INSTALL_INTERFACE:include>)
endforeach()
zkc_link_contribution_libraries()
target_link_libraries(ZkcIR PUBLIC ZkcSupport)
target_link_libraries(ZkcTransforms PUBLIC ZkcIR)
include("{compiler}/cmake/InstallSDK.cmake")
zkc_install_sdk(COMPONENTS ZkcSupport ZkcIR ZkcTransforms)
foreach(header installed IN ZIP_LISTS ZKC_CONTRIBUTION_PUBLIC_HEADER_FILES ZKC_CONTRIBUTION_PUBLIC_HEADER_PATHS)
  get_filename_component(directory "${{installed}}" DIRECTORY)
  get_filename_component(basename "${{installed}}" NAME)
  install(FILES "${{header}}" DESTINATION "include/${{directory}}" RENAME "${{basename}}")
endforeach()
''')
    consumer = work / "consumer"
    write(consumer / "main.cpp", "#include <probe/Alias.hpp>\n#include <probe/Transform.hpp>\nint main() { return contributed_value().value != 42 || contributed_transform().value != 42; }\n")
    write(consumer / "CMakeLists.txt", '''cmake_minimum_required(VERSION 3.21)
project(Consumer LANGUAGES C CXX)
find_package(ZkcCompiler REQUIRED CONFIG COMPONENTS IR Transforms)
add_executable(consumer main.cpp)
target_link_libraries(consumer PRIVATE Zkc::IR Zkc::Transforms)
''')
    for linkage in ("static", "shared"):
        build, install = work / f"{linkage}-build", work / f"{linkage}-install"
        configure(source, build, f"-DCMAKE_PREFIX_PATH={prefix}",
                  f"-DCMAKE_INSTALL_PREFIX={install}", f"-DBUILD_SHARED_LIBS={'ON' if linkage == 'shared' else 'OFF'}")
        run("cmake", "--build", build)
        run("cmake", "--install", build)
        assert not (install / "include/Internal.h").exists()
        relocated = work / f"{linkage}-relocated"
        install.rename(relocated)
        downstream = work / f"{linkage}-consumer"
        configure(consumer, downstream, f"-DCMAKE_PREFIX_PATH={relocated};{prefix}")
        run("cmake", "--build", downstream)
        run(downstream / "consumer")
        exported = "\n".join((relocated / f"lib/cmake/ZkcCompiler/Zkc{component}Targets.cmake").read_text()
                             for component in ("IR", "Transforms"))
        assert "Vendor::Public" in exported
        if linkage == "static":
            assert "LINK_ONLY:Vendor::Private" in exported
        else:
            assert "Vendor::Private" not in exported
        # Prove that the regression control needs dependency rediscovery, not a
        # leftover imported target in the consumer's configure process.
        config = relocated / "lib/cmake/ZkcCompiler/ZkcCompilerConfig.cmake"
        config.write_text(config.read_text().replace("find_dependency(Vendor)", ""))
        failure = run("cmake", "-S", consumer, "-B", work / f"{linkage}-missing-discovery",
                      f"-DCMAKE_PREFIX_PATH={relocated};{prefix}", f"-DMLIR_DIR={mlir}", f"-DLLVM_DIR={llvm}", success=False)
        assert "Vendor::Public" in failure.stderr or "Vendor::Private" in failure.stderr
    print("Static/shared contributed package relocation, public/private links and missing-discovery controls passed")


if __name__ == "__main__":
    main()
