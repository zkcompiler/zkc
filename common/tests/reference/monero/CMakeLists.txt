cmake_minimum_required(VERSION 3.20)
project(zkc_monero_reference LANGUAGES C CXX)
set(MONERO_SOURCE "" CACHE PATH "Unmodified pinned Monero checkout")
find_package(Boost REQUIRED)
find_package(PkgConfig REQUIRED)
pkg_check_modules(SODIUM REQUIRED IMPORTED_TARGET libsodium)
find_path(RAPIDJSON_INCLUDE_DIR rapidjson/document.h REQUIRED)
set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(MONERO_FILES
  src/ringct/bulletproofs_plus.cc src/ringct/multiexp.cc
  src/ringct/rctOps.cpp src/ringct/rctTypes.cpp src/ringct/rctCryptoOps.c
  src/crypto/crypto-ops.c src/crypto/crypto-ops-data.c src/crypto/hash.c
  src/crypto/keccak.c src/crypto/random.c src/crypto/crypto.cpp
  src/common/perf_timer.cpp src/common/aligned.c
  contrib/epee/src/memwipe.c contrib/epee/src/mlocker.cpp
  external/easylogging++/easylogging++.cc)
list(TRANSFORM MONERO_FILES PREPEND "${MONERO_SOURCE}/")
add_library(monero-primitives STATIC ${MONERO_FILES})
target_include_directories(monero-primitives PUBLIC
  "${MONERO_SOURCE}/src" "${MONERO_SOURCE}/src/ringct"
  "${MONERO_SOURCE}/contrib/epee/include" "${MONERO_SOURCE}/external/easylogging++"
  ${Boost_INCLUDE_DIRS} ${RAPIDJSON_INCLUDE_DIR})
target_compile_definitions(monero-primitives PUBLIC
  AUTO_INITIALIZE_EASYLOGGINGPP ELPP_DISABLE_LOGS PERF_TIMER_DISABLED)
target_compile_options(monero-primitives PRIVATE -ffunction-sections -fdata-sections)
target_link_libraries(monero-primitives PUBLIC PkgConfig::SODIUM pthread)
add_executable(monero-reference reference.cpp)
target_link_libraries(monero-reference PRIVATE monero-primitives)
target_link_options(monero-reference PRIVATE -Wl,--gc-sections -Wl,--wrap=_ZN3rct5skGenEv)

# The benchmark retains upstream randomness and has no replay linker wrapper.
add_executable(monero-benchmark ../../../benchmarks/monero.cpp)
target_link_libraries(monero-benchmark PRIVATE monero-primitives)
target_link_options(monero-benchmark PRIVATE -Wl,--gc-sections)
