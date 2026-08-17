//===- ZkcTest.h - A unit-test harness with no dependency -------*- C++ -*-===//
// The pure cores are tested wherever this repository builds, which
// means the harness cannot be a dependency the build might not have.
// A packaged LLVM ships no gtest, and a gate that runs only where
// someone happens to have built LLVM from source is not a gate.
//
// So: registration, the comparisons the tests use, and a runner. The
// macros carry gtest's names because they are the names a reader of a
// C++ test expects, and the semantics are the ones those names mean —
// `EXPECT` records and continues, `ASSERT` records and returns.
//===----------------------------------------------------------------------===//

#ifndef ZKC_UNITTESTS_ZKCTEST_H
#define ZKC_UNITTESTS_ZKCTEST_H

#include "llvm/Support/raw_ostream.h"

#include <string>

namespace zkctest {

/// One recorded failure. It prints and counts when the full expression
/// ends, which is what lets a caller stream context onto it.
class Failure {
public:
  Failure(const char *file, int line, const char *what);
  ~Failure();

  template <typename T> Failure &operator<<(const T &value) {
    stream << value;
    return *this;
  }

private:
  const char *file;
  int line;
  const char *what;
  std::string context;
  llvm::raw_string_ostream stream{context};
};

/// Turns a streamed failure into a void expression, so `ASSERT` can
/// `return` it from a test body.
struct Voidify {
  void operator=(const Failure &) const {}
};

void registerCase(const char *suite, const char *name, void (*body)());

struct Registrar {
  Registrar(const char *suite, const char *name, void (*body)()) {
    registerCase(suite, name, body);
  }
};

/// Runs every registered case; returns the process exit status.
int runAll();

} // namespace zkctest

#define ZKC_TEST_CHECK(condition, what, onFailure)                             \
  switch (0)                                                                   \
  case 0:                                                                      \
  default:                                                                     \
    if (condition)                                                             \
      ;                                                                        \
    else                                                                       \
      onFailure ::zkctest::Voidify() =                                         \
          ::zkctest::Failure(__FILE__, __LINE__, what)

#define TEST(suite, name)                                                      \
  static void zkcTest_##suite##_##name();                                      \
  static ::zkctest::Registrar zkcRegistrar_##suite##_##name(                   \
      #suite, #name, zkcTest_##suite##_##name);                                \
  static void zkcTest_##suite##_##name()

#define EXPECT_TRUE(c) ZKC_TEST_CHECK((c), "expected true: " #c, )
#define EXPECT_FALSE(c) ZKC_TEST_CHECK(!(c), "expected false: " #c, )
#define EXPECT_EQ(a, b) ZKC_TEST_CHECK((a) == (b), "expected " #a " == " #b, )
#define EXPECT_NE(a, b) ZKC_TEST_CHECK((a) != (b), "expected " #a " != " #b, )
#define EXPECT_LT(a, b) ZKC_TEST_CHECK((a) < (b), "expected " #a " < " #b, )
#define EXPECT_LE(a, b) ZKC_TEST_CHECK((a) <= (b), "expected " #a " <= " #b, )
#define EXPECT_GT(a, b) ZKC_TEST_CHECK((a) > (b), "expected " #a " > " #b, )
#define EXPECT_GE(a, b) ZKC_TEST_CHECK((a) >= (b), "expected " #a " >= " #b, )
#define ADD_FAILURE() ZKC_TEST_CHECK(false, "failure", )

#define ASSERT_TRUE(c) ZKC_TEST_CHECK((c), "required true: " #c, return)
#define ASSERT_FALSE(c) ZKC_TEST_CHECK(!(c), "required false: " #c, return)
#define ASSERT_EQ(a, b)                                                        \
  ZKC_TEST_CHECK((a) == (b), "required " #a " == " #b, return)

#endif // ZKC_UNITTESTS_ZKCTEST_H
