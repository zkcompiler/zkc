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
//
// What the harness adds beyond gtest's surface is the two things these
// tests kept writing by hand: `FOR_EACH`, which labels the element a
// table-driven case failed on, and `EXPECT_REFUSED`/`EXPECT_ADMITTED`,
// which state what was expected of a fallible call and consume the
// `llvm::Error` either way. A test that has to remember to consume is
// a test that reports a harness abort instead of its own failure.
//===----------------------------------------------------------------------===//

#ifndef ZKC_UNITTESTS_ZKCTEST_H
#define ZKC_UNITTESTS_ZKCTEST_H

#include "llvm/ADT/StringRef.h"
#include "llvm/Support/Error.h"
#include "llvm/Support/raw_ostream.h"

#include <string>
#include <type_traits>
#include <utility>

namespace zkctest {

namespace detail {

/// Whether a value can be written to a stream. A comparison prints the
/// two sides it compared when it can, because "expected a == b" without
/// them sends the reader back to a debugger for what the failure
/// already knew.
template <typename T, typename = void> struct IsPrintable : std::false_type {};
template <typename T>
struct IsPrintable<T, std::void_t<decltype(std::declval<llvm::raw_ostream &>()
                                           << std::declval<const T &>())>>
    : std::true_type {};

template <typename T> void print(llvm::raw_ostream &os, const T &value) {
  if constexpr (IsPrintable<T>::value)
    os << value;
  else
    os << "<unprintable>";
}

template <typename T> std::string describe(const T &value) {
  std::string text;
  llvm::raw_string_ostream os(text);
  print(os, value);
  return text;
}

} // namespace detail

/// The two sides a failed comparison saw, for the failure to stream.
template <typename A, typename B>
std::string compared(const A &lhs, const B &rhs) {
  return "got " + detail::describe(lhs) + " and " + detail::describe(rhs);
}

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

void pushContext(std::string label);
void popContext();

/// A label every failure recorded inside the scope names. `FOR_EACH`
/// pushes the element, so a table-driven case says which row failed
/// without each assertion repeating the row.
class ScopedContext {
public:
  template <typename T> explicit ScopedContext(const T &value) {
    pushContext(detail::describe(value));
  }
  ~ScopedContext() { popContext(); }

  ScopedContext(const ScopedContext &) = delete;
  ScopedContext &operator=(const ScopedContext &) = delete;
};

/// What a fallible call did, with the error consumed and its message
/// kept. Consuming here is the point: `llvm::Error` aborts the process
/// when dropped, so a test that forgets reports a crash rather than the
/// failure it found.
struct Outcome {
  bool admitted;
  std::string message;
};

Outcome outcomeOf(llvm::Error error);

template <typename T> Outcome outcomeOf(llvm::Expected<T> &&value) {
  if (value)
    return {true, {}};
  return outcomeOf(value.takeError());
}
template <typename T> Outcome outcomeOf(llvm::Expected<T> &value) {
  return outcomeOf(std::move(value));
}

void registerCase(const char *suite, const char *name, void (*body)());

struct Registrar {
  Registrar(const char *suite, const char *name, void (*body)()) {
    registerCase(suite, name, body);
  }
};

/// Runs every registered case whose `suite.name` contains one of the
/// arguments — all of them when there are none — and returns the
/// process exit status.
int runAll(int argc = 0, char **argv = nullptr);

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

/// A comparison that keeps both sides so the failure can name them.
/// The `for` chain binds each side once — a test may compare the result
/// of a call, and evaluating it twice would compare two different runs.
#define ZKC_TEST_COMPARE(a, b, op, what, onFailure)                            \
  for (bool zkcDone = false; !zkcDone;)                                        \
    for (const auto &zkcLhs = (a); !zkcDone;)                                  \
      for (const auto &zkcRhs = (b); !zkcDone; zkcDone = true)                 \
        if (zkcLhs op zkcRhs)                                                  \
          ;                                                                    \
        else                                                                   \
          onFailure ::zkctest::Voidify() =                                     \
              ::zkctest::Failure(__FILE__, __LINE__, what)                     \
              << ::zkctest::compared(zkcLhs, zkcRhs)

#define TEST(suite, name)                                                      \
  static void zkcTest_##suite##_##name();                                      \
  static ::zkctest::Registrar zkcRegistrar_##suite##_##name(                   \
      #suite, #name, zkcTest_##suite##_##name);                                \
  static void zkcTest_##suite##_##name()

/// Iterate a container, naming the element on every failure inside.
#define FOR_EACH(declaration, container)                                       \
  for (const auto &declaration : (container))                                  \
    if (::zkctest::ScopedContext zkcElement{declaration}; false)               \
      ;                                                                        \
    else

#define EXPECT_TRUE(c) ZKC_TEST_CHECK((c), "expected true: " #c, )
#define EXPECT_FALSE(c) ZKC_TEST_CHECK(!(c), "expected false: " #c, )
#define EXPECT_EQ(a, b) ZKC_TEST_COMPARE(a, b, ==, "expected " #a " == " #b, )
#define EXPECT_NE(a, b) ZKC_TEST_COMPARE(a, b, !=, "expected " #a " != " #b, )
#define EXPECT_LT(a, b) ZKC_TEST_COMPARE(a, b, <, "expected " #a " < " #b, )
#define EXPECT_LE(a, b) ZKC_TEST_COMPARE(a, b, <=, "expected " #a " <= " #b, )
#define EXPECT_GT(a, b) ZKC_TEST_COMPARE(a, b, >, "expected " #a " > " #b, )
#define EXPECT_GE(a, b) ZKC_TEST_COMPARE(a, b, >=, "expected " #a " >= " #b, )
#define ADD_FAILURE() ZKC_TEST_CHECK(false, "failure", )

/// Substring containment, for a message or a rendering whose exact text
/// is not the claim.
#define EXPECT_CONTAINS(haystack, needle)                                      \
  for (bool zkcDone = false; !zkcDone;)                                        \
    for (llvm::StringRef zkcText = (haystack); !zkcDone; zkcDone = true)       \
      ZKC_TEST_CHECK(zkcText.contains(needle),                                 \
                     "expected " #haystack " to contain " #needle, )           \
          << "got \"" << zkcText << "\""

/// The two things a test says about a fallible call. Both consume.
#define EXPECT_REFUSED(expr)                                                   \
  ZKC_TEST_CHECK(!::zkctest::outcomeOf(expr).admitted,                         \
                 "expected a refusal: " #expr, )
#define EXPECT_ADMITTED(expr)                                                  \
  if (::zkctest::Outcome zkcOutcome = ::zkctest::outcomeOf(expr);              \
      zkcOutcome.admitted)                                                     \
    ;                                                                          \
  else                                                                         \
    ::zkctest::Voidify() =                                                     \
        ::zkctest::Failure(__FILE__, __LINE__, "expected admission: " #expr)   \
        << zkcOutcome.message

#define ASSERT_TRUE(c) ZKC_TEST_CHECK((c), "required true: " #c, return)
#define ASSERT_FALSE(c) ZKC_TEST_CHECK(!(c), "required false: " #c, return)
#define ASSERT_EQ(a, b)                                                        \
  ZKC_TEST_COMPARE(a, b, ==, "required " #a " == " #b, return)
#define ASSERT_NE(a, b)                                                        \
  ZKC_TEST_COMPARE(a, b, !=, "required " #a " != " #b, return)
#define ASSERT_LT(a, b)                                                        \
  ZKC_TEST_COMPARE(a, b, <, "required " #a " < " #b, return)
#define ASSERT_LE(a, b)                                                        \
  ZKC_TEST_COMPARE(a, b, <=, "required " #a " <= " #b, return)
#define ASSERT_GT(a, b)                                                        \
  ZKC_TEST_COMPARE(a, b, >, "required " #a " > " #b, return)
#define ASSERT_GE(a, b)                                                        \
  ZKC_TEST_COMPARE(a, b, >=, "required " #a " >= " #b, return)

#endif // ZKC_UNITTESTS_ZKCTEST_H
