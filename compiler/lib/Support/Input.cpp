#include "Input.h"
#include "zkc/Support/Json.h"
#include <algorithm>
#include <array>
#include <fstream>
#include <iostream>
using namespace llvm;
namespace zkc {
Expected<std::string> readInput(StringRef path, size_t byteLimit) {
  std::ifstream file;
  if (path != "-") {
    file.open(path.str(), std::ios::binary);
    if (!file)
      return error("io-error");
  }
  std::istream &input = path == "-" ? std::cin : file;
  std::string text;
  std::array<char, 16384> buffer;
  while (input) {
    input.read(buffer.data(),
               std::min(buffer.size(), byteLimit - text.size() + 1));
    text.append(buffer.data(), input.gcount());
    if (input.bad() || (input.fail() && !input.eof()))
      return error("io-error");
    if (text.size() > byteLimit)
      return error("byte-limit");
  }
  return text;
}
} // namespace zkc
