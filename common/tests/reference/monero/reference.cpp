// Optional independent control: compile the unmodified pinned Monero sources.
// Only the prover's skGen symbol is wrapped to replay nonzero test coins.
#include "easylogging++.h"
#include "ringct/bulletproofs_plus.h"
#include "ringct/rctOps.h"
#include "serialization/binary_archive.h"
#include "serialization/containers.h"
#include "serialization/serialization.h"
#include <fstream>
#include <iostream>
#include <limits>
#include <random>
#include <sstream>
extern "C" rct::key real_skgen() asm("__real__ZN3rct5skGenEv");
static bool replay = false;
static unsigned cursor = 0;
extern "C" rct::key wrap_skgen() asm("__wrap__ZN3rct5skGenEv");
rct::key wrap_skgen() {
  if (!replay)
    return real_skgen();
  return rct::d2h(++cursor);
}
static std::string read(const char *path) {
  std::ifstream in(path, std::ios::binary);
  return {std::istreambuf_iterator<char>(in), {}};
}
static void write(const std::string &path, const std::string &data) {
  std::ofstream out(path, std::ios::binary);
  out.write(data.data(), data.size());
}
int main(int argc, char **argv) {
  try {
    if (argc == 2 && std::string(argv[1]) == "map") {
      std::string line;
      while (std::cin >> line) {
        if (line.size() != 64)
          return 2;
        unsigned char input[32], output[32];
        for (unsigned i = 0; i < 32; i++)
          input[i] = std::stoul(line.substr(2 * i, 2), nullptr, 16);
        ge_p2 p;
        ge_p1p1 q;
        ge_p3 r;
        ge_fromfe_frombytes_vartime(&p, input);
        ge_mul8(&q, &p);
        ge_p1p1_to_p3(&r, &q);
        ge_p3_tobytes(output, &r);
        static constexpr char hex[] = "0123456789abcdef";
        for (unsigned char b : output)
          std::cout << hex[b >> 4] << hex[b & 15];
        std::cout << "\n";
      }
      return 0;
    }
    if ((argc == 4 || argc == 5) && std::string(argv[1]) == "prove") {
      unsigned count = std::stoul(argv[2]);
      if (count < 1 || count > 16)
        return 2;
      std::vector<uint64_t> values(count);
      rct::keyV masks(count);
      std::string pattern = argc == 5 ? argv[4] : "sequence";
      if (pattern != "zero" && pattern != "max" && pattern != "mixed" &&
          pattern != "random" && pattern != "sequence")
        return 2;
      std::mt19937_64 random(12345 + count);
      for (unsigned i = 0; i < count; i++) {
        values[i] = pattern == "zero"  ? 0
                    : pattern == "max" ? UINT64_MAX
                    : pattern == "mixed"
                        ? std::vector<uint64_t>{0, 1, UINT64_C(1) << 63,
                                                UINT64_MAX}[i % 4]
                    : pattern == "random" ? random()
                                          : i;
        masks[i] = rct::d2h(i + 17);
      }
      replay = true;
      auto proof = rct::bulletproof_plus_PROVE(values, masks);
      replay = false;
      std::stringstream stream;
      binary_archive<true> ar(stream);
      if (!::serialization::serialize(ar, proof))
        return 3;
      std::string prefix = argv[3];
      write(prefix + ".proof", stream.str());
      std::string recorded;
      for (auto v : values)
        recorded += std::to_string(v) + "\n";
      write(prefix + ".values", recorded);
      write(prefix + ".commitments",
            std::string(reinterpret_cast<const char *>(proof.V.data()),
                        proof.V.size() * 32));
      std::cout << "{\"accepted\":"
                << (rct::bulletproof_plus_VERIFY(proof) ? "true" : "false")
                << ",\"coins\":" << cursor << "}\n";
      return 0;
    }
    if (argc == 4 && std::string(argv[1]) == "verify") {
      auto raw = read(argv[2]);
      auto commitments = read(argv[3]);
      if (commitments.empty() || commitments.size() % 32 ||
          commitments.size() > 512) {
        std::cout << "false\n";
        return 0;
      }
      rct::BulletproofPlus proof;
      binary_archive<false> ar(epee::span<const std::uint8_t>(
          reinterpret_cast<const std::uint8_t *>(raw.data()), raw.size()));
      if (!::serialization::serialize(ar, proof) || !ar.eof()) {
        std::cout << "false\n";
        return 0;
      }
      proof.V.resize(commitments.size() / 32);
      memcpy(proof.V.data(), commitments.data(), commitments.size());
      std::cout << ((rct::n_bulletproof_plus_amounts(proof) > 0 &&
                     rct::bulletproof_plus_VERIFY(proof))
                        ? "true\n"
                        : "false\n");
      return 0;
    }
  } catch (const std::exception &e) {
    std::cerr << e.what() << "\n";
    std::cout << "false\n";
    return 0;
  }
  return 2;
}
