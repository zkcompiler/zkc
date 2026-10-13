// Ordinary pinned Monero BP+ calls. See ../tests/reference/monero/README.md.
#include "easylogging++.h"
#include "ringct/bulletproofs_plus.h"
#include "ringct/rctOps.h"
#include "serialization/binary_archive.h"
#include "serialization/containers.h"
#include "serialization/serialization.h"
#include <chrono>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <rapidjson/document.h>
#include <rapidjson/stringbuffer.h>
#include <rapidjson/writer.h>
#include <set>
#include <sstream>
#include <stdexcept>
#include <time.h>

using Json = rapidjson::Value;
using Clock = std::chrono::steady_clock;
struct Rejection : std::runtime_error {
  using std::runtime_error::runtime_error;
};
static void failure(const char *status, const char *error) {
  rapidjson::StringBuffer buffer;
  rapidjson::Writer<rapidjson::StringBuffer> writer(buffer);
  writer.StartObject();
  writer.Key("format");
  writer.String("zkc.benchmark-worker/0");
  writer.Key("status");
  writer.String(status);
  writer.Key("error");
  writer.String(error);
  writer.EndObject();
  std::cout << buffer.GetString() << '\n';
}
static std::string read(const std::string &path) {
  std::ifstream in(path, std::ios::binary);
  if (!in)
    throw std::runtime_error("cannot read " + path);
  return {std::istreambuf_iterator<char>(in), {}};
}
static void write(const std::string &path, const std::string &value) {
  std::ofstream out(path, std::ios::binary);
  out.write(value.data(), value.size());
  if (!out)
    throw std::runtime_error("cannot write " + path);
}
static rapidjson::Document document(const std::string &path) {
  rapidjson::Document result;
  auto bytes = read(path);
  result.Parse(bytes.data(), bytes.size());
  if (result.HasParseError() || !result.IsObject())
    throw std::runtime_error("invalid JSON object");
  return result;
}
static const Json &member(const Json &object, const char *name) {
  if (!object.IsObject() || !object.HasMember(name))
    throw std::runtime_error(std::string("missing ") + name);
  return object[name];
}
static void fields(const Json &object, std::set<std::string> allowed) {
  if (!object.IsObject())
    throw std::runtime_error("expected object");
  for (auto it = object.MemberBegin(); it != object.MemberEnd(); ++it)
    if (!allowed.erase(it->name.GetString()))
      throw std::runtime_error("unknown or duplicate field");
}
static std::string text(const Json &object, const char *name) {
  const auto &v = member(object, name);
  if (!v.IsString())
    throw std::runtime_error("expected string");
  return {v.GetString(), v.GetStringLength()};
}
static uint64_t number(const Json &object, const char *name) {
  const auto &v = member(object, name);
  if (!v.IsUint64())
    throw std::runtime_error("expected unsigned number");
  return v.GetUint64();
}
static uint64_t decimal(const Json &v) {
  if (!v.IsString())
    throw std::runtime_error("expected decimal string");
  std::string s(v.GetString(), v.GetStringLength());
  if (s.empty() || s.find_first_not_of("0123456789") != std::string::npos)
    throw std::runtime_error("invalid decimal");
  return std::stoull(s);
}

static uint64_t cpuTime() {
  timespec time{};
  if (clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &time))
    throw std::runtime_error("CPU clock");
  return uint64_t(time.tv_sec) * 1000000000 + time.tv_nsec;
}
int main(int argc, char **argv) {
  try {
    if (argc != 2)
      throw std::runtime_error("usage: monero-benchmark REQUEST.json");
    auto request = document(argv[1]);
    fields(request, {"format", "backend", "operation", "plan", "proof"});
    if (text(request, "format") != "zkc.benchmark-job/0")
      throw std::runtime_error("unknown job format");
    const auto &backend = member(request, "backend");
    fields(backend, {"kind", "public", "witness"});
    if (text(backend, "kind") != "monero")
      throw std::runtime_error("wrong backend");
    const auto &plan = member(request, "plan");
    fields(plan, {"warmups", "samples", "iterations"});
    auto warmups = number(plan, "warmups"), samples = number(plan, "samples"),
         iterations = number(plan, "iterations");
    if (!samples || !iterations || warmups > 1000000 || samples > 1000000 ||
        iterations > 1000000 || (warmups + samples) * iterations > 1000000)
      throw std::runtime_error("invalid sample plan");
    auto operation = text(request, "operation");
    bool prove = operation == "prove";
    if (!prove && operation != "verify")
      throw std::runtime_error("unknown operation");
    auto publicInput = document(text(backend, "public"));
    fields(publicInput, {"commitments", "rounds"});
    const auto &raw = member(publicInput, "commitments");
    if (!raw.IsArray() || raw.Empty() || raw.Size() % 32 || raw.Size() > 512)
      throw std::runtime_error("commitment count");
    rct::keyV commitments(raw.Size() / 32);
    for (unsigned i = 0; i < raw.Size(); ++i) {
      if (!raw[i].IsUint() || raw[i].GetUint() > 255)
        throw std::runtime_error("commitment byte");
      commitments[i / 32].bytes[i % 32] = raw[i].GetUint();
    }
    unsigned rounds = 6, padded = 1;
    while (padded < commitments.size()) {
      padded *= 2;
      ++rounds;
    }
    if (decimal(member(publicInput, "rounds")) != rounds)
      throw std::runtime_error("round count");
    std::vector<uint64_t> amounts;
    rct::keyV masks;
    if (prove) {
      auto witness = document(text(backend, "witness"));
      fields(witness, {"values", "masks"});
      const auto &values = member(witness, "values"),
                 &blindings = member(witness, "masks");
      if (!values.IsArray() || !blindings.IsArray() ||
          values.Size() != commitments.size() ||
          blindings.Size() != values.Size())
        throw std::runtime_error("witness shape");
      for (unsigned i = 0; i < values.Size(); ++i) {
        amounts.push_back(decimal(values[i]));
        masks.push_back(rct::d2h(decimal(blindings[i])));
      }
    }
    auto path = text(request, "proof");
    auto input = prove ? std::string() : read(path);
    auto verify = [&](const std::string &bytes) {
      rct::BulletproofPlus proof;
      binary_archive<false> ar(epee::span<const std::uint8_t>(
          reinterpret_cast<const uint8_t *>(bytes.data()), bytes.size()));
      if (!::serialization::serialize(ar, proof) || !ar.eof())
        return false;
      proof.V = commitments;
      return rct::n_bulletproof_plus_amounts(proof) > 0 &&
             rct::bulletproof_plus_VERIFY(proof);
    };
    auto produce = [&]() {
      auto proof = rct::bulletproof_plus_PROVE(amounts, masks);
      if (proof.V != commitments)
        throw std::runtime_error("witness mismatch");
      std::stringstream stream;
      binary_archive<true> ar(stream);
      if (!::serialization::serialize(ar, proof))
        throw std::runtime_error("serialization");
      return stream.str();
    };
    rapidjson::Document report(rapidjson::kObjectType);
    auto &allocator = report.GetAllocator();
    Json timings(rapidjson::kArrayType), proofs(rapidjson::kArrayType);
    std::string last;
    for (uint64_t i = 0; i < warmups + samples; ++i) {
      uint64_t elapsed = 0, cpuElapsed = 0, firstCall = 0;
      for (uint64_t j = 0; j < iterations; ++j) {
        auto cpu = cpuTime();
        auto start = Clock::now();
        auto produced = prove ? produce() : std::string();
        if (!prove && !verify(input))
          throw Rejection("proof rejected");
        auto duration = std::chrono::duration_cast<std::chrono::nanoseconds>(
                            Clock::now() - start)
                            .count();
        cpuElapsed += cpuTime() - cpu;
        elapsed += duration;
        if (j == 0)
          firstCall = duration;
        if (prove) {
          last = std::move(produced);
          auto name = path.substr(0, path.find_last_of('.')) + "." +
                      std::to_string(proofs.Size()) + ".proof";
          write(name, last);
          Json record(rapidjson::kObjectType);
          record.AddMember("path", Json(name.c_str(), allocator), allocator);
          record.AddMember("bytes", static_cast<uint64_t>(last.size()),
                           allocator);
          proofs.PushBack(record, allocator);
        }
      }
      Json sample(rapidjson::kObjectType);
      sample.AddMember("phase",
                       Json(i < warmups ? "warmup" : "sample", allocator),
                       allocator);
      sample.AddMember("index", i, allocator);
      sample.AddMember("iterations", iterations, allocator);
      sample.AddMember("cpu_ns", cpuElapsed, allocator);
      sample.AddMember("first_call_ns", firstCall, allocator);
      sample.AddMember("elapsed_ns", elapsed, allocator);
      timings.PushBack(sample, allocator);
    }
    if (prove)
      write(path, last);
    report.AddMember("format", "zkc.benchmark-worker/0", allocator);
    report.AddMember("status", "passed", allocator);
    report.AddMember("boundary", "reference_proof_call", allocator);
    report.AddMember("admission_ns", Json(), allocator);
    report.AddMember("samples", timings, allocator);
    report.AddMember("proofs", proofs, allocator);
    report.AddMember("proof_bytes",
                     static_cast<uint64_t>(prove ? last.size() : input.size()),
                     allocator);
    report.AddMember("diagnostics", Json(), allocator);
    Json build(rapidjson::kObjectType);
    build.AddMember("compiler", __VERSION__, allocator);
#ifdef __OPTIMIZE__
    build.AddMember("optimized", true, allocator);
#else
    build.AddMember("optimized", false, allocator);
#endif
#ifdef NDEBUG
    build.AddMember("debug_assertions", false, allocator);
#else
    build.AddMember("debug_assertions", true, allocator);
#endif
    report.AddMember("build", build, allocator);
    Json process(rapidjson::kObjectType);
    const char *threads = std::getenv("RAYON_NUM_THREADS");
    process.AddMember("rayon_num_threads",
                      threads ? Json(threads, allocator) : Json(), allocator);
    std::istringstream status(read("/proc/self/status"));
    std::string line;
    while (std::getline(status, line)) {
      if (line.rfind("VmHWM:", 0) == 0)
        report.AddMember("process_peak_rss_bytes",
                         static_cast<uint64_t>(std::stoull(line.substr(6))) *
                             1024,
                         allocator);
      if (line.rfind("Threads:", 0) == 0)
        process.AddMember("threads_at_exit",
                          Json(line.substr(8).c_str(), allocator), allocator);
      if (line.rfind("Cpus_allowed_list:", 0) == 0)
        process.AddMember("affinity", Json(line.substr(18).c_str(), allocator),
                          allocator);
    }
    report.AddMember("process", process, allocator);
    uint64_t floor = UINT64_MAX;
    for (unsigned i = 0; i < 1000; ++i) {
      auto start = Clock::now();
      auto end = Clock::now();
      floor = std::min(
          floor,
          static_cast<uint64_t>(
              std::chrono::duration_cast<std::chrono::nanoseconds>(end - start)
                  .count()));
    }
    report.AddMember("timer_floor_ns", floor, allocator);
    rapidjson::StringBuffer buffer;
    rapidjson::Writer<rapidjson::StringBuffer> writer(buffer);
    report.Accept(writer);
    std::cout << buffer.GetString() << '\n';
    return 0;
  } catch (const Rejection &error) {
    failure("rejected", error.what());
    return 1;
  } catch (const std::exception &error) {
    failure("failed", error.what());
    return 1;
  }
}
