#ifndef ZKC_TRANSFORMS_ORACLEPUBLICATION_H
#define ZKC_TRANSFORMS_ORACLEPUBLICATION_H

#include "OracleAccounting.h"
#include "OracleCommonRealization.h"
#include "OracleNativeCommon.h"
#include "zkc/Support/BoundedStream.h"
#include "zkc/Support/Json.h"
#include "zkc/Support/MLIRInput.h"
#include "llvm/Support/JSON.h"

namespace zkc::protocol {
using OraclePublicationField = llvm::json::Object::value_type;
// Reserve policy copying, validation, sorting, JSON construction and the
// selection codec's own size printer. String/path comparison widths include
// the ordered inventory's logarithmic comparisons before any copy is made.
inline bool reserveOraclePolicy(const OracleRealizationPolicy &policy,
                                OracleNativeWork &work) {
  if (!work.charge(256))
    return false;
  if (auto *uniform = std::get_if<OracleTableRealization>(&policy.roots))
    return work.chargeProduct(16, 1 + uniform->scheme.size());
  const auto &roots = std::get<std::vector<OracleRootSelection>>(policy.roots);
  unsigned comparisons = 1;
  for (size_t size = roots.size(); size > 1; size >>= 1)
    ++comparisons;
  for (const auto &root : roots)
    if (!work.chargeProduct(16 + 4 * comparisons,
                            1 + root.entry.size() + root.path.size() +
                                root.realization.scheme.size()))
      return false;
  return true;
}
// Reserve this inspection and string escaping. The
// output stream separately debits actual emitted bytes before copying them. The
// returned conservative byte bound is used only for the small canonical
// selection printer; records measure exact bytes.
inline llvm::Expected<uint64_t>
reserveOraclePublication(const llvm::json::Value &value, OracleNativeWork &work,
                         unsigned depth = 0) {
  if (!work.charge(4))
    return error("oracle-common-limit");
  if (depth >= 64 && (value.getAsArray() || value.getAsObject()))
    return error("oracle-realization-record-limit");
  uint64_t bytes = 24;
  if (auto text = value.getAsString()) {
    if (!work.charge(text->size()))
      return error("oracle-common-limit");
    return 2 + 6 * uint64_t(text->size());
  }
  auto child = [&](const llvm::json::Value &item) -> llvm::Error {
    auto size = reserveOraclePublication(item, work, depth + 1);
    if (!size)
      return size.takeError();
    bytes += 1 + *size;
    return llvm::Error::success();
  };
  if (auto *array = value.getAsArray()) {
    bytes = 2;
    for (const auto &item : *array)
      if (auto e = child(item))
        return std::move(e);
  } else if (auto *object = value.getAsObject()) {
    bytes = 2;
    for (const auto &field : *object) {
      llvm::StringRef key = field.first;
      if (!work.charge(3) || !work.charge(key.size()))
        return error("oracle-common-limit");
      bytes += 3 + 6 * uint64_t(key.size());
      if (auto e = child(field.second))
        return std::move(e);
    }
  }
  return bytes;
}

inline llvm::Expected<std::string>
serializeOraclePublication(const llvm::json::Value &value,
                           OracleNativeWork &work) {
  return oracleExpectedWithWork(work, [&]() -> llvm::Expected<std::string> {
    constexpr uint64_t limit = 32 * 1024 * 1024;
    std::string bytes;
    bool depthExceeded = false;
    // One recursive visit checks each subtree immediately before formatting
    // it. No completed plan, global object map or second tree walk is built.
    // A failed nested sort is caught locally before opening that object, so
    // LLVM's streaming callbacks can close their already-open containers.
    class Output final : public llvm::raw_ostream {
      std::string &bytes;
      OracleNativeWork &work;
      uint64_t limit;
      bool &depthExceeded;
      bool exceeded = false;
      void write_impl(const char *data, size_t size) override {
        if (exceeded || work.exhausted || depthExceeded)
          return;
        if (size > limit - bytes.size()) {
          exceeded = true;
          return;
        }
        // LLVM JSON's streaming destructor requires balanced containers.
        // Drain already reserved formatting after refusal, without copying
        // any further output; never throw across that streaming destructor.
        if (!work.charge(size))
          return;
        bytes.append(data, size);
      }
      uint64_t current_pos() const override { return bytes.size(); }

    public:
      Output(std::string &bytes, OracleNativeWork &work, uint64_t limit,
             bool &depthExceeded)
          : bytes(bytes), work(work), limit(limit),
            depthExceeded(depthExceeded) {
        SetUnbuffered();
      }
      bool overflow() const { return exceeded; }
    } out(bytes, work, limit, depthExceeded);
    llvm::json::OStream json(out);
    std::function<void(const llvm::json::Value &, unsigned)> emit =
        [&](const auto &node, unsigned depth) {
          if (depthExceeded || out.overflow() || !work.charge()) {
            // Complete the streaming grammar while the cancelled output
            // discards bytes, including a refusal before the root is opened.
            json.value(nullptr);
            return;
          }
          using Value = llvm::json::Value;
          switch (node.kind()) {
          case Value::Object: {
            if (depth >= 64) {
              depthExceeded = true;
              json.value(nullptr);
              return;
            }
            llvm::SmallVector<const OraclePublicationField *> fields;
            for (const auto &field : *node.getAsObject()) {
              // The local ordered-field slot and key formatting/escape pass.
              if (!work.charge(4 + llvm::StringRef(field.first).size())) {
                json.value(nullptr);
                return;
              }
              fields.push_back(&field);
            }
            auto less = [&](const OraclePublicationField *left,
                            const OraclePublicationField *right) {
              auto a = llvm::StringRef(left->first),
                   b = llvm::StringRef(right->first);
              if (!work.charge(1 + std::min(a.size(), b.size())))
                throw OracleAccountingLimit{};
              return a < b;
            };
            try {
              if (fields.size() == 2) {
                if (less(fields[1], fields[0]))
                  std::swap(fields[0], fields[1]);
              } else
                llvm::sort(fields, less);
            } catch (const OracleAccountingLimit &) {
              json.value(nullptr);
              return;
            }
            json.object([&] {
              for (auto *field : fields) {
                json.attributeBegin(field->first);
                emit(field->second, depth + 1);
                json.attributeEnd();
                if (work.exhausted || depthExceeded || out.overflow())
                  break;
              }
            });
            return;
          }
          case Value::Array:
            if (depth >= 64) {
              depthExceeded = true;
              json.value(nullptr);
              return;
            }
            json.array([&] {
              for (const auto &item : *node.getAsArray()) {
                emit(item, depth + 1);
                if (work.exhausted || depthExceeded || out.overflow())
                  break;
              }
            });
            return;
          case Value::String:
            if (!work.charge(node.getAsString()->size())) {
              json.value(nullptr);
              return;
            }
            break;
          default:
            break;
          }
          json.value(node);
        };
    emit(value, 0);
    if (depthExceeded)
      return error("oracle-realization-record-limit");
    if (work.exhausted)
      return error("oracle-common-limit");
    if (out.overflow())
      return error("oracle-realization-record-limit");
    return std::move(bytes);
  });
}
// Detach arbitrary borrowed JSON before publishing it. The record encoder has
// its own construction invariant and does not call this generic copy path.
inline llvm::Error reserveOracleJsonOwnership(const llvm::json::Value &value,
                                              OracleNativeWork &work,
                                              unsigned depth = 0) {
  if (!work.charge())
    return error("oracle-common-limit");
  if (depth >= 64 && (value.getAsArray() || value.getAsObject()))
    return error("oracle-realization-record-limit");
  if (auto text = value.getAsString()) {
    if (!work.chargeProduct(2, text->size()))
      return error("oracle-common-limit");
  } else if (auto *array = value.getAsArray()) {
    for (const auto &item : *array)
      if (auto e = reserveOracleJsonOwnership(item, work, depth + 1))
        return e;
  } else if (auto *object = value.getAsObject()) {
    for (const auto &field : *object) {
      if (!work.charge(1 + 2 * llvm::StringRef(field.first).size()))
        return error("oracle-common-limit");
      if (auto e = reserveOracleJsonOwnership(field.second, work, depth + 1))
        return e;
    }
  }
  return llvm::Error::success();
}
inline llvm::Expected<OracleRealizationPublication>
finishOraclePublication(llvm::json::Value value, OracleNativeWork &work) {
  return oracleExpectedWithWork(
      work, [&]() -> llvm::Expected<OracleRealizationPublication> {
        if (auto e = reserveOracleJsonOwnership(value, work))
          return std::move(e);
        ownJsonStrings(value);
        auto bytes = serializeOraclePublication(value, work);
        if (!bytes)
          return bytes.takeError();
        return OracleRealizationPublication{std::move(value),
                                            std::move(*bytes)};
      });
}
} // namespace zkc::protocol
#endif
