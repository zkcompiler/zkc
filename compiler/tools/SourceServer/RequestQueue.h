#ifndef ZKC_SOURCE_REQUESTQUEUE_H
#define ZKC_SOURCE_REQUESTQUEUE_H
#include <algorithm>
#include <cassert>
#include <deque>
#include <map>
#include <memory>
#include <string>
#include <vector>
namespace zkc::editor {
/// Single-worker scheduling state. Every method runs under the server mutex;
/// computation happens outside it. The same transitions are directly testable
/// without a clock, a slow input, or a production-only test command.
template <class Task> class RequestQueue {
public:
  using Pointer = std::shared_ptr<Task>;
  enum class Admission { Accepted, Duplicate, Full };
  Admission admission(const std::string &key) const {
    if (active.count(key))
      return Admission::Duplicate;
    if (queued.size() >= capacity || active.size() >= capacity)
      return Admission::Full;
    return Admission::Accepted;
  }
  bool contains(const std::string &key) const { return active.count(key); }
  bool empty() const { return queued.empty(); }
  void push(Pointer task) {
    if (!task->key.empty()) {
      assert(admission(task->key) == Admission::Accepted);
      active.emplace(task->key, task);
    }
    queued.push_back(std::move(task));
  }
  Pointer take() {
    while (!queued.empty()) {
      auto task = queued.front();
      queued.pop_front();
      if (task->finished)
        continue;
      assert(!running);
      running = task;
      return task;
    }
    return {};
  }
  Pointer cancel(const std::string &key) {
    auto found = active.find(key);
    if (found == active.end())
      return {};
    auto task = found->second;
    task->cancellation.cancel();
    auto pending = std::find(queued.begin(), queued.end(), task);
    if (pending != queued.end())
      queued.erase(pending);
    return task;
  }
  bool complete(const Pointer &task) {
    if (task->finished)
      return false;
    task->finished = true;
    auto found = active.find(task->key);
    // A cancelled request ID may already have been reused. Completing the old
    // worker must not erase or complete the new request with that ID.
    if (found != active.end() && found->second == task)
      active.erase(found);
    return true;
  }
  std::vector<Pointer> invalidate() {
    if (running)
      running->cancellation.cancel();
    std::vector<Pointer> result;
    for (const auto &[_, task] : active) {
      task->cancellation.cancel();
      result.push_back(task);
    }
    queued.clear();
    return result;
  }
  void release([[maybe_unused]] const Pointer &task) {
    assert(running == task);
    running.reset();
  }
  template <class Snapshot>
  bool publishable(const Task &task,
                   const std::shared_ptr<Snapshot> &current) const {
    return task.snapshot == current && !task.finished &&
           !task.cancellation.cancelled();
  }

private:
  static constexpr unsigned capacity = 32;
  std::map<std::string, Pointer> active;
  std::deque<Pointer> queued;
  Pointer running;
};
} // namespace zkc::editor
#endif
