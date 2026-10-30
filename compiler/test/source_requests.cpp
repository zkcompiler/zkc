#include "../tools/SourceServer/RequestQueue.h"
#include "support/NativeCases.h"
#include "zkc/Source/Source.h"
using namespace zkc::test;
namespace {
struct Task {
  std::string key;
  std::shared_ptr<int> snapshot;
  zkc::source::Cancellation cancellation;
  bool finished = false;
};
using Queue = zkc::editor::RequestQueue<Task>;
auto task(std::string key, std::shared_ptr<int> snapshot = {}) {
  return std::make_shared<Task>(
      Task{std::move(key), std::move(snapshot), {}, false});
}
} // namespace
int main() {
  Cases cases;
  cases.run("queued cancellation releases capacity before worker advances", [] {
    Queue queue;
    auto running = task("running");
    queue.push(running);
    require(queue.take() == running, "wrong running task");
    for (unsigned i = 0; i < 31; ++i)
      queue.push(task(std::to_string(i)));
    require(queue.admission("new") == Queue::Admission::Full,
            "capacity not enforced");
    require(queue.admission("running") == Queue::Admission::Duplicate,
            "full queue hid duplicate identity");
    auto cancelled = queue.cancel("0");
    require(cancelled && cancelled->cancellation.cancelled(),
            "queued task not cancelled");
    require(queue.complete(cancelled), "cancelled task not completed");
    require(queue.admission("new") == Queue::Admission::Accepted,
            "cancelled queued task retained capacity");
    queue.push(task("new"));
    queue.complete(running);
    queue.release(running);
    require(queue.take()->key == "1", "cancelled task still occupied queue");
  });
  cases.run("late cancelled worker cannot erase reused request identity", [] {
    Queue queue;
    auto old = task("s:same");
    queue.push(old);
    queue.take();
    require(queue.cancel(old->key) == old && queue.complete(old),
            "old request not cancelled");
    auto fresh = task(old->key);
    queue.push(fresh);
    require(!queue.complete(old) && queue.contains(fresh->key),
            "late completion erased new request identity");
    queue.release(old);
    require(queue.take() == fresh && !fresh->finished &&
                !fresh->cancellation.cancelled(),
            "new request inherited old cancellation");
    require(queue.complete(fresh) && !queue.complete(fresh),
            "reply was not single-use");
    queue.release(fresh);
  });
  cases.run(
      "invalidated snapshots cannot publish after computation finishes", [] {
        Queue queue;
        auto oldSnapshot = std::make_shared<int>(1);
        auto newSnapshot = std::make_shared<int>(2);
        auto old = task("request", oldSnapshot);
        queue.push(old);
        queue.take();
        require(queue.publishable(*old, oldSnapshot),
                "current request was hidden");
        require(!queue.publishable(*old, newSnapshot),
                "old generation could publish");
        auto cancelled = queue.invalidate();
        require(cancelled.size() == 1 && !queue.publishable(*old, oldSnapshot),
                "invalidated request could still publish");
        for (const auto &pending : cancelled)
          queue.complete(pending);
        require(queue.empty() && !queue.contains("request"),
                "invalidation retained requests");
        queue.release(old);
        auto current = task("request", newSnapshot);
        queue.push(current);
        require(queue.publishable(*current, newSnapshot),
                "new generation was suppressed");
      });
  cases.run("diagnostic workers cancel without a client request identity", [] {
    Queue queue;
    auto snapshot = std::make_shared<int>(1);
    auto diagnostic = task("", snapshot);
    queue.push(diagnostic);
    queue.take();
    require(queue.invalidate().empty(),
            "diagnostic acquired a client request ID");
    require(!queue.publishable(*diagnostic, snapshot),
            "stale diagnostics can publish");
    queue.release(diagnostic);
  });
  cases.run("string and integer IDs have separate scheduler identity", [] {
    Queue queue;
    auto integer = task("i:1"), string = task("s:1");
    queue.push(integer);
    queue.push(string);
    require(queue.cancel(integer->key) == integer, "wrong typed ID cancelled");
    queue.complete(integer);
    require(queue.take() == string && !string->cancellation.cancelled(),
            "integer cancellation affected the string ID");
  });
  return cases.result();
}
