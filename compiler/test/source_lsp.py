"""Exercise the optional source server through its actual framed subprocess."""

import json
import queue
import subprocess
import threading

from support.cases import case, counted
from support.tools import records, tool


class Client:
    def __init__(self):
        self.process = subprocess.Popen(
            [tool("source_lsp")], stdin=subprocess.PIPE,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE,
        )
        self.inbox = queue.Queue()
        self.pending = []
        self.notifications = []
        self.sequence = 0
        self.reader = threading.Thread(target=self.read, daemon=True)
        self.reader.start()

    def read(self):
        try:
            while True:
                headers = {}
                while True:
                    line = self.process.stdout.readline()
                    if not line:
                        raise EOFError("server output ended")
                    if line == b"\r\n":
                        break
                    key, value = line.decode().split(":", 1)
                    headers[key.lower()] = value.strip()
                size = int(headers["content-length"])
                self.inbox.put(json.loads(self.process.stdout.read(size)))
        except Exception as error:
            self.inbox.put(error)

    def send(self, method, params=None, request_id=None):
        message = {"jsonrpc": "2.0", "method": method, "params": params}
        if request_id is not None:
            message["id"] = request_id
        data = json.dumps(message, ensure_ascii=False).encode()
        self.process.stdin.write(f"Content-Length: {len(data)}\r\n\r\n".encode() + data)
        self.process.stdin.flush()

    def response(self, request_id):
        for i, message in enumerate(self.pending):
            if message.get("id") == request_id and type(message["id"]) is type(request_id):
                return self.pending.pop(i)
        while True:
            message = self.inbox.get(timeout=30)
            if isinstance(message, Exception):
                raise message
            if "id" not in message:
                self.notifications.append(message)
            elif message["id"] == request_id and type(message["id"]) is type(request_id):
                return message
            else:
                self.pending.append(message)

    def request(self, method, params=None):
        self.sequence += 1
        self.send(method, params, self.sequence)
        result = self.response(self.sequence)
        assert "error" not in result, result
        return result["result"]

    def initialize(self, modules=None, encodings=None):
        capabilities = {} if encodings is None else {"general": {"positionEncodings": encodings}}
        result = self.request("initialize", {
            "capabilities": capabilities,
            "initializationOptions": {"modules": modules or []},
        })
        self.send("initialized", {})
        return result

    def open(self, uri, text, version=1):
        self.send("textDocument/didOpen", {"textDocument": {
            "uri": uri, "languageId": "zkc", "version": version, "text": text,
        }})

    def change(self, uri, version, changes):
        self.send("textDocument/didChange", {
            "textDocument": {"uri": uri, "version": version}, "contentChanges": changes,
        })

    def stop(self):
        if self.process.poll() is None:
            self.request("shutdown")
            self.send("exit")
            assert self.process.wait(timeout=10) == 0, self.process.stderr.read().decode()

    def __enter__(self):
        return self

    def __exit__(self, kind, value, traceback):
        try:
            if kind is None:
                self.stop()
        finally:
            if self.process.poll() is None:
                self.process.kill()
            self.process.wait(timeout=10)
            for stream in (self.process.stdin, self.process.stdout, self.process.stderr):
                stream.close()
            self.reader.join(timeout=5)


def at(uri, line=0, character=0):
    return {"textDocument": {"uri": uri}, "position": {"line": line, "character": character}}


SOURCE = "pub protocol Demo roles(P)(value: bool @P) -> bool @P:\n    result = value\n    return result\n"
URI = "file:///tmp/source_lsp_fixture.zkc"

with case("initialization validates source options and ignores unrelated client IDs"), Client() as client:
    for options in [[], {"modules": "wrong"}, {"unknown": []},
                    {"modules": [{"module": "m", "uri": URI, "extra": True}]}]:
        client.send("initialize", {"initializationOptions": options}, "retry")
        assert client.response("retry")["error"]["code"] == -32602
    client.request("initialize", {"initializationOptions": None,
                                  "capabilities": {"experimental": {"id": 3.25}}})
    client.open(URI, SOURCE)
    assert client.request("zkc/status", at(URI))["native"] == "checked"

with case("lifecycle and native semantic editor requests"), Client() as client:
    client.send("textDocument/hover", at(URI), "early")
    assert client.response("early")["error"]["code"] == -32002
    assert client.initialize()["capabilities"]["positionEncoding"] == "utf-16"
    client.open(URI, SOURCE)
    assert client.request("zkc/status", at(URI))["native"] == "checked"
    hover = client.request("textDocument/hover", at(URI, 2, 12))
    assert "Available at: P" in hover["contents"]["value"], hover
    definition = client.request("textDocument/definition", at(URI, 2, 12))
    assert definition["range"]["start"] == {"line": 1, "character": 4}, definition
    symbols = client.request("textDocument/documentSymbol", at(URI))
    assert [symbol["name"] for symbol in symbols] == ["Demo"], symbols
    items = client.request("textDocument/completion", at(URI, 2, 4))["items"]
    assert "result" in [item["label"] for item in items]
    assert isinstance(client.request("textDocument/formatting", at(URI)), list)
    client.send("zkc/status", at(URI), "7")
    client.send("zkc/status", at(URI), 7)
    assert client.response("7")["id"] == "7"
    assert client.response(7)["id"] == 7

for encoding, start, end in [("utf-16", 3, 5), ("utf-8", 3, 7)]:
    with case(f"{encoding} non-BMP CRLF edits and atomic resynchronization"), Client() as client:
        client.initialize(encodings=[encoding])
        text = "// 😀\r\n" + SOURCE.replace("\n", "\r\n")
        client.open(URI, text)
        before = client.request("zkc/status", at(URI))
        client.change(URI, 2, [{"range": {
            "start": {"line": 0, "character": start},
            "end": {"line": 0, "character": end}}, "text": "ok"}])
        after = client.request("zkc/status", at(URI))
        assert before["capture"] != after["capture"] and after["native"] == "checked"
        client.change(URI, 3, [
            {"range": {"start": {"line": 0, "character": 3}, "end": {"line": 0, "character": 5}}, "text": "x"},
            {"range": {"start": {"line": 999, "character": 0}, "end": {"line": 999, "character": 0}}, "text": "x"},
        ])
        client.send("zkc/status", at(URI), "invalid")
        assert client.response("invalid")["error"]["code"] == -32801
        client.change(URI, 4, [{"text": SOURCE}])
        restored = client.request("zkc/status", at(URI))
        assert restored["native"] == "checked"
        client.change(URI, 3, [{"text": "invalid stale text"}])
        assert client.request("zkc/status", at(URI))["capture"] == restored["capture"]
        client.change(URI, 5, [{"text": text}])
        client.change(URI, 6, [{"range": {
            "start": {"line": 0, "character": 4},
            "end": {"line": 0, "character": end}}, "text": "split"}])
        client.send("zkc/status", at(URI), "split")
        assert client.response("split")["error"]["code"] == -32801
        client.change(URI, 7, [{"text": SOURCE}])
        assert client.request("zkc/status", at(URI))["native"] == "checked"

with case("invalid body keeps recoverable symbols without guessed semantics"), Client() as client:
    client.initialize()
    client.open(URI, SOURCE.replace("result = value", "result = missing"))
    assert client.request("zkc/status", at(URI))["native"] == "invalid"
    assert client.request("textDocument/documentSymbol", at(URI))[0]["name"] == "Demo"
    client.send("textDocument/formatting", at(URI), "format")
    assert client.response("format")["error"]["code"] == -32803
    assert any(item["method"] == "textDocument/publishDiagnostics" and
               item["params"]["diagnostics"][0]["code"] == "source.name"
               for item in client.notifications if item.get("params", {}).get("diagnostics"))

with case("whole project invalidation matches fresh checks after dependency edits"):
    root = records("dependencies")
    provider = root / "ops.zkc"
    consumer = root / "m.zkc"
    provider_text = "def hidden(a: bool) -> bool:\n    a\npub def first(a: bool, b: bool) -> bool:\n    hidden(a)\npub operator infixl(60) ⊕ = first\n"
    consumer_text = "use ops::{operator ⊕}\n" + SOURCE.replace("result = value", "result = value ⊕ false ⊕ true")
    provider.write_text(provider_text)
    consumer.write_text(consumer_text)
    modules = [{"module": "ops", "uri": provider.as_uri()}, {"module": "m", "uri": consumer.as_uri()}]
    with Client() as client:
        client.initialize(modules)
        client.open(consumer.as_uri(), consumer_text)
        initial = client.request("zkc/status", at(consumer.as_uri()))
        for updated in [provider_text.replace("infixl(60)", "infixr(70)"),
                        provider_text.replace("    a\n", "    false\n")]:
            provider.write_text(updated)
            assert client.request("zkc/status", at(consumer.as_uri()))["capture"] == initial["capture"], "query read a file implicitly"
            client.send("workspace/didChangeWatchedFiles", {"changes": [{"uri": provider.as_uri(), "type": 2}]})
            changed = client.request("zkc/status", at(consumer.as_uri()))
            assert changed["capture"] != initial["capture"]
            assert changed["native"] == "checked"
            with Client() as fresh:
                fresh.initialize(modules)
                recomputed = fresh.request("zkc/status", at(consumer.as_uri()))
                assert {k: v for k, v in changed.items() if k != "generation"} == {k: v for k, v in recomputed.items() if k != "generation"}
                assert client.request("textDocument/formatting", at(consumer.as_uri())) == fresh.request("textDocument/formatting", at(consumer.as_uri()))
            initial = changed
        client.change(consumer.as_uri(), 2, [{"text": consumer_text + "spec for Demo:\n    security: secure()\n"}])
        assert client.request("zkc/status", at(consumer.as_uri()))["assurance"] == "unavailable"
        client.change(consumer.as_uri(), 3, [{"text": consumer_text}])
        assert client.request("zkc/status", at(consumer.as_uri()))["assurance"] == "not-requested"

with case("configured file deletion and recreation invalidate and recover"):
    path = records("recreation") / "m.zkc"
    path.write_text(SOURCE)
    with Client() as client:
        client.initialize([{"module": "m", "uri": path.as_uri()}])
        assert client.request("zkc/status", at(path.as_uri()))["native"] == "checked"
        path.unlink()
        client.send("workspace/didChangeWatchedFiles", {"changes": [{"uri": path.as_uri(), "type": 3}]})
        client.send("zkc/status", at(path.as_uri()), "deleted")
        assert client.response("deleted")["error"]["code"] == -32801
        path.write_text(SOURCE)
        client.send("workspace/didChangeWatchedFiles", {"changes": [{"uri": path.as_uri(), "type": 1}]})
        assert client.request("zkc/status", at(path.as_uri()))["native"] == "checked"

with case("negative document versions and close clear open state"), Client() as client:
    client.initialize()
    client.open(URI, SOURCE, version=-2)
    initial = client.request("zkc/status", at(URI))
    client.change(URI, -1, [{"text": SOURCE + "\n"}])
    assert client.request("zkc/status", at(URI))["capture"] != initial["capture"]
    client.send("textDocument/didClose", {"textDocument": {"uri": URI}})
    client.send("zkc/status", at(URI), "closed")
    assert client.response("closed")["error"]["code"] == -32602

with case("standalone module identity follows full, incremental and reopen edits"), Client() as client:
    client.initialize()
    client.open(URI, "module before\n" + SOURCE)
    assert client.request("zkc/status", at(URI))["native"] == "checked"
    edits = [
        ([{"text": "module after\n" + SOURCE}], "module after\n" + SOURCE),
        ([{"range": {"start": {"line": 0, "character": 7},
                     "end": {"line": 0, "character": 12}}, "text": "next"}], "module next\n" + SOURCE),
        ([{"range": {"start": {"line": 0, "character": 0},
                     "end": {"line": 1, "character": 0}}, "text": ""}], SOURCE),
    ]
    for version, (changes, text) in enumerate(edits, 2):
        client.change(URI, version, changes)
        edited = client.request("zkc/status", at(URI))
        with Client() as fresh:
            fresh.initialize()
            fresh.open(URI, text)
            recomputed = fresh.request("zkc/status", at(URI))
        assert edited["native"] == "checked", edited
        assert {k: v for k, v in edited.items() if k != "generation"} == {k: v for k, v in recomputed.items() if k != "generation"}
    client.open(URI, "module reopened\n" + SOURCE, version=5)
    assert client.request("zkc/status", at(URI))["native"] == "checked"

with case("configured module identities remain authoritative across edits"):
    path = records("configured-identity") / "m.zkc"
    path.write_text("module m\n" + SOURCE)
    with Client() as client:
        client.initialize([{"module": "m", "uri": path.as_uri()}])
        client.open(path.as_uri(), "module m\n" + SOURCE)
        assert client.request("zkc/status", at(path.as_uri()))["native"] == "checked"
        client.change(path.as_uri(), 2, [{"text": "module renamed\n" + SOURCE}])
        assert client.request("zkc/status", at(path.as_uri()))["native"] == "invalid"
        client.open(path.as_uri(), "module reopened\n" + SOURCE, version=3)
        assert client.request("zkc/status", at(path.as_uri()))["native"] == "invalid"

with case("cancelled queued requests immediately release capacity"), Client() as client:
    client.initialize()
    large = "\n".join(f"def helper{i}(x: bool) -> bool:\n    x" for i in range(15000)) + "\n" + SOURCE
    client.open(URI, large)
    for index in range(32):
        client.send("zkc/status", at(URI), f"cancel-{index}")
    for index in range(32):
        client.send("$/cancelRequest", {"id": f"cancel-{index}"})
    for index in range(32):
        answer = client.response(f"cancel-{index}")
        assert "result" in answer or answer["error"]["code"] in (-32800, -32803), answer
    client.send("zkc/status", at(URI), "after-cancel")
    assert "result" in client.response("after-cancel")

with case("queued cancellation, reused IDs and stale publication"), Client() as client:
    client.initialize()
    large = "\n".join(f"def helper{i}(x: bool) -> bool:\n    x" for i in range(1500)) + "\n" + SOURCE
    client.open(URI, large)
    client.send("zkc/status", at(URI), "cancel")
    client.send("$/cancelRequest", {"id": "cancel"})
    assert client.response("cancel")["error"]["code"] == -32800
    client.change(URI, 2, [{"text": SOURCE}])
    client.send("zkc/status", at(URI), "cancel")
    assert client.response("cancel")["result"]["native"] == "checked"
    client.request("textDocument/hover", at(URI, 2, 12))
    versions = [item["params"]["version"] for item in client.notifications
                if item["method"] == "textDocument/publishDiagnostics"]
    assert versions and versions[-1] == 2 and versions == sorted(versions), versions

with case("duplicate outstanding IDs and bounded queue refuse independently"), Client() as client:
    client.initialize()
    large = "\n".join(f"def helper{i}(x: bool) -> bool:\n    x" for i in range(3000)) + "\n" + SOURCE
    client.open(URI, large)
    client.send("zkc/status", at(URI), "duplicate")
    client.send("zkc/status", at(URI), "duplicate")
    assert client.response("duplicate")["error"]["code"] == -32600
    for index in range(64):
        client.send("zkc/status", at(URI), f"queue-{index}")
    client.change(URI, 2, [{"text": SOURCE}])
    answers = [client.response(f"queue-{index}") for index in range(64)]
    assert any(item.get("error", {}).get("code") == -32803 for item in answers), answers
    assert "error" in client.response("duplicate")
    assert client.request("zkc/status", at(URI))["native"] == "checked"

for payload in [b"Content-Length: 9999999999\r\n\r\n",
                b"Content-Length: 2\r\nContent-Length: 2\r\n\r\n{}",
                b"Content-Length: 1\n\n{",
                b"Content-Length: 4\r\n\r\n[{}]",
                b"Content-Length: 10\r\n\r\n{}"]:
    with case(f"malformed framing refuses {payload[:40]!r}"):
        process = subprocess.run([tool("source_lsp")], input=payload, capture_output=True, timeout=10)
        assert process.returncode == 1, process.stdout

for body in [b'{"jsonrpc":"2.0","method":"initialize","id":1.0}',
             b'{"jsonrpc":"2.0","method":"initialize","id":2147483648}',
             b'{"jsonrpc":"2.0","method":"initialize","id":1,"id":2}',
             b'{"jsonrpc":"2.0","method":"initialize","id":"\\ud800"}',
             b'{"jsonrpc":"2.0","method":"$/cancelRequest","params":{"id":1.0}}',
             b'{"jsonrpc":"2.0","method":"initialize","id":1,"params":' + b'[' * 65 + b']' * 65 + b'}']:
    with case(f"invalid JSON identity or resource envelope refuses {body[:80]!r}"):
        payload = f"Content-Length: {len(body)}\r\n\r\n".encode() + body
        process = subprocess.run([tool("source_lsp")], input=payload, capture_output=True, timeout=10)
        assert process.returncode == 1, process.stdout

print(f"{counted()} source server cases passed")
