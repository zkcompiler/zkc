// Client names exported APIs, never their private storage types.
module {
  dependency views = library(namespace="zkc.examples", name="views", version="1", resolution="source-v1");
  use views::{Zero, One, Many, EmptyViews, StoredViews, TerminalViews};
  link EmptyZero = Zero<EmptyViews>;
  protocol EmptyZeroProtocol {
    roles (P); inputs (P ready: bool, P ok: bool); outputs (P bool);
    local [walk] P: let answer = EmptyZero(ready, ok);
    return answer;
  }
  instance EmptyZeroRun: EmptyZeroProtocol { roles (P = P); }
  entry emptyzero = EmptyZeroRun;
  link EmptyOne = One<EmptyViews>;
  protocol EmptyOneProtocol {
    roles (P); inputs (P ready: bool, P ok: bool); outputs (P bool);
    local [walk] P: let answer = EmptyOne(ready, ok);
    return answer;
  }
  instance EmptyOneRun: EmptyOneProtocol { roles (P = P); }
  entry emptyone = EmptyOneRun;
  link EmptyMany = Many<EmptyViews>;
  protocol EmptyManyProtocol {
    roles (P); inputs (P ready: bool, P ok: bool); outputs (P bool);
    local [walk] P: let answer = EmptyMany(ready, ok);
    return answer;
  }
  instance EmptyManyRun: EmptyManyProtocol { roles (P = P); }
  entry emptymany = EmptyManyRun;
  link StoredZero = Zero<StoredViews>;
  protocol StoredZeroProtocol {
    roles (P); inputs (P ready: bool, P ok: bool); outputs (P bool);
    local [walk] P: let answer = StoredZero(ready, ok);
    return answer;
  }
  instance StoredZeroRun: StoredZeroProtocol { roles (P = P); }
  entry storedzero = StoredZeroRun;
  link StoredOne = One<StoredViews>;
  protocol StoredOneProtocol {
    roles (P); inputs (P ready: bool, P ok: bool); outputs (P bool);
    local [walk] P: let answer = StoredOne(ready, ok);
    return answer;
  }
  instance StoredOneRun: StoredOneProtocol { roles (P = P); }
  entry storedone = StoredOneRun;
  link StoredMany = Many<StoredViews>;
  protocol StoredManyProtocol {
    roles (P); inputs (P ready: bool, P ok: bool); outputs (P bool);
    local [walk] P: let answer = StoredMany(ready, ok);
    return answer;
  }
  instance StoredManyRun: StoredManyProtocol { roles (P = P); }
  entry storedmany = StoredManyRun;
  link TerminalZero = Zero<TerminalViews>;
  protocol TerminalZeroProtocol {
    roles (P); inputs (P ready: bool, P ok: bool); outputs (P bool);
    local [walk] P: let answer = TerminalZero(ready, ok);
    return answer;
  }
  instance TerminalZeroRun: TerminalZeroProtocol { roles (P = P); }
  entry terminalzero = TerminalZeroRun;
  link TerminalOne = One<TerminalViews>;
  protocol TerminalOneProtocol {
    roles (P); inputs (P ready: bool, P ok: bool); outputs (P bool);
    local [walk] P: let answer = TerminalOne(ready, ok);
    return answer;
  }
  instance TerminalOneRun: TerminalOneProtocol { roles (P = P); }
  entry terminalone = TerminalOneRun;
  link TerminalMany = Many<TerminalViews>;
  protocol TerminalManyProtocol {
    roles (P); inputs (P ready: bool, P ok: bool); outputs (P bool);
    local [walk] P: let answer = TerminalMany(ready, ok);
    return answer;
  }
  instance TerminalManyRun: TerminalManyProtocol { roles (P = P); }
  entry terminalmany = TerminalManyRun;
}
