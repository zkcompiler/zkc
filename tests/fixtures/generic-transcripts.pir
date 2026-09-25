module {
  fn Observe<T: domain Transcript, E: domain Codec>(state: Transcript<T>, value: bool) -> Transcript<T> requires (
    Transcript(T),
    Encodes.bool(E)
  ) {
    [observe] let next = transcript::observe::bool::<T, E>(state, value) attributes (
      Round,
      message,
      boolean,
      P,
      V
    );
    return next;
  }

  fn Challenge<T: domain Transcript>(
    state: Transcript<T>
  ) -> (T::ChallengeField::Element, Transcript<T>) requires (FieldTranscript(T)) {
    [draw] let (value, next) = transcript::challenge::<T>(state) attributes (
      Round,
      challenge,
      Challenge,
      draw,
      V
    );
    return (value, next);
  }

  fn Guard<>(allowed: bool) -> () {
    [guard] control::require(allowed);
    return;
  }

  configure ObserveBool = Observe(T = "merlin3.bls12-381.fr64be/1", E = "zkcv.bool/1");
  configure Draw = Challenge(T = "merlin3.bls12-381.fr64be/1");
  configure Require = Guard();
  protocol Round {
    roles (P);
    inputs (P state: Transcript<"merlin3.bls12-381.fr64be/1">, P value: bool, P allowed: bool);
    outputs (
      P "bls12-381.fr"::Element,
      P "bls12-381.fr"::Element,
      P Transcript<"merlin3.bls12-381.fr64be/1">
    );
    local [observe] P: let observed = ObserveBool(state, value);
    local [first] P: let (a, next) = Draw(observed);
    local [guard] P: Require(allowed);
    local [second] P: let (b, final) = Draw(next);
    return (a, b, final);
  }

  instance concrete: Round {
    roles (P = P);
  }

  entry main = concrete;
}
