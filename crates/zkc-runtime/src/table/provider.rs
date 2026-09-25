use crate::{Error, Outcome, Stop};
/// A provider owns its persistent state; the dispatcher never reconstructs it.
pub trait ChallengeProvider {
    fn draw(&mut self) -> Result<Outcome<u8>, Error>;
    fn remaining(&self) -> &[u8];
}
#[derive(Debug)]
pub struct TapeProvider {
    tape: Vec<u8>,
    position: usize,
}
impl TapeProvider {
    pub fn new(tape: Vec<u8>) -> Result<Self, Error> {
        if tape.iter().any(|x| *x >= 7) {
            return Err(Error("noncanonical-scalar"));
        }
        Ok(Self { tape, position: 0 })
    }
}
impl ChallengeProvider for TapeProvider {
    fn draw(&mut self) -> Result<Outcome<u8>, Error> {
        match self.tape.get(self.position).copied() {
            None => Ok(Outcome::Stopped(Stop::Exhausted)),
            Some(value) => {
                self.position += 1;
                Ok(Outcome::Returned(value))
            }
        }
    }
    fn remaining(&self) -> &[u8] {
        &self.tape[self.position..]
    }
}
