use crate::{Result, codec::*, ensure};
use merlin::Transcript;
use serde_json::{Value, json};
use sha2::{Digest, Sha256};
use zkc_arkworks::{Scalar, scalar_from_wide_be};
/// Same public frames; no hidden peer and no runtime/backend protocol execution.
pub struct Session<'a> {
    transcript: Transcript,
    candidate: Option<&'a [u8]>,
    pub proof: Vec<u8>,
    pub cursor: usize,
    pub messages: usize,
    pub draws: usize,
    pub actions: usize,
    pub events: Vec<Value>,
}
impl<'a> Session<'a> {
    pub fn new(root: &Value, candidate: Option<&'a [u8]>) -> Result<Self> {
        let root = logical(root)?;
        let digest = Sha256::digest(&root);
        let mut proof = b"ZKCPRF01".to_vec();
        proof.extend(digest);
        if let Some(b) = candidate {
            ensure(
                b.len() <= LIMIT && b.get(..40) == Some(proof.as_slice()),
                "proof-header-binding",
            )?;
        }
        let mut transcript = Transcript::new(b"zkc.artifact/1");
        transcript.append_message(b"binding", &root);
        Ok(Self {
            transcript,
            candidate,
            proof,
            cursor: 40,
            messages: 0,
            draws: 0,
            actions: 0,
            events: vec![],
        })
    }
    pub fn receive(&mut self) -> Result<Vec<u8>> {
        let b = self.candidate.ok_or("receive-in-producer")?;
        let end = self.cursor.checked_add(8).ok_or("proof-length")?;
        let len = u64::from_le_bytes(
            b.get(self.cursor..end)
                .ok_or("proof-truncated")?
                .try_into()?,
        );
        let len = usize::try_from(len)?;
        ensure(len <= LIMIT, "proof-message-limit")?;
        let next = end.checked_add(len).ok_or("proof-length")?;
        let value = b.get(end..next).ok_or("proof-truncated")?.to_vec();
        self.cursor = next;
        self.messages += 1;
        Ok(value)
    }
    pub fn send(&mut self, value: &[u8]) -> Result<()> {
        ensure(
            self.candidate.is_none() && self.proof.len() + 8 + value.len() <= LIMIT,
            "proof-size",
        )?;
        self.proof.extend((value.len() as u64).to_le_bytes());
        self.proof.extend(value);
        self.messages += 1;
        Ok(())
    }
    pub fn observe(&mut self, origin: Value, value: &[u8]) -> Result<()> {
        self.transcript
            .append_message(b"origin", &logical(&origin)?);
        self.transcript.append_message(b"value", value);
        self.actions += 1;
        self.events.push(json!(["observe", origin, hex(value)]));
        Ok(())
    }
    pub fn draw(&mut self, origin: Value) -> Result<Scalar> {
        self.transcript
            .append_message(b"origin", &logical(&origin)?);
        let mut bytes = [0; 64];
        self.transcript.challenge_bytes(b"challenge", &mut bytes);
        let c = scalar_from_wide_be(&bytes);
        self.draws += 1;
        self.actions += 1;
        self.events
            .push(json!(["challenge", origin, hex(&scalar(c)?)]));
        Ok(c)
    }
    pub fn guard(
        &mut self,
        instance: &str,
        path: &Value,
        location: [&str; 4],
        ok: bool,
    ) -> Result<()> {
        let [protocol, call, function, site] = location;
        self.events.push(json!([
            "guard", instance, path, protocol, call, function, site, "V", ok
        ]));
        ensure(ok, "source-control-require")
    }
    pub fn finish(&self) -> Result<()> {
        if let Some(b) = self.candidate {
            ensure(self.cursor == b.len(), "proof-trailing")?;
        }
        Ok(())
    }
    pub fn is_validator(&self) -> bool {
        self.candidate.is_some()
    }
}
pub fn origin(instance: &str, path: &Value, event: Value) -> Value {
    json!(["zkc.logical-origin/1", "main", instance, path, event])
}
pub fn message(
    instance: &str,
    path: &Value,
    protocol: &str,
    site: &str,
    schema: &str,
    sender: &str,
    receiver: &str,
) -> Value {
    origin(
        instance,
        path,
        json!(["message", protocol, site, schema, sender, receiver]),
    )
}
pub fn challenge(
    instance: &str,
    path: &Value,
    protocol: &str,
    call: &str,
    function: &str,
) -> Value {
    origin(
        instance,
        path,
        json!(["challenge", protocol, call, function, "draw", "V"]),
    )
}
