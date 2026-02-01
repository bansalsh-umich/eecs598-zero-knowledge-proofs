use anyhow::{Context, Result, anyhow};
use std::{
    any::TypeId,
    fmt::{self, Debug, Display},
    time::Duration,
};
use tokio::sync::{
    mpsc::{UnboundedReceiver, UnboundedSender, unbounded_channel},
    oneshot,
};

pub mod transcript;
pub use transcript::show_transcript;

#[derive(Debug, Clone, PartialEq, Eq, Hash, Copy)]
pub enum Party {
    Prover,
    Verifier,
}

impl Party {
    const fn as_str(self) -> &'static str {
        match self {
            Party::Prover => "prover",
            Party::Verifier => "verifier",
        }
    }
}

impl Display for Party {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

struct SubprotocolRequest {
    key: String,
    type_ids: (TypeId, TypeId),
    comms: Box<dyn std::any::Any + Send + Sync>,
    response: oneshot::Sender<()>,
}

pub struct Comms<S, R> {
    sender: UnboundedSender<S>,
    receiver: UnboundedReceiver<R>,
    span: tracing::Span,
    timeout: Duration,
    id: Party,
    subprotocol_tx: UnboundedSender<SubprotocolRequest>,
    subprotocol_rx: UnboundedReceiver<SubprotocolRequest>,
}

impl<S, R> Debug for Comms<S, R> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Comms")
            .field("id", &self.id)
            .field("timeout", &self.timeout)
            .finish_non_exhaustive()
    }
}

fn minmax<T: Ord>(v1: T, v2: T) -> (T, T) {
    if v2 < v1 { (v2, v1) } else { (v1, v2) }
}

impl<S, R> Comms<S, R>
where
    S: Debug + Send + 'static,
    R: Debug + Send + 'static,
{
    const DEFAULT_TIMEOUT: Duration = Duration::from_secs(10);

    pub fn pair(key: impl Into<String>) -> (Self, Comms<R, S>) {
        let key = key.into();

        let (s1, r1) = unbounded_channel();
        let (s2, r2) = unbounded_channel();
        let (sub_tx1, sub_rx1) = unbounded_channel();
        let (sub_tx2, sub_rx2) = unbounded_channel();

        let span_p = tracing::info_span!("transcript", protocol = %key, party = "prover");
        let span_v = tracing::info_span!("transcript", protocol = %key, party = "verifier");

        let prover = Comms {
            sender: s1,
            receiver: r2,
            span: span_p,
            timeout: Self::DEFAULT_TIMEOUT,
            id: Party::Prover,
            subprotocol_tx: sub_tx1,
            subprotocol_rx: sub_rx2,
        };

        let verifier = Comms {
            sender: s2,
            receiver: r1,
            span: span_v,
            timeout: Self::DEFAULT_TIMEOUT,
            id: Party::Verifier,
            subprotocol_tx: sub_tx2,
            subprotocol_rx: sub_rx1,
        };

        (prover, verifier)
    }

    #[tracing::instrument(skip(self), parent = &self.span, err)]
    pub async fn recv(&mut self) -> Result<R> {
        let msg = tokio::time::timeout(self.timeout, self.receiver.recv())
            .await
            .context("recv timeout")?
            .context("recv channel closed")?;
        tracing::info!(msg = ?msg);
        Ok(msg)
    }

    #[tracing::instrument(skip(self, msg), parent = &self.span)]
    pub fn send(&self, msg: S) -> Result<()> {
        tracing::info!(msg = ?msg);
        self.sender
            .send(msg)
            .map_err(|_| anyhow!("send channel closed"))
    }

    pub fn set_timeout(&mut self, new_timeout: Duration) {
        self.timeout = new_timeout;
    }

    #[tracing::instrument(parent = &self.span, skip(self, key), err)]
    pub async fn establish_subprotocol<S2, R2>(
        &mut self,
        key: impl Into<String>,
    ) -> Result<Comms<S2, R2>>
    where
        S2: Send + 'static,
        R2: Send + 'static,
    {
        let key = key.into();
        let span = tracing::info_span!(parent: &self.span, "", protocol = %key);
        let type_ids = minmax(TypeId::of::<S2>(), TypeId::of::<R2>());

        match self.id {
            Party::Prover => {
                let (s1, r1) = unbounded_channel::<S2>();
                let (s2, r2) = unbounded_channel::<R2>();
                let (sub_tx1, sub_rx1) = unbounded_channel();
                let (sub_tx2, sub_rx2) = unbounded_channel();
                let (resp_tx, resp_rx) = oneshot::channel();

                self.subprotocol_tx
                    .send(SubprotocolRequest {
                        key,
                        type_ids,
                        comms: Box::new((s2, r1, sub_tx1, sub_rx2)),
                        response: resp_tx,
                    })
                    .map_err(|_| anyhow!("subprotocol channel closed"))?;

                tokio::time::timeout(self.timeout, resp_rx)
                    .await
                    .context("subprotocol handshake timeout")?
                    .context("subprotocol handshake failed")?;

                Ok(Comms {
                    sender: s1,
                    receiver: r2,
                    span,
                    timeout: self.timeout,
                    id: self.id,
                    subprotocol_tx: sub_tx2,
                    subprotocol_rx: sub_rx1,
                })
            }
            Party::Verifier => {
                let req = tokio::time::timeout(self.timeout, self.subprotocol_rx.recv())
                    .await
                    .context("subprotocol request timeout")?
                    .context("subprotocol channel closed")?;

                if req.key != key {
                    anyhow::bail!(
                        "subprotocol key mismatch: expected {:?}, got {:?}",
                        key,
                        req.key
                    );
                }

                if req.type_ids != type_ids {
                    anyhow::bail!(
                        "subprotocol type mismatch: expected {:?}, got {:?}",
                        type_ids,
                        req.type_ids
                    );
                }

                let (sender, receiver, sub_tx, sub_rx): (
                    UnboundedSender<S2>,
                    UnboundedReceiver<R2>,
                    UnboundedSender<SubprotocolRequest>,
                    UnboundedReceiver<SubprotocolRequest>,
                ) = *req.comms.downcast().expect("type mismatch in downcast");

                req.response.send(()).ok();

                Ok(Comms {
                    sender,
                    receiver,
                    span,
                    timeout: self.timeout,
                    id: self.id,
                    subprotocol_tx: sub_tx,
                    subprotocol_rx: sub_rx,
                })
            }
        }
    }
}
