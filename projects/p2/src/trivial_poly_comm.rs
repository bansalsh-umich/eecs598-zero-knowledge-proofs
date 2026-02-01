//! This module implements the 'trivial' polynomial commitment (where a commitment to a polynomial
//! is just the polynomial itself).
//!
//! You are not required to modify anything in this file. This file just serves as an example of
//! what an implementation of the InteractiveProof trait looks like. If you wish to write delphian
//! before quokka, you may use this as a stand-in for it, but your final submission should use quokka.
use std::{fmt::Debug, marker::PhantomData};

use crate::ip::{self, Comms, InteractiveProof};

use anyhow::bail;
use comms::show_transcript;
use p1::{Field, One, Zero, poly::Multilinear};

#[derive(Debug, Clone)]
pub struct Statement<F> {
    pub comm: Commitment<F>,
    pub point: Vec<F>,
    pub value: F,
}

pub type Commitment<F> = Multilinear<F>;
pub type Opening<F> = F;
// The polynomial being checked.
pub type Witness<F> = Multilinear<F>;

/// In the trivial PC, the verifier sends nothing
pub type VerifierMessage = ();
// The prover is not really required to send anything either, because the verifier already has the
// polynomial itself
// However, we will show sending an empty message to demonstrate using 'comms' struct.
pub type ProverMessage = ();

pub struct OpenProtocol<F>(PhantomData<F>);
pub fn commit<F: Field>(poly: &Multilinear<F>) -> (Commitment<F>, Opening<F>) {
    (poly.clone(), F::zero())
}

impl<F: Field> InteractiveProof for OpenProtocol<F> {
    type Statement = Statement<F>;
    type Witness = Witness<F>;
    type ProverMessage = ProverMessage;
    type VerifierMessage = VerifierMessage;
    type ProverOutput = ();
    type VerifierOutput = ();

    async fn prover(
        _stmt: Statement<F>,
        _wit: Witness<F>,
        comms: Comms<ProverMessage, VerifierMessage>,
    ) -> ip::Result<()> {
        comms.send(())?;
        Ok(())
    }

    #[allow(clippy::let_unit_value)]
    async fn verifier<R: rand::Rng>(
        stmt: Statement<F>,
        mut comms: Comms<VerifierMessage, ProverMessage>,
        _rng: &mut R,
    ) -> ip::Result<()> {
        let _msg = comms.recv().await?;
        if stmt.comm.evaluate(&stmt.point) != stmt.value {
            bail!("Poly does not evaluate to the correct value");
        }
        Ok(())
    }
}

type F = p1::zq::Zq<p1::moduli::Thirteen>;
#[tokio::test]
async fn my_test() {
    let _guard = show_transcript();
    let wit = Multilinear::new(1, vec![F::zero(), F::one()]);
    let stmt = Statement {
        comm: Multilinear::new(1, vec![F::zero(), F::one()]),
        point: vec![F::zero()],
        value: F::zero(),
    };
    let (p, v) = ip::execute::<OpenProtocol<F>>("protocol_test", stmt, wit).await;
    println!("{p:?} {v:?}");
}
